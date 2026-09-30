#!/usr/bin/env python3
"""
SharpPing - free "sharp signal" alerter.

What it does each run:
  1. Gate (costs nothing): respects min poll interval, daily call cap, credit floor,
     and only spends API credits if a game starts inside WINDOW_HOURS.
  2. Pulls odds from The Odds API (sharp book + soft books).
  3. Removes the vig from the sharp book (Pinnacle) -> "fair" probability.
  4. Flags soft-book prices that beat fair by MIN_EDGE, then scores them (0-100):
       edge 40 + steam 25 + sharp/consensus agreement 20 + stale line 15
  5. Sends alerts >= ALERT_SCORE to Telegram / Discord / ntfy.
  6. Logs every signal and tracks closing-line value (CLV) on later runs.

Usage:
  python sharpping.py --demo      # no API key needed, shows a sample signal
  python sharpping.py --dry       # real data, prints signals, sends/writes nothing
  python sharpping.py             # real run
  python sharpping.py --report    # CLV summary of logged signals

Only the Python standard library is used (Python 3.9+).
"""
import argparse
import json
import os
import sys
import urllib.error
import urllib.parse
import urllib.request
from datetime import datetime, timedelta, timezone
from pathlib import Path
from statistics import median

try:
    from zoneinfo import ZoneInfo
except ImportError:  # pragma: no cover
    ZoneInfo = None


def _env(name, default, cast=str):
    v = os.getenv(name)
    if v is None or v.strip() == "":
        return default
    try:
        return cast(v.strip())
    except ValueError:
        return default


# ----------------------------- CONFIG (all env-overridable) -----------------------------
API_BASE = "https://api.the-odds-api.com/v4"
API_KEY = _env("ODDS_API_KEY", "")
SPORT = _env("SPORT", "americanfootball_nfl")  # e.g. basketball_nba, baseball_mlb, icehockey_nhl
MARKETS = _env("MARKETS", "h2h")  # each extra market multiplies credit cost (h2h,spreads,totals)
SHARP = [b for b in _env("SHARP_BOOKS", "pinnacle").split(",") if b]
SOFT = [b for b in _env(
    "SOFT_BOOKS",
    "draftkings,fanduel,betmgm,williamhill_us,betrivers,fanatics,hardrockbet,betonlineag,bovada",
).split(",") if b]
# The Odds API bills per group of 10 bookmakers per market, so keep the list at 10 or fewer.
BOOKMAKERS = list(dict.fromkeys(SHARP + SOFT))[:10]
SOFT = [b for b in SOFT if b in BOOKMAKERS]

MIN_EDGE = _env("MIN_EDGE", 0.03, float)          # 3% EV vs fair price
EDGE_FULL = _env("EDGE_FULL", 0.05, float)        # edge at which edge score maxes out
MIN_BOOKS = _env("MIN_BOOKS", 5, int)             # books quoting the market (liquidity filter)
ALERT_SCORE = _env("ALERT_SCORE", 70, int)
STEAM_MOVE = _env("STEAM_MOVE", 0.005, float)     # 0.5% fair-prob move counts as "moved"
STEAM_BOOKS = _env("STEAM_BOOKS", 3, int)         # books moving the same way = steam
STALE_MOVE = _env("STALE_MOVE", 0.015, float)     # sharp moved 1.5%+ while soft book didn't
NEWS_JUMP = _env("NEWS_JUMP", 0.06, float)        # 6%+ single-snapshot jump = likely news
MAX_ALERTS_PER_RUN = _env("MAX_ALERTS_PER_RUN", 5, int)
COOLDOWN_HOURS = _env("COOLDOWN_HOURS", 6, float)

BANKROLL = _env("BANKROLL", 1000.0, float)
KELLY_FRACTION = _env("KELLY_FRACTION", 0.25, float)
MAX_STAKE_PCT = _env("MAX_STAKE_PCT", 2.0, float)  # cap, percent of bankroll

# Credit budget (free tier ~500/month). 1 call = 1 credit per market with <=10 bookmakers.
WINDOW_HOURS = _env("WINDOW_HOURS", 24, float)    # only poll if a game starts within this
MIN_POLL_MINUTES = _env("MIN_POLL_MINUTES", 45, float)
DAILY_CALL_CAP = _env("DAILY_CALL_CAP", 14, int)
MIN_CREDITS_LEFT = _env("MIN_CREDITS_LEFT", 10, int)
MAX_SNAP_AGE_MIN = _env("MAX_SNAP_AGE_MIN", 180, float)

TELEGRAM_TOKEN = _env("TELEGRAM_BOT_TOKEN", "")
TELEGRAM_CHAT = _env("TELEGRAM_CHAT_ID", "")
DISCORD_WEBHOOK = _env("DISCORD_WEBHOOK_URL", "")
NTFY_TOPIC = _env("NTFY_TOPIC", "")
TIMEZONE = _env("TIMEZONE", "America/Chicago")

DATA_DIR = Path(_env("DATA_DIR", "data"))
STATE_FILE = DATA_DIR / "state.json"
SIGNALS_FILE = DATA_DIR / "signals.json"


# ----------------------------- small helpers -----------------------------
def log(msg):
    print(f"[sharpping] {msg}", flush=True)


def parse_ts(s):
    return datetime.fromisoformat(s.replace("Z", "+00:00"))


def iso(dt):
    return dt.strftime("%Y-%m-%dT%H:%M:%SZ")


def load_json(path, default):
    try:
        return json.loads(Path(path).read_text())
    except (FileNotFoundError, json.JSONDecodeError):
        return default


def save_json(path, obj):
    Path(path).parent.mkdir(parents=True, exist_ok=True)
    Path(path).write_text(json.dumps(obj, indent=1))


def american(dec):
    if dec >= 2:
        return f"+{round((dec - 1) * 100)}"
    return f"{round(-100 / (dec - 1))}"


def http_get(url, params):
    full = f"{url}?{urllib.parse.urlencode(params)}"
    req = urllib.request.Request(full, headers={"User-Agent": "sharpping/1.0"})
    with urllib.request.urlopen(req, timeout=30) as r:
        return json.loads(r.read().decode()), r.headers


def http_post(url, body, headers):
    req = urllib.request.Request(url, data=body, headers=headers, method="POST")
    with urllib.request.urlopen(req, timeout=20) as r:
        return r.status


# ----------------------------- odds math -----------------------------
def no_vig(prices):
    """Proportional vig removal. prices: {outcome: decimal odds} -> {outcome: fair prob}."""
    if len(prices) < 2 or any((not v) or v <= 1 for v in prices.values()):
        return None
    inv = {k: 1.0 / v for k, v in prices.items()}
    s = sum(inv.values())
    return {k: v / s for k, v in inv.items()}


def parse_event(ev):
    """-> {book: {group: {outcome: decimal_price}}}. Group = market (+ absolute line)."""
    books = {}
    for bm in ev.get("bookmakers", []):
        for mk in bm.get("markets", []):
            groups = {}
            for o in mk.get("outcomes", []):
                pt = o.get("point")
                g = mk["key"] if pt is None else f'{mk["key"]}@{abs(pt):g}'
                k = o["name"] if pt is None else f'{o["name"]} {pt:+g}'
                groups.setdefault(g, {})[k] = float(o["price"])
            for g, outs in groups.items():
                if len(outs) >= 2:
                    books.setdefault(bm["key"], {})[g] = outs
    return books


def sharp_fair(books, g):
    for b in SHARP:
        if b in books and g in books[b]:
            fair = no_vig(books[b][g])
            if fair:
                return b, fair
    return None


def kelly_stake(fair_p, price):
    b = price - 1
    full = (fair_p * price - 1) / b if b > 0 else 0
    pct = max(0.0, min(KELLY_FRACTION * full * 100, MAX_STAKE_PCT))
    return pct, BANKROLL * pct / 100


# ----------------------------- signal detection -----------------------------
def analyze(ev, books, prev_books, commence):
    sigs = []
    prev_books = prev_books or {}
    for g in {g for b in books.values() for g in b}:
        ref = sharp_fair(books, g)
        if not ref:
            continue
        ref_book, fair = ref
        outs = set(fair)

        comp = {}  # book -> no-vig probs, same outcome set only
        for bk, bg in books.items():
            if g in bg and set(bg[g]) == outs:
                nv = no_vig(bg[g])
                if nv:
                    comp[bk] = nv
        if len(comp) < MIN_BOOKS:  # liquidity / thin market filter
            continue

        prev_comp = {}
        for bk, bg in prev_books.items():
            if g in bg and set(bg[g]) == outs:
                nv = no_vig(bg[g])
                if nv:
                    prev_comp[bk] = nv

        for out in outs:
            sharp_move = None
            if ref_book in prev_comp:
                sharp_move = fair[out] - prev_comp[ref_book][out]
            if sharp_move is not None and sharp_move <= -STEAM_MOVE:
                continue  # sharp money is moving AWAY from this side

            steam_n = sum(
                1 for bk, nv in comp.items()
                if bk in prev_comp and nv[out] - prev_comp[bk][out] >= STEAM_MOVE
            )
            steam_ok = (sharp_move is not None and sharp_move >= STEAM_MOVE
                        and steam_n >= STEAM_BOOKS)
            news = sharp_move is not None and abs(sharp_move) >= NEWS_JUMP

            for bk in SOFT:
                if bk not in comp or bk in SHARP:
                    continue
                price = books[bk][g][out]
                edge = fair[out] * price - 1
                if edge < MIN_EDGE:
                    continue

                prev_price = prev_books.get(bk, {}).get(g, {}).get(out)
                stale = (prev_price is not None and abs(prev_price - price) < 1e-9
                         and sharp_move is not None and sharp_move >= STALE_MOVE)

                others = [nv[out] for b, nv in comp.items() if b not in SHARP and b != bk]
                cons = median(others) if others else None
                if cons is None:
                    agree_pts, diff = 0.0, None
                else:
                    diff = abs(cons - fair[out])
                    agree_pts = 20 * (1 - min(max((diff - 0.01) / 0.03, 0), 1))

                edge_pts = 40 * min(edge / EDGE_FULL, 1)
                if steam_ok:
                    steam_pts = 25
                elif sharp_move is not None and sharp_move >= STEAM_MOVE:
                    steam_pts = 10
                else:
                    steam_pts = 0
                stale_pts = 15 if stale else 0
                score = edge_pts + steam_pts + agree_pts + stale_pts - (25 if news else 0)
                score = int(max(0, min(100, round(score))))

                reasons = [f"edge +{edge * 100:.1f}% vs {ref_book} no-vig"]
                if steam_ok:
                    reasons.append(f"steam: {steam_n} books moved this way (sharp {sharp_move * 100:+.1f}%)")
                elif steam_pts:
                    reasons.append(f"sharp book moved {sharp_move * 100:+.1f}% toward this side")
                if stale:
                    reasons.append(f"{bk} hasn't moved while sharp did")
                if diff is not None:
                    reasons.append(f"other books within {diff * 100:.1f}% of sharp")

                pct, usd = kelly_stake(fair[out], price)
                sigs.append({
                    "id": f'{ev["id"]}|{g}|{out}|{bk}',
                    "ts": iso(datetime.now(timezone.utc)),
                    "event_id": ev["id"], "sport": ev.get("sport_title", SPORT),
                    "home": ev.get("home_team", ""), "away": ev.get("away_team", ""),
                    "commence": iso(commence), "group": g, "market": g,
                    "outcome": out, "book": bk, "price": price,
                    "fair": round(fair[out], 4), "edge": round(edge, 4),
                    "score": score, "stake_pct": round(pct, 2), "stake_usd": round(usd, 2),
                    "reasons": reasons, "news": news, "ref_book": ref_book,
                    "close_fair": None, "clv": None, "frozen": False,
                })
    return sigs


def update_clv(sig_log, cur_books, now):
    """Refresh closing fair prob for logged signals until the game starts."""
    for s in sig_log:
        if s.get("frozen"):
            continue
        if parse_ts(s["commence"]) <= now:
            s["frozen"] = True
            continue
        books = cur_books.get(s["event_id"])
        if not books:
            continue
        r = sharp_fair(books, s["group"])
        if r and s["outcome"] in r[1]:
            cf = r[1][s["outcome"]]
            s["close_fair"] = round(cf, 4)
            s["clv"] = round(cf * s["price"] - 1, 4)


# ----------------------------- notifications -----------------------------
def fmt_msg(s):
    try:
        tz = ZoneInfo(TIMEZONE) if ZoneInfo else timezone.utc
    except Exception:
        tz = timezone.utc
    when = parse_ts(s["commence"]).astimezone(tz).strftime("%a %b %d %I:%M %p")
    lines = [
        f"SHARP SIGNAL  {s['score']}/100",
        f"{s['sport']}: {s['away']} @ {s['home']} ({when})",
        f"BET: {s['outcome']} [{s['market']}] @ {s['book']} {american(s['price'])}",
        f"Fair: {american(1 / s['fair'])} ({s['fair'] * 100:.1f}%)   Edge: +{s['edge'] * 100:.1f}%",
        f"Stake ({KELLY_FRACTION:g} Kelly, cap {MAX_STAKE_PCT:g}%): "
        f"{s['stake_pct']:.2f}% = about ${s['stake_usd']:.0f}",
        "Why: " + "; ".join(s["reasons"]),
    ]
    if s["news"]:
        lines.append("WARNING: very large sudden move. Check injury/lineup news first.")
    lines.append("Confirm the price is still live before betting.")
    return "\n".join(lines)


def notify(text, title="SharpPing"):
    sent = False
    if TELEGRAM_TOKEN and TELEGRAM_CHAT:
        try:
            body = json.dumps({"chat_id": TELEGRAM_CHAT, "text": text}).encode()
            http_post(f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/sendMessage",
                      body, {"Content-Type": "application/json"})
            sent = True
        except Exception as e:
            log(f"telegram failed: {e}")
    if DISCORD_WEBHOOK:
        try:
            body = json.dumps({"content": text[:1900]}).encode()
            http_post(DISCORD_WEBHOOK, body,
                      {"Content-Type": "application/json", "User-Agent": "sharpping/1.0"})
            sent = True
        except Exception as e:
            log(f"discord failed: {e}")
    if NTFY_TOPIC:
        try:
            http_post(f"https://ntfy.sh/{NTFY_TOPIC}", text.encode("utf-8"),
                      {"Title": title, "Priority": "high", "Tags": "dart"})
            sent = True
        except Exception as e:
            log(f"ntfy failed: {e}")
    if not sent:
        log("no notification channel configured (set Telegram/Discord/ntfy env vars)")


# ----------------------------- data fetching (credit-aware) -----------------------------
def gated_fetch(state, now):
    """Return odds events, or None if we should not spend credits this run."""
    last = state.get("last_poll")
    if last and (now - parse_ts(last)).total_seconds() < MIN_POLL_MINUTES * 60:
        log("min poll interval not reached; skipping")
        return None
    day = now.strftime("%Y-%m-%d")
    calls = state.setdefault("calls", {})
    for d in [d for d in calls if d < (now - timedelta(days=3)).strftime("%Y-%m-%d")]:
        calls.pop(d)
    if calls.get(day, 0) >= DAILY_CALL_CAP:
        log("daily call cap reached; skipping")
        return None
    rem = state.get("remaining")
    if rem is not None and rem < MIN_CREDITS_LEFT:
        log(f"only {rem} credits left; skipping to protect the quota")
        return None

    # The events list is documented as not consuming credits; use it to decide if a poll is worthwhile.
    evs, _ = http_get(f"{API_BASE}/sports/{SPORT}/events", {"apiKey": API_KEY})
    horizon = now + timedelta(hours=WINDOW_HOURS)
    if not any(now < parse_ts(e["commence_time"]) <= horizon for e in evs):
        log(f"no {SPORT} games start within {WINDOW_HOURS:g}h; no credits spent")
        return None

    data, headers = http_get(f"{API_BASE}/sports/{SPORT}/odds", {
        "apiKey": API_KEY, "bookmakers": ",".join(BOOKMAKERS), "markets": MARKETS,
        "oddsFormat": "decimal", "dateFormat": "iso", "commenceTimeTo": iso(horizon),
    })
    state["last_poll"] = iso(now)
    calls[day] = calls.get(day, 0) + 1
    r = headers.get("x-requests-remaining")
    if r is not None:
        try:
            state["remaining"] = int(float(r))
        except ValueError:
            pass
    log(f"fetched {len(data)} events; credits remaining: {state.get('remaining', '?')}")
    return data


def demo_data(now):
    commence = iso(now + timedelta(hours=3))

    def bm(key, buf, kc):
        return {"key": key, "markets": [{"key": "h2h", "outcomes": [
            {"name": "Buffalo Bills", "price": buf}, {"name": "Kansas City Chiefs", "price": kc}]}]}

    base = {"id": "demo1", "sport_title": "NFL (DEMO)", "home_team": "Buffalo Bills",
            "away_team": "Kansas City Chiefs", "commence_time": commence}
    cur = dict(base, bookmakers=[bm("pinnacle", 1.93, 1.97), bm("draftkings", 2.10, 1.76),
                                 bm("fanduel", 1.95, 1.87), bm("betmgm", 1.95, 1.87),
                                 bm("williamhill_us", 1.95, 1.87), bm("betrivers", 1.96, 1.86)])
    prev = dict(base, bookmakers=[bm("pinnacle", 2.05, 1.85), bm("draftkings", 2.10, 1.76),
                                  bm("fanduel", 2.05, 1.80), bm("betmgm", 2.05, 1.80),
                                  bm("williamhill_us", 2.05, 1.80), bm("betrivers", 2.05, 1.80)])
    return [cur], {"demo1": parse_event(prev)}


# ----------------------------- main flow -----------------------------
def run(demo, dry):
    now = datetime.now(timezone.utc)
    state = load_json(STATE_FILE, {})
    sig_log = load_json(SIGNALS_FILE, [])

    if demo:
        events, prev_snap = demo_data(now)
    else:
        if not API_KEY:
            sys.exit("Set ODDS_API_KEY (free key at https://the-odds-api.com). Try --demo first.")
        try:
            events = gated_fetch(state, now)
        except urllib.error.HTTPError as e:
            sys.exit(f"Odds API error {e.code}: {e.reason}")
        except urllib.error.URLError as e:
            sys.exit(f"Network error: {e.reason}")
        if events is None:
            if not dry:
                save_json(STATE_FILE, state)
            return
        prev_snap = {}
        if state.get("snap_ts") and (now - parse_ts(state["snap_ts"])).total_seconds() <= MAX_SNAP_AGE_MIN * 60:
            prev_snap = state.get("snap", {})
        else:
            log("no fresh previous snapshot: steam/stale checks start next run")

    cur_snap, candidates = {}, []
    for ev in events:
        commence = parse_ts(ev["commence_time"])
        if commence <= now + timedelta(minutes=5):
            continue
        books = parse_event(ev)
        cur_snap[ev["id"]] = books
        candidates += analyze(ev, books, prev_snap.get(ev["id"]), commence)

    # cooldown / dedupe
    alerted = state.setdefault("alerted", {})
    cutoff = now - timedelta(hours=COOLDOWN_HOURS * 4)
    for k in [k for k, v in alerted.items() if parse_ts(v["ts"]) < cutoff]:
        alerted.pop(k)
    fresh = []
    for s in sorted(candidates, key=lambda x: (-x["score"], -x["edge"])):
        if s["score"] < ALERT_SCORE:
            continue
        a = alerted.get(s["id"])
        if a and (now - parse_ts(a["ts"])).total_seconds() < COOLDOWN_HOURS * 3600 \
                and s["price"] < a["price"] * 1.03:
            continue
        fresh.append(s)
    fresh = fresh[:MAX_ALERTS_PER_RUN]

    log(f"{len(candidates)} candidate(s) >= {MIN_EDGE * 100:.0f}% edge, {len(fresh)} alert(s) >= score {ALERT_SCORE}")
    for s in fresh:
        print("\n" + fmt_msg(s) + "\n")

    if demo:
        return
    if dry:
        log("dry run: nothing sent or saved")
        return

    update_clv(sig_log, cur_snap, now)
    for s in fresh:
        notify(fmt_msg(s))
        alerted[s["id"]] = {"ts": iso(now), "price": s["price"]}
        sig_log.append(s)
    state["snap"], state["snap_ts"] = cur_snap, iso(now)
    save_json(STATE_FILE, state)
    save_json(SIGNALS_FILE, sig_log)


def report():
    sig_log = load_json(SIGNALS_FILE, [])
    done = [s for s in sig_log if s.get("clv") is not None]
    print(f"Signals logged: {len(sig_log)}   with CLV data: {len(done)}")
    if not done:
        return
    clvs = [s["clv"] for s in done]
    pos = sum(1 for c in clvs if c > 0)
    print(f"Average CLV (EV at last-seen sharp price): {sum(clvs) / len(clvs) * 100:+.2f}%")
    print(f"Beat the close: {pos}/{len(done)} ({pos / len(done) * 100:.0f}%)")
    if len(done) < 200:
        print("Fewer than 200 signals: treat this as noise, not proof.")


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description="SharpPing sharp-signal alerter")
    ap.add_argument("--demo", action="store_true", help="run on built-in sample data (no API key)")
    ap.add_argument("--dry", action="store_true", help="real data, but send and save nothing")
    ap.add_argument("--report", action="store_true", help="print CLV summary")
    a = ap.parse_args()
    if a.report:
        report()
    else:
        run(a.demo, a.dry)
