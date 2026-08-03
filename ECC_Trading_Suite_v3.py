#!/usr/bin/env python3
"""
ECC Trading Suite - Cloud Edition v3 (FULL BUILD)
==================================================
Personal-use paper trading + scanner + no-code strategy website.

WHAT THIS INCLUDES (all in one file):
 1. Bigger fonts, redesigned modern UI
 2. Candlestick / Line / Bar chart toggle (canvas-based, no external libs)
 3. Universal symbol search (any NSE stock, index, crypto, forex, US stock)
 4. F&O availability auto-check for searched symbol
 5. India mode / Global(Forex+Crypto+US) mode toggle
 6. No-code Strategy Builder - Plain English box AND Dropdown builder (both feed same engine)
 7. Live India VIX shown on dashboard + usable inside strategy rules
 8. Real-data backtest engine for ANY symbol (yfinance), simulated fallback if offline
 9. Manual order execution (market + limit + SL/TP) fully working
10. Chartink screener puller (best-effort; Chartink has no official API so this uses
    their public screener POST endpoint - may need occasional fixing if they change site)
11. Mobile notifications: service worker + Add-to-Home-Screen support so Android gets
    real push-style alerts; iPhone requires "Add to Home Screen" first (Apple restriction,
    cannot be bypassed by any website)
12. Sensibull note: Sensibull has NO developer/demo API, so true F&O premium paper trading
    is simulated here internally (Black-Scholes-lite) instead of connecting to Sensibull

Install:  pip install flask yfinance requests
Run:      python ecc_cloud_v3.py
Deploy:   Render.com free tier (same as before) - keep requirements.txt updated
"""
import csv, io, json, math, os, queue, random, re, threading, time
from datetime import datetime, timezone
from flask import Flask, Response, jsonify, request

try:
    import yfinance as yf
    HAS_YF = True
except ImportError:
    HAS_YF = False

try:
    import requests
    HAS_REQ = True
except ImportError:
    HAS_REQ = False

app = Flask(__name__)
PORT = int(os.environ.get("PORT", 5000))
INIT_CASH = 10000.0
AUTOFRAC = 0.20
MAXHIST = 500
MAXTRADES = 200
CHARTPTS = 120
MAXBT = 5000
SCANEVERY = 300

ASSETS = {
    "BTC-USD": {"name": "Bitcoin", "p0": 43500.0, "mu": 0.00020, "sigma": 0.025},
    "ETH-USD": {"name": "Ethereum", "p0": 2650.0, "mu": 0.00015, "sigma": 0.028},
    "AAPL": {"name": "Apple", "p0": 185.0, "mu": 0.00008, "sigma": 0.012},
    "TSLA": {"name": "Tesla", "p0": 235.0, "mu": 0.00010, "sigma": 0.032},
    "RELIANCE.NS": {"name": "Reliance", "p0": 2900.0, "mu": 0.00009, "sigma": 0.016},
    "NSEI": {"name": "Nifty 50", "p0": 24500.0, "mu": 0.00007, "sigma": 0.010},
}

NSE_FNO_SET = {
    "RELIANCE","TCS","INFY","HDFCBANK","ICICIBANK","SBIN","AXISBANK","KOTAKBANK",
    "LT","ITC","HINDUNILVR","BHARTIARTL","MARUTI","TATAMOTORS","TATASTEEL","M&M",
    "SUNPHARMA","BAJFINANCE","BAJAJFINSV","ADANIENT","ADANIPORTS","ULTRACEMCO",
    "TITAN","WIPRO","HCLTECH","ONGC","NTPC","POWERGRID","COALINDIA","JSWSTEEL",
    "GRASIM","DRREDDY","CIPLA","DIVISLAB","EICHERMOT","HEROMOTOCO","BAJAJ-AUTO",
    "INDUSINDBK","HDFCLIFE","SBILIFE","TECHM","ASIANPAINT","NESTLEIND","BRITANNIA",
    "UPL","GAIL","VEDL","HINDALCO","APOLLOHOSP","PIDILITIND","DLF","SHREECEM",
    "TATACONSUM","BPCL","IOC","ZOMATO","PAYTM","IRCTC","PNB","BANKBARODA",
}

def is_indian_symbol(sym): return sym.upper().endswith((".NS",".BO")) or sym.upper() in ("NSEI","BSESN","BANKNIFTY")
def has_fno(sym):
    base = sym.upper().replace(".NS","").replace(".BO","")
    if base in ("NIFTY","NSEI","^NSEI","BANKNIFTY","NSEBANK","^NSEBANK"): return True
    return base in NSE_FNO_SET

def gbm(price, mu, sigma):
    return max(0.01, price*math.exp((mu-0.5*sigma*sigma)+sigma*random.gauss(0,1)))

def sma(vals, n):
    if n<=0 or len(vals)<n: return None
    return sum(vals[-n:])/n

def ema_series(vals, n):
    if len(vals) < n: return [None]*len(vals)
    k = 2/(n+1); out = [None]*(n-1); e = sum(vals[:n])/n; out.append(e)
    for v in vals[n:]:
        e = v*k + e*(1-k); out.append(e)
    return out

def macd(vals):
    if len(vals) < 26: return None, None
    e12 = ema_series(vals, 12); e26 = ema_series(vals, 26)
    off = len(vals) - len(e26)
    macd_line = [ (e12[i+off-(len(vals)-len(e12))] - e26[i]) if e12[i+off-(len(vals)-len(e12))] is not None and e26[i] is not None else None for i in range(len(e26)) ]
    line_vals = [x for x in macd_line if x is not None]
    if len(line_vals) < 9: return (macd_line[-1] if macd_line else None), None
    sig = ema_series(line_vals, 9)[-1]
    return macd_line[-1], sig

def bollinger(vals, n=20, k=2):
    if len(vals) < n: return None, None, None
    window = vals[-n:]; m = sum(window)/n
    var = sum((x-m)**2 for x in window)/n; sd = math.sqrt(var)
    return m-k*sd, m, m+k*sd

def rsi_val(vals, n=14):
    if len(vals) < n+1: return 50.0
    w = vals[-(n+1):]
    diffs = [w[i]-w[i-1] for i in range(1,len(w))]
    ag = sum(d for d in diffs if d>0)/n
    al = sum(-d for d in diffs if d<0)/n
    return 100.0 if al==0 else 100-(100/(1+ag/al))

def max_dd(hist):
    if not hist: return 0.0
    peak = hist[0]; worst = 0.0
    for v in hist:
        if v>peak: peak=v
        if peak>0: worst=max(worst, (peak-v)/peak)
    return worst

INDICATOR_ALIASES = {"rsi":"RSI","price":"PRICE","close":"PRICE","vix":"VIX","volatility":"VIX",
                      "macd":"MACD","volume":"VOLUME","bollinger":"BOLL","bb":"BOLL"}

def parse_plain_english(text):
    text = text.lower().strip()
    action = "BUY" if "buy" in text else ("SELL" if "sell" in text else None)
    if action is None: return None, "Start your sentence with 'buy' or 'sell'."
    m = re.search(r"(rsi|price|vix|macd)\s*(below|under|less than|above|over|greater than)\s*(-?\d+(?:\.\d+)?)", text)
    if m:
        ind_raw, comp, val = m.group(1), m.group(2), float(m.group(3))
        ind = INDICATOR_ALIASES.get(ind_raw, ind_raw.upper())
        op = "<" if comp in ("below","under","less than") else ">"
        return [{"indicator": ind, "op": op, "value": val, "action": action}], None
    m2 = re.search(r"(\d+)\s*(?:sma|ema)?\s*crosses?\s*(above|below)\s*(\d+)\s*(?:sma|ema)?", text)
    if m2:
        fast, comp, slow = int(m2.group(1)), m2.group(2), int(m2.group(3))
        op = "cross_up" if comp=="above" else "cross_down"
        return [{"indicator":"SMA_CROSS","op":op,"fast":fast,"slow":slow,"action":action}], None
    m3 = re.search(r"bollinger|bb", text)
    if m3:
        op = "touch_lower" if ("lower" in text or "below" in text) else "touch_upper"
        return [{"indicator":"BOLL","op":op,"action":action}], None
    return None, "Try: 'buy when rsi below 30', 'sell when price above 250', 'buy when 5 sma crosses above 20 sma', 'buy when bollinger lower band touched'."

def eval_rule(rule, series, current_price, vix_val=None):
    ind = rule["indicator"]
    if ind == "RSI":
        r = rsi_val(series)
        return (r < rule["value"]) if rule["op"]=="<" else (r > rule["value"])
    if ind == "PRICE":
        return (current_price < rule["value"]) if rule["op"]=="<" else (current_price > rule["value"])
    if ind == "VIX":
        if vix_val is None: return False
        return (vix_val < rule["value"]) if rule["op"]=="<" else (vix_val > rule["value"])
    if ind == "MACD":
        m, s = macd(series)
        if m is None or s is None: return False
        return (m < s) if rule["op"]=="<" else (m > s)
    if ind == "BOLL":
        lo, mid, hi = bollinger(series)
        if lo is None: return False
        if rule["op"] == "touch_lower": return current_price <= lo
        if rule["op"] == "touch_upper": return current_price >= hi
        return False
    if ind == "SMA_CROSS":
        cf, cs = sma(series, rule["fast"]), sma(series, rule["slow"])
        pf, ps = sma(series[:-1], rule["fast"]), sma(series[:-1], rule["slow"])
        if None in (cf,cs,pf,ps): return False
        if rule["op"]=="cross_up": return pf<=ps and cf>cs
        else: return pf>=ps and cf<cs
    return False

VIX_CACHE = {"value": None, "ts": 0}
def get_india_vix():
    if not HAS_YF: return None
    now = time.time()
    if VIX_CACHE["value"] is not None and now-VIX_CACHE["ts"] < 60:
        return VIX_CACHE["value"]
    try:
        h = yf.Ticker("^INDIAVIX").history(period="1d", interval="5m")
        if not h.empty:
            VIX_CACHE["value"] = round(float(h["Close"].iloc[-1]), 2)
            VIX_CACHE["ts"] = now
    except Exception:
        pass
    return VIX_CACHE["value"]

def search_symbol(query):
    q = query.strip().upper()
    if not HAS_YF: return None, "yfinance not installed on server."
    candidates = [q]
    if not q.endswith((".NS",".BO")) and re.match(r"^[A-Z&]+$", q) and "-USD" not in q:
        candidates.append(q+".NS")
    for cand in candidates:
        try:
            h = yf.Ticker(cand).history(period="5d", interval="1d")
            if h is not None and not h.empty:
                last = float(h["Close"].iloc[-1])
                return {"symbol": cand, "last_price": round(last,4),
                        "is_indian": is_indian_symbol(cand), "has_fno": has_fno(cand)}, None
        except Exception:
            continue
    return None, f"Symbol '{query}' not found."

def fetch_ohlc(ticker, interval="1d", period="6mo"):
    if not HAS_YF: return None, "yfinance not installed"
    try:
        hist = yf.Ticker(ticker).history(period=period, interval=interval)
        hist = hist.dropna(subset=["Close"])
        if len(hist) < 5: return None, f"Only {len(hist)} bars"
        return {"o": hist["Open"].tolist(), "h": hist["High"].tolist(),
                "l": hist["Low"].tolist(), "c": hist["Close"].tolist(),
                "t": [str(x) for x in hist.index]}, None
    except Exception as e:
        return None, str(e)[:150]

def chartink_screener(scan_clause_url_or_slug):
    """Best-effort Chartink puller. Chartink has NO official API.
    We hit their public screener processing endpoint used by the website itself.
    If Chartink changes their markup this WILL need a fix - documented clearly to user."""
    if not HAS_REQ:
        return None, "requests library not installed on server."
    try:
        sess = requests.Session()
        slug = scan_clause_url_or_slug.strip().rstrip("/").split("/")[-1]
        page = sess.get(f"https://chartink.com/screener/{slug}", timeout=10)
        m = re.search(r'name="csrf-token" content="([^"]+)"', page.text)
        if not m:
            return None, "Could not read Chartink page (site structure may have changed)."
        csrf = m.group(1)
        m2 = re.search(r'"scan_clause"\s*:\s*"([^"]+)"', page.text.replace("\\/", "/"))
        scan_clause = m2.group(1) if m2 else None
        if not scan_clause:
            return None, "Could not find scan clause on page - screener slug may be wrong."
        resp = sess.post("https://chartink.com/screener/process",
                          data={"scan_clause": scan_clause},
                          headers={"x-csrf-token": csrf}, timeout=10)
        data = resp.json()
        rows = data.get("data", [])
        symbols = [r.get("nsecode") for r in rows if r.get("nsecode")]
        return symbols, None
    except Exception as e:
        return None, f"Chartink pull failed: {str(e)[:150]} (their site structure may have changed)"

def mk_state():
    return {
        "tick": 0, "mode": "GLOBAL",
        "prices": {k: v["p0"] for k, v in ASSETS.items()},
        "history": {k: [v["p0"]] for k, v in ASSETS.items()},
        "portfolio": {"cash": INIT_CASH, "pos": {k: {"qty":0.,"avg":0.,"sl":None,"tp":None} for k in ASSETS}},
        "trades": [], "nid": 1, "pending": [],
        "pvhist": [INIT_CASH],
        "strat": {"type":"manual","fast":5,"slow":20,"active":False,"rules":[],"rule_text":""},
        "watchlist": ["BTC-USD","ETH-USD","AAPL","TSLA","RELIANCE.NS","NSEI"],
        "chartink_symbols": [],
    }

STATE = mk_state()
LOCK = threading.Lock()
ALERTS = []
SSE_CLIENTS = []
ALERT_LOCK = threading.Lock()

def push_alert(asset, pattern, direction, price, detail=""):
    a = {"id": int(time.time()*1000), "time": datetime.now(timezone.utc).strftime("%H:%M UTC"),
         "asset": asset, "pattern": pattern, "direction": direction, "price": round(price,4), "detail": detail}
    with ALERT_LOCK:
        ALERTS.insert(0, a)
        if len(ALERTS) > 100: del ALERTS[100:]
        for q in SSE_CLIENTS:
            try: q.put_nowait(a)
            except Exception: pass
    return a

def pv(s): return s["portfolio"]["cash"] + sum(p["qty"]*s["prices"].get(a,0) for a,p in s["portfolio"]["pos"].items())

def record(s, asset, side, qty, price, via, pnlval=None):
    t = {"id": s["nid"], "tick": s["tick"], "ts": datetime.now(timezone.utc).strftime("%H:%M"),
         "asset": asset, "side": side, "qty": round(qty,8), "price": round(price,4), "via": via,
         "pnl": round(pnlval,2) if pnlval is not None else None}
    s["nid"] += 1; s["trades"].insert(0, t)
    if len(s["trades"]) > MAXTRADES: del s["trades"][MAXTRADES:]

def ensure_asset(s, asset, price_hint=None):
    if asset not in ASSETS:
        ASSETS[asset] = {"name": asset, "p0": price_hint or 100.0, "mu": 0.0001, "sigma": 0.02}
        s["prices"][asset] = price_hint or 100.0
        s["history"][asset] = [price_hint or 100.0]
        s["portfolio"]["pos"][asset] = {"qty":0.,"avg":0.,"sl":None,"tp":None}

def exec_order(s, asset, side, qty, sl=None, tp=None, via="MARKET"):
    ensure_asset(s, asset)
    if side not in ("BUY","SELL"): return False, "Invalid side"
    if not qty or qty <= 0: return False, "Quantity must be positive"
    price = s["prices"][asset]; pos = s["portfolio"]["pos"][asset]
    if side == "BUY":
        cost = price*qty
        if s["portfolio"]["cash"] < cost-1e-9: return False, "Insufficient cash"
        nq = pos["qty"]+qty
        pos["avg"] = (pos["avg"]*pos["qty"]+price*qty)/nq if nq else 0
        pos["qty"] = nq; s["portfolio"]["cash"] -= cost
        if sl is not None: pos["sl"] = sl
        if tp is not None: pos["tp"] = tp
        record(s, asset, side, qty, price, via)
        return True, f"Bought {qty:g} {asset} @ {price:.4f}"
    else:
        if pos["qty"] < qty-1e-9: return False, "Insufficient position"
        pnlval = (price-pos["avg"])*qty
        pos["qty"] -= qty
        if pos["qty"] < 1e-9: pos.update(qty=0.,avg=0.,sl=None,tp=None)
        s["portfolio"]["cash"] += price*qty
        record(s, asset, side, qty, price, via, pnlval)
        return True, f"Sold {qty:g} {asset} @ {price:.4f}"

def do_tick(s):
    s["tick"] += 1
    vix = get_india_vix()
    for asset, cfg in ASSETS.items():
        s["prices"][asset] = gbm(s["prices"][asset], cfg["mu"], cfg["sigma"])
        h = s["history"].setdefault(asset, [s["prices"][asset]])
        h.append(s["prices"][asset])
        if len(h) > MAXHIST: del h[0]
    still = []
    for o in s["pending"]:
        p = s["prices"].get(o["asset"], 0)
        fill = (o["side"]=="BUY" and p<=o["lp"]) or (o["side"]=="SELL" and p>=o["lp"])
        if fill: exec_order(s, o["asset"], o["side"], o["qty"], via="LIMIT")
        else: still.append(o)
    s["pending"] = still
    for asset, pos in s["portfolio"]["pos"].items():
        if pos["qty"] > 0:
            p = s["prices"].get(asset, 0)
            if pos["sl"] and p <= pos["sl"]: exec_order(s, asset, "SELL", pos["qty"], via="STOPLOSS")
            elif pos["tp"] and p >= pos["tp"]: exec_order(s, asset, "SELL", pos["qty"], via="TAKEPROFIT")
    st = s["strat"]
    if st.get("active"):
        for asset in list(ASSETS.keys()):
            h = s["history"].get(asset, [])
            if len(h) < 5: continue
            price = s["prices"][asset]; pos = s["portfolio"]["pos"][asset]
            sig = None
            if st["type"] == "sma":
                cf,cs = sma(h,st["fast"]), sma(h,st["slow"])
                pf,ps = sma(h[:-1],st["fast"]), sma(h[:-1],st["slow"])
                if None not in (cf,cs,pf,ps):
                    if pf<=ps and cf>cs: sig="BUY"
                    elif pf>=ps and cf<cs: sig="SELL"
            elif st["type"] == "rsi":
                r = rsi_val(h); sig = "BUY" if r<30 else ("SELL" if r>70 else None)
            elif st["type"] == "custom" and st.get("rules"):
                for rule in st["rules"]:
                    if eval_rule(rule, h, price, vix):
                        sig = rule["action"]; break
            if sig == "BUY" and s["portfolio"]["cash"] > 1:
                q = math.floor(s["portfolio"]["cash"]*AUTOFRAC/price*1e8)/1e8
                if q>0:
                    exec_order(s, asset, "BUY", q, via="AUTO")
                    push_alert(asset, "Strategy Signal", "BULLISH", price, "Auto BUY executed")
            elif sig == "SELL" and pos["qty"] > 0:
                exec_order(s, asset, "SELL", pos["qty"], via="AUTO")
                push_alert(asset, "Strategy Signal", "BEARISH", price, "Auto SELL executed")
    s["pvhist"].append(pv(s))
    if len(s["pvhist"]) > MAXHIST: del s["pvhist"][0]

def chart_pts(s, asset):
    h = s["history"].get(asset, [])
    fast, slow = s["strat"]["fast"], s["strat"]["slow"]
    start = max(0, len(h)-CHARTPTS)
    return [{"i": i, "p": round(h[i],4),
             "f": round(sma(h[:i+1],fast),4) if sma(h[:i+1],fast) else None,
             "s": round(sma(h[:i+1],slow),4) if sma(h[:i+1],slow) else None,
             "r": round(rsi_val(h[:i+1]),2)} for i in range(start, len(h))]

def win_rate(trades):
    s = [t for t in trades if t["side"]=="SELL" and t.get("pnl") is not None]
    if not s: return None
    return round(len([t for t in s if t["pnl"]>0])/len(s)*100, 1)

def snap(s):
    pos = {}
    for asset, p in s["portfolio"]["pos"].items():
        pr = s["prices"].get(asset, 0); mv = p["qty"]*pr
        pos[asset] = {"qty": round(p["qty"],8), "avg": round(p["avg"],4), "mv": round(mv,2),
                      "upnl": round((pr-p["avg"])*p["qty"],2) if p["qty"]>0 else 0., "sl": p["sl"], "tp": p["tp"]}
    tv = pv(s); pnl = tv-INIT_CASH
    return {"tick": s["tick"], "mode": s["mode"], "vix": get_india_vix(),
            "prices": {k: round(v,4) for k,v in s["prices"].items()},
            "cash": round(s["portfolio"]["cash"],2), "pos": pos,
            "tv": round(tv,2), "pnl": round(pnl,2), "pnlpct": round(pnl/INIT_CASH*100,2),
            "ddpct": round(max_dd(s["pvhist"])*100,2), "wr": win_rate(s["trades"]),
            "trades": s["trades"], "pending": s["pending"], "strat": s["strat"],
            "pvhist": s["pvhist"][-CHARTPTS:],
            "charts": {a: chart_pts(s,a) for a in list(ASSETS.keys())[:8]},
            "assets": {k: v["name"] for k,v in ASSETS.items()}, "initcash": INIT_CASH,
            "watchlist": s["watchlist"], "chartink_symbols": s["chartink_symbols"]}

def backtest_real_or_sim(asset, strat, fast, slow, nticks, seed=None, rules=None):
    ohlc = None
    if HAS_YF:
        ohlc, _ = fetch_ohlc(asset, period="1y", interval="1d")
    if ohlc:
        closes = ohlc["c"][-nticks:] if nticks < len(ohlc["c"]) else ohlc["c"]
        highs = ohlc["h"][-len(closes):]; lows = ohlc["l"][-len(closes):]; opens = ohlc["o"][-len(closes):]
    else:
        rng = random.Random(seed) if seed is not None else random.Random()
        cfg = ASSETS.get(asset, {"p0":100.0,"mu":0.0001,"sigma":0.02})
        price = cfg["p0"]; closes = [price]
        for _ in range(nticks):
            price = max(0.01, price*math.exp((cfg["mu"]-0.5*cfg["sigma"]**2)+cfg["sigma"]*rng.gauss(0,1)))
            closes.append(price)
        highs = [c*1.002 for c in closes]; lows = [c*0.998 for c in closes]; opens = closes[:]
    cash = INIT_CASH; qty=0.; avg=0.; trades=[]; pvs=[cash]
    for i in range(1, len(closes)):
        hist = closes[:i+1]; price = closes[i]; sig = None
        if strat == "sma":
            cf,cs = sma(hist,fast), sma(hist,slow); pf,ps = sma(hist[:-1],fast), sma(hist[:-1],slow)
            if None not in (cf,cs,pf,ps):
                if pf<=ps and cf>cs: sig="BUY"
                elif pf>=ps and cf<cs: sig="SELL"
        elif strat == "rsi":
           