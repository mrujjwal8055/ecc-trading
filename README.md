# ecc-trading
this is for personal use
[ecc_cloud 12.py](https://github.com/user-attachments/files/30627596/ecc_cloud.12.py)
#!/usr/bin/env python3
"""
ECC Trading Suite — Cloud Edition (Step 2)
===========================================
Runs 24/7 on Render.com (free tier).
Accessible from anywhere on mobile data.

Requirements: pip install flask yfinance

Deploy:
  1. Upload this file + requirements.txt to GitHub
  2. Connect to Render.com → New Web Service
  3. Build command : pip install -r requirements.txt
  4. Start command : python ecc_cloud.py
  5. Get your public URL and open on phone

Self-test: python ecc_cloud.py --selftest
"""

import csv, io, json, math, os, queue, random, threading, time
from datetime import datetime, timezone

from flask import Flask, Response, jsonify, request

try:
    import yfinance as yf
    HAS_YF = True
except ImportError:
    HAS_YF = False

app = Flask(__name__)

# ── Render.com uses PORT env variable ────────────────────────────────────────
PORT = int(os.environ.get("PORT", 5000))

# ─────────────────────────────────────────────────────────────────────────────
# CONSTANTS
# ─────────────────────────────────────────────────────────────────────────────
INIT_CASH   = 10_000.0
AUTO_FRAC   = 0.20
MAX_HIST    = 500
MAX_TRADES  = 200
CHART_PTS   = 80
MAX_BT      = 5_000
SCAN_EVERY  = 300   # seconds between live scans (5 min)

ASSETS = {
    "BTC":  {"name":"Bitcoin",  "p0":43_500., "mu":0.00020, "sigma":0.025},
    "ETH":  {"name":"Ethereum", "p0": 2_650., "mu":0.00015, "sigma":0.028},
    "AAPL": {"name":"Apple",    "p0":   185., "mu":0.00008, "sigma":0.012},
    "TSLA": {"name":"Tesla",    "p0":   235., "mu":0.00010, "sigma":0.032},
}

DEFAULT_WATCHLIST = [
    "BTC-USD","ETH-USD",
    "RELIANCE.NS","TCS.NS","INFY.NS","HDFCBANK.NS",
    "^NSEI","^BSESN",
    "EURUSD=X","USDINR=X",
    "AAPL","TSLA","NVDA",
]

# ─────────────────────────────────────────────────────────────────────────────
# PURE MATH
# ─────────────────────────────────────────────────────────────────────────────

def gbm(price, mu, sigma):
    return max(0.01, price * math.exp(
        (mu - 0.5*sigma**2) + sigma*random.gauss(0, 1)))

def sma(vals, n):
    if n <= 0 or len(vals) < n: return None
    return sum(vals[-n:]) / n

def rsi_val(vals, n=14):
    if len(vals) < n+1: return 50.0
    w = vals[-(n+1):]
    diffs = [w[i]-w[i-1] for i in range(1, len(w))]
    ag = sum(d for d in diffs if d > 0) / n
    al = sum(-d for d in diffs if d < 0) / n
    return 100.0 if al == 0 else 100 - 100/(1+ag/al)

def rsi_series_full(closes, n=14):
    k = len(closes); out = [None]*k
    if k < n+1: return out
    g = [max(closes[i]-closes[i-1], 0.) for i in range(1, n+1)]
    l = [max(closes[i-1]-closes[i], 0.) for i in range(1, n+1)]
    ag = sum(g)/n; al = sum(l)/n
    out[n] = 100. if al==0 else 100-100/(1+ag/al)
    for i in range(n+1, k):
        d = closes[i]-closes[i-1]
        ag = (ag*(n-1)+max(d,0))/n; al = (al*(n-1)+max(-d,0))/n
        out[i] = 100. if al==0 else 100-100/(1+ag/al)
    return out

def sma_signal(vals, fast, slow):
    if fast<=0 or slow<=0 or fast>=slow or len(vals)<slow+1: return "HOLD"
    cf,cs = sma(vals,fast), sma(vals,slow)
    pf,ps = sma(vals[:-1],fast), sma(vals[:-1],slow)
    if None in (cf,cs,pf,ps): return "HOLD"
    if pf<ps and cf>cs: return "BUY"
    if pf>ps and cf<cs: return "SELL"
    return "HOLD"

def rsi_signal(vals, n=14, lo=30, hi=70):
    r = rsi_val(vals, n)
    return "BUY" if r<lo else ("SELL" if r>hi else "HOLD")

def maxdd(hist):
    if not hist: return 0.0
    peak=hist[0]; worst=0.0
    for v in hist:
        if v>peak: peak=v
        if peak>0: worst = max(worst, (peak-v)/peak)
    return worst

# ── Pattern detectors ─────────────────────────────────────────────────────────

def find_swings(highs, lows, win=3):
    n=len(highs); sh=[]; sl=[]
    for i in range(win, n-win):
        if highs[i]==max(highs[i-win:i+win+1]): sh.append((i, highs[i]))
        if lows[i] ==min(lows [i-win:i+win+1]): sl.append((i, lows[i]))
    return sh, sl

def detect_divergence(sh, sl, rsi_s):
    cands = []
    if len(sl)>=2:
        (i1,p1),(i2,p2) = sl[-2],sl[-1]
        r1,r2 = rsi_s[i1],rsi_s[i2]
        if r1 and r2 and p2<p1 and r2>r1:
            cands.append({"direction":"BULLISH","pivot":i2})
    if len(sh)>=2:
        (i1,p1),(i2,p2) = sh[-2],sh[-1]
        r1,r2 = rsi_s[i1],rsi_s[i2]
        if r1 and r2 and p2>p1 and r2<r1:
            cands.append({"direction":"BEARISH","pivot":i2})
    if not cands: return None
    return max(cands, key=lambda c:c["pivot"])

def confirm_entry(div, closes):
    ci = div["pivot"]+1
    if ci>=len(closes): return None
    if div["direction"]=="BULLISH" and closes[ci]>closes[div["pivot"]]: return ci
    if div["direction"]=="BEARISH" and closes[ci]<closes[div["pivot"]]: return ci
    return None

def detect_tl_breakout(sh, sl, closes, lk=4):
    n=len(closes)
    if n<2: return None
    li,pi = n-1,n-2; result=None
    def fit(pts):
        if len(pts)<2: return None
        xs=[p[0] for p in pts]; ys=[p[1] for p in pts]; m=len(pts)
        mx=sum(xs)/m; my=sum(ys)/m
        den=sum((x-mx)**2 for x in xs)
        if den==0: return None
        s=sum((x-mx)*(y-my) for x,y in zip(xs,ys))/den
        return s, my-s*mx
    rh=sh[-lk:]
    f=fit(rh)
    if f:
        s,ic=f
        if s<0 and closes[li]>s*li+ic and closes[pi]<=s*pi+ic:
            result={"direction":"BULLISH_BREAKOUT","price":closes[li]}
    rl=sl[-lk:]
    if result is None:
        f=fit(rl)
        if f:
            s,ic=f
            if s>0 and closes[li]<s*li+ic and closes[pi]>=s*pi+ic:
                result={"direction":"BEARISH_BREAKDOWN","price":closes[li]}
    return result

# ─────────────────────────────────────────────────────────────────────────────
# ALERT SYSTEM  (SSE broadcast to all connected browsers)
# ─────────────────────────────────────────────────────────────────────────────

ALERTS      = []
SSE_CLIENTS = []
ALERT_LOCK  = threading.Lock()

def push_alert(asset, pattern, direction, price, detail=""):
    a = {
        "id":        int(time.time()*1000),
        "time":      datetime.now(timezone.utc).strftime("%H:%M UTC"),
        "asset":     asset,
        "pattern":   pattern,
        "direction": direction,
        "price":     round(price, 4),
        "detail":    detail,
    }
    with ALERT_LOCK:
        ALERTS.insert(0, a)
        if len(ALERTS) > 100: del ALERTS[100:]
        for q in SSE_CLIENTS:
            try: q.put_nowait(a)
            except: pass
    return a

# ─────────────────────────────────────────────────────────────────────────────
# PAPER TRADING STATE
# ─────────────────────────────────────────────────────────────────────────────

def mk_state():
    return {
        "tick":0,
        "prices":  {k:v["p0"] for k,v in ASSETS.items()},
        "history": {k:[v["p0"]] for k,v in ASSETS.items()},
        "portfolio":{
            "cash":INIT_CASH,
            "pos":{k:{"qty":0.,"avg":0.,"sl":None,"tp":None} for k in ASSETS},
        },
        "trades":[], "nid":1, "pending":[], "pv_hist":[INIT_CASH],
        "strat":{"type":"manual","fast":5,"slow":20,"active":False},
        "scan_seen":{},
    }

STATE = mk_state()
LOCK  = threading.Lock()

def pv(s):
    return s["portfolio"]["cash"] + sum(
        p["qty"]*s["prices"][a]
        for a,p in s["portfolio"]["pos"].items())

def record(s, asset, side, qty, price, via, pnl_val=None):
    t = {"id":s["nid"],"tick":s["tick"],
         "ts":datetime.now(timezone.utc).strftime("%H:%M"),
         "asset":asset,"side":side,"qty":round(qty,8),
         "price":round(price,4),"via":via,
         "pnl":round(pnl_val,2) if pnl_val is not None else None}
    s["nid"]+=1; s["trades"].insert(0,t)
    if len(s["trades"])>MAX_TRADES: del s["trades"][MAX_TRADES:]

def exec_order(s, asset, side, qty, sl=None, tp=None, via="MARKET"):
    if asset not in ASSETS:        return False,"Unknown asset"
    if side not in("BUY","SELL"):  return False,"Invalid side"
    if not qty or qty<=0:           return False,"Quantity must be positive"
    price=s["prices"][asset]; pos=s["portfolio"]["pos"][asset]
    if side=="BUY":
        cost=price*qty
        if s["portfolio"]["cash"]<cost-1e-9: return False,"Insufficient cash"
        nq=pos["qty"]+qty
        pos["avg"]=(pos["avg"]*pos["qty"]+price*qty)/nq
        pos["qty"]=nq; s["portfolio"]["cash"]-=cost
        if sl is not None: pos["sl"]=sl
        if tp is not None: pos["tp"]=tp
        record(s,asset,side,qty,price,via)
        return True,f"Bought {qty:g} {asset} @ ${price:,.4f}"
    if pos["qty"]<qty-1e-9: return False,"Insufficient position"
    pnl_val=(price-pos["avg"])*qty
    pos["qty"]-=qty
    if pos["qty"]<1e-9: pos.update(qty=0.,avg=0.,sl=None,tp=None)
    s["portfolio"]["cash"]+=price*qty
    record(s,asset,side,qty,price,via,pnl_val)
    return True,f"Sold {qty:g} {asset} @ ${price:,.4f}"

def do_tick(s):
    s["tick"]+=1
    for asset,cfg in ASSETS.items():
        s["prices"][asset]=gbm(s["prices"][asset],cfg["mu"],cfg["sigma"])
        h=s["history"][asset]; h.append(s["prices"][asset])
        if len(h)>MAX_HIST: del h[0]
    still=[]
    for o in s["pending"]:
        p=s["prices"][o["asset"]]
        fill=(o["side"]=="BUY" and p<=o["lp"]) or (o["side"]=="SELL" and p>=o["lp"])
        if fill: exec_order(s,o["asset"],o["side"],o["qty"],via="LIMIT")
        else: still.append(o)
    s["pending"]=still
    for asset,pos in s["portfolio"]["pos"].items():
        if pos["qty"]>0:
            p=s["prices"][asset]
            if pos["sl"] and p<=pos["sl"]:
                exec_order(s,asset,"SELL",pos["qty"],via="STOP_LOSS")
            elif pos["tp"] and p>=pos["tp"]:
                exec_order(s,asset,"SELL",pos["qty"],via="TAKE_PROFIT")
    st=s["strat"]
    if st.get("active") and st.get("type") in("sma","rsi"):
        for asset in ASSETS:
            h=s["history"][asset]; p=s["prices"][asset]
            sig=(sma_signal(h,st["fast"],st["slow"]) if st["type"]=="sma"
                 else rsi_signal(h))
            pos=s["portfolio"]["pos"][asset]
            if sig=="BUY" and s["portfolio"]["cash"]>1.:
                q=math.floor((s["portfolio"]["cash"]*AUTO_FRAC/p)*1e8)/1e8
                if q>0: exec_order(s,asset,"BUY",q,via="AUTO")
            elif sig=="SELL" and pos["qty"]>0:
                exec_order(s,asset,"SELL",pos["qty"],via="AUTO")
    s["pv_hist"].append(pv(s))
    if len(s["pv_hist"])>MAX_HIST: del s["pv_hist"][0]

def chart_pts(s, asset):
    h=s["history"][asset]; fast=s["strat"]["fast"]; slow=s["strat"]["slow"]
    start=max(0,len(h)-CHART_PTS)
    return [{"t":i,"p":round(h[i],4),
             "f":(lambda v:round(v,4) if v else None)(sma(h[:i+1],fast)),
             "s":(lambda v:round(v,4) if v else None)(sma(h[:i+1],slow)),
             "r":round(rsi_val(h[:i+1]),2)}
            for i in range(start,len(h))]

def win_rate(trades):
    s=[t for t in trades if t["side"]=="SELL" and t.get("pnl") is not None]
    if not s: return None
    return round(len([t for t in s if t["pnl"]>0])/len(s)*100,1)

def snap(s):
    pos={}
    for asset,p in s["portfolio"]["pos"].items():
        pr=s["prices"][asset]; mv=p["qty"]*pr
        pos[asset]={"qty":round(p["qty"],8),"avg":round(p["avg"],4),
                    "mv":round(mv,2),
                    "upnl":round((pr-p["avg"])*p["qty"],2) if p["qty"]>0 else 0.,
                    "sl":p["sl"],"tp":p["tp"]}
    tv=pv(s); pnl=tv-INIT_CASH
    return {"tick":s["tick"],
            "prices":{k:round(v,4) for k,v in s["prices"].items()},
            "cash":round(s["portfolio"]["cash"],2),"pos":pos,
            "tv":round(tv,2),"pnl":round(pnl,2),
            "pnl_pct":round(pnl/INIT_CASH*100,2),
            "dd_pct":round(maxdd(s["pv_hist"])*100,2),
            "wr":win_rate(s["trades"]),"trades":s["trades"][:40],
            "pending":s["pending"],"strat":s["strat"],
            "pv_hist":s["pv_hist"][-CHART_PTS:],
            "charts":{a:chart_pts(s,a) for a in ASSETS},
            "assets":{k:{"name":v["name"]} for k,v in ASSETS.items()},
            "init_cash":INIT_CASH}

# ─────────────────────────────────────────────────────────────────────────────
# BACKTEST
# ─────────────────────────────────────────────────────────────────────────────

def backtest(asset, strat, fast, slow, nticks, seed=None):
    cfg=ASSETS[asset]; rng=random.Random(seed) if seed is not None else random.Random()
    price=cfg["p0"]; hist=[price]; cash=INIT_CASH; qty=0.; avg=0.
    trades=[]; pvs=[cash]
    for i in range(1, nticks+1):
        price=max(0.01,price*math.exp(
            (cfg["mu"]-0.5*cfg["sigma"]**2)+cfg["sigma"]*rng.gauss(0,1)))
        hist.append(price)
        sig=(sma_signal(hist,fast,slow) if strat=="sma" else rsi_signal(hist))
        if sig=="BUY" and cash>1.:
            bq=math.floor((cash*AUTO_FRAC/price)*1e8)/1e8
            if bq>0:
                nq=qty+bq; avg=(avg*qty+price*bq)/nq; qty=nq; cash-=bq*price
                trades.append({"side":"BUY","price":price})
        elif sig=="SELL" and qty>0:
            cash+=qty*price
            trades.append({"side":"SELL","price":price,"avg":avg})
            qty=0.; avg=0.
        pvs.append(cash+qty*price)
    fv=pvs[-1]; pnl=fv-INIT_CASH
    sells=[t for t in trades if t["side"]=="SELL"]
    wins=[t for t in sells if t["price"]>t.get("avg",0)]
    wr=round(len(wins)/len(sells)*100,1) if sells else None
    stride=max(1,nticks//150)
    return {"asset":asset,"strat":strat,"nticks":nticks,
            "fv":round(fv,2),"pnl":round(pnl,2),
            "pnl_pct":round(pnl/INIT_CASH*100,2),
            "dd_pct":round(maxdd(pvs)*100,2),
            "ntrades":len(trades),"wr":wr,
            "ph":[round(p,4) for p in hist[::stride]],
            "pvh":[round(v,2) for v in pvs[::stride]]}

# ─────────────────────────────────────────────────────────────────────────────
# LIVE MARKET SCANNER  (runs every SCAN_EVERY seconds in background)
# ─────────────────────────────────────────────────────────────────────────────

SCAN_STATUS   = {"running":False,"last":"Never","next_in":SCAN_EVERY,"tickers":[]}
SCAN_STATUS_L = threading.Lock()

def fetch_ohlcv(ticker, interval="1d", period="6mo"):
    if not HAS_YF:
        return None, "yfinance not installed"
    try:
        hist = yf.Ticker(ticker).history(period=period, interval=interval)
        if hist is None or hist.empty:
            return None, "No data"
        hist = hist.dropna(subset=["Close"])
        if len(hist) < 20:
            return None, f"Only {len(hist)} bars"
        return {
            "closes": hist["Close"].tolist(),
            "highs":  hist["High"].tolist(),
            "lows":   hist["Low"].tolist(),
            "ts":     [str(t) for t in hist.index],
        }, None
    except Exception as e:
        return None, str(e)[:60]

def scan_ticker(ticker, data, seen):
    closes = data["closes"]
    highs  = data["highs"]
    lows   = data["lows"]
    ts     = data["ts"]
    rs     = rsi_series_full(closes)
    sh, sl = find_swings(highs, lows, win=3)
    alerts = []

    div = detect_divergence(sh, sl, rs)
    if div:
        ci = confirm_entry(div, closes)
        if ci is not None:
            key = f"{ticker}_div_{div['direction']}"
            if seen.get(key) != ts[ci]:
                a = push_alert(ticker, "RSI Divergence",
                               div["direction"], closes[ci])
                alerts.append(a)
                seen[key] = ts[ci]

    bo = detect_tl_breakout(sh, sl, closes)
    if bo:
        key = f"{ticker}_tl_{bo['direction']}"
        cur_ts = ts[-1] if ts else ""
        if seen.get(key) != cur_ts:
            a = push_alert(ticker, "Trendline Breakout",
                           bo["direction"], bo["price"])
            alerts.append(a)
            seen[key] = cur_ts

    return alerts

def background_scanner(watchlist):
    seen = {}
    while True:
        with SCAN_STATUS_L:
            SCAN_STATUS["running"] = True
            SCAN_STATUS["tickers"] = []

        for ticker in watchlist:
            data, err = fetch_ohlcv(ticker)
            status_line = f"{ticker}: " + ("scanned" if data else f"skipped ({err})")
            with SCAN_STATUS_L:
                SCAN_STATUS["tickers"].append(status_line)
            if data:
                try: scan_ticker(ticker, data, seen)
                except: pass

        now = datetime.now(timezone.utc).strftime("%H:%M UTC")
        with SCAN_STATUS_L:
            SCAN_STATUS["running"] = False
            SCAN_STATUS["last"]    = now
            SCAN_STATUS["next_in"] = SCAN_EVERY

        # Count down next_in each second
        for i in range(SCAN_EVERY, 0, -1):
            time.sleep(1)
            with SCAN_STATUS_L:
                SCAN_STATUS["next_in"] = i

# ─────────────────────────────────────────────────────────────────────────────
# FLASK ROUTES
# ─────────────────────────────────────────────────────────────────────────────

@app.route("/")
def index():
    return MAIN_HTML

@app.route("/health")
def health():
    """Keep-alive endpoint for UptimeRobot — ping this every 5 min."""
    return jsonify({"ok":True,"status":"running",
                    "tick": STATE["tick"],
                    "alerts": len(ALERTS)})

@app.route("/manifest.json")
def pwa_manifest():
    """PWA manifest — enables Add to Home Screen as a proper app icon."""
    m = {"name":"ECC Trading Suite","short_name":"ECC Trading",
         "description":"24/7 paper trading + live signal scanner",
         "start_url":"/","display":"standalone",
         "background_color":"#0d1117","theme_color":"#0d1117",
         "orientation":"portrait",
         "icons":[{"src":"/icon.svg","sizes":"any",
                   "type":"image/svg+xml","purpose":"any maskable"}]}
    from flask import Response as FR
    return FR(json.dumps(m), mimetype="application/json")

@app.route("/icon.svg")
def app_icon():
    """App icon shown on phone home screen."""
    svg = ('<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 100 100">'
           '<rect width="100" height="100" rx="22" fill="#0d1117"/>'
           '<polyline points="15,70 30,45 45,60 60,30 75,50 85,35" '
           'fill="none" stroke="#3fb950" stroke-width="7" '
           'stroke-linecap="round" stroke-linejoin="round"/>'
           '<circle cx="85" cy="35" r="5" fill="#3fb950"/>'
           '</svg>')
    from flask import Response as FR
    return FR(svg, mimetype="image/svg+xml")

@app.route("/api/telegram/test", methods=["POST"])
def api_telegram_test():
    """Test Telegram alerts. Set BOT_TOKEN + CHAT_ID env vars on Render."""
    token   = os.environ.get("BOT_TOKEN","")
    chat_id = os.environ.get("CHAT_ID","")
    if not token or not chat_id:
        return jsonify({"ok":False,
            "error":"Set BOT_TOKEN and CHAT_ID in Render environment variables"}), 400
    try:
        import urllib.request, urllib.parse
        msg  = "ECC Trading Bot connected!\nYou will receive signal alerts here."
        url  = f"https://api.telegram.org/bot{token}/sendMessage"
        data = urllib.parse.urlencode(
            {"chat_id":chat_id,"text":msg}).encode()
        urllib.request.urlopen(
            urllib.request.Request(url, data=data), timeout=10)
        return jsonify({"ok":True,"message":"Test message sent!"})
    except Exception as e:
        return jsonify({"ok":False,"error":str(e)}), 500

@app.route("/api/state")
def api_state():
    with LOCK: s = snap(STATE)
    return jsonify({"ok":True,"state":s})

@app.route("/api/tick", methods=["POST"])
def api_tick():
    with LOCK: do_tick(STATE); s = snap(STATE)
    return jsonify({"ok":True,"state":s})

@app.route("/api/reset", methods=["POST"])
def api_reset():
    global STATE
    with LOCK: STATE = mk_state(); s = snap(STATE)
    return jsonify({"ok":True,"state":s})

@app.route("/api/order", methods=["POST"])
def api_order():
    d = request.get_json(silent=True) or {}
    asset=d.get("asset"); side=d.get("side"); otype=d.get("order_type","MARKET")
    if asset not in ASSETS:        return jsonify({"ok":False,"error":"Unknown asset"}),400
    if side not in("BUY","SELL"):  return jsonify({"ok":False,"error":"Invalid side"}),400
    if otype not in("MARKET","LIMIT"): return jsonify({"ok":False,"error":"Invalid order type"}),400
    try: qty=float(d.get("qty"))
    except: return jsonify({"ok":False,"error":"Invalid quantity"}),400
    if not math.isfinite(qty) or qty<=0:
        return jsonify({"ok":False,"error":"Quantity must be positive"}),400
    def pof(k):
        v=d.get(k)
        if v in(None,"","null"): return None
        try: f=float(v); return f if math.isfinite(f) else None
        except: return None
    sl=pof("sl") if side=="BUY" else None
    tp=pof("tp") if side=="BUY" else None
    lp=pof("limit_price") if otype=="LIMIT" else None
    if otype=="LIMIT" and (lp is None or lp<=0):
        return jsonify({"ok":False,"error":"Limit price must be positive"}),400
    with LOCK:
        pnow=STATE["prices"][asset]
        if sl is not None and sl>=pnow:
            return jsonify({"ok":False,"error":"Stop-loss must be below current price"}),400
        if tp is not None and tp<=pnow:
            return jsonify({"ok":False,"error":"Take-profit must be above current price"}),400
        if otype=="MARKET":
            ok,msg=exec_order(STATE,asset,side,qty,sl=sl,tp=tp)
        else:
            STATE["pending"].append({"id":int(time.time()*1000),
                "asset":asset,"side":side,"qty":qty,"lp":lp})
            ok,msg=True,f"Limit {side} {qty:g} {asset} @ ${lp:,.4f}"
        s=snap(STATE)
    if ok: return jsonify({"ok":True,"message":msg,"state":s})
    return jsonify({"ok":False,"error":msg,"state":s}),400

@app.route("/api/strategy", methods=["POST"])
def api_strategy():
    d=request.get_json(silent=True) or {}
    t=d.get("type","manual")
    if t not in("manual","sma","rsi"):
        return jsonify({"ok":False,"error":"Invalid strategy"}),400
    try: fast=int(d.get("fast",5)); slow=int(d.get("slow",20))
    except: return jsonify({"ok":False,"error":"fast/slow must be integers"}),400
    if fast<2 or slow<3 or fast>=slow:
        return jsonify({"ok":False,"error":"Need 2 <= fast < slow"}),400
    active=bool(d.get("active",False))
    with LOCK:
        STATE["strat"]={"type":t,"fast":fast,"slow":slow,"active":active}
        s=snap(STATE)
    return jsonify({"ok":True,"state":s})

@app.route("/api/backtest", methods=["POST"])
def api_backtest():
    d=request.get_json(silent=True) or {}
    asset=d.get("asset","BTC"); strat=d.get("strat","sma")
    if asset not in ASSETS:
        return jsonify({"ok":False,"error":"Unknown asset"}),400
    if strat not in("sma","rsi"):
        return jsonify({"ok":False,"error":"Strategy must be sma or rsi"}),400
    try:
        fast=int(d.get("fast",5)); slow=int(d.get("slow",20))
        nt=int(d.get("nt",500))
    except: return jsonify({"ok":False,"error":"Invalid parameters"}),400
    if fast<2 or slow<3 or fast>=slow:
        return jsonify({"ok":False,"error":"Need 2 <= fast < slow"}),400
    nt=max(10,min(nt,MAX_BT))
    try: seed=int(d.get("seed")) if d.get("seed") not in(None,"","null") else None
    except: seed=None
    return jsonify({"ok":True,"result":backtest(asset,strat,fast,slow,nt,seed)})

@app.route("/api/alerts")
def api_alerts():
    with ALERT_LOCK: a=list(ALERTS)
    return jsonify({"ok":True,"alerts":a})

@app.route("/api/scan/status")
def api_scan_status():
    with SCAN_STATUS_L: s=dict(SCAN_STATUS)
    return jsonify({"ok":True,"has_yf":HAS_YF,"status":s})

@app.route("/api/export")
def api_export():
    with LOCK: trades=list(STATE["trades"])
    buf=io.StringIO(); w=csv.writer(buf)
    w.writerow(["id","tick","time","asset","side","qty","price","via","pnl"])
    for t in reversed(trades):
        w.writerow([t["id"],t["tick"],t["ts"],t["asset"],t["side"],
                    t["qty"],t["price"],t["via"],t["pnl"]])
    return Response(buf.getvalue(), mimetype="text/csv",
                    headers={"Content-Disposition":
                             'attachment;filename="trades.csv"'})

@app.route("/api/events")
def api_events():
    def stream():
        q=queue.Queue()
        with ALERT_LOCK: SSE_CLIENTS.append(q)
        try:
            while True:
                try:
                    a=q.get(timeout=20)
                    yield f"data: {json.dumps(a)}\n\n"
                except queue.Empty:
                    yield ":ping\n\n"
        finally:
            with ALERT_LOCK:
                try: SSE_CLIENTS.remove(q)
                except: pass
    return Response(stream(), mimetype="text/event-stream",
                    headers={"Cache-Control":"no-cache",
                             "X-Accel-Buffering":"no"})

# ─────────────────────────────────────────────────────────────────────────────
# FRONTEND  (identical mobile-first UI as Step 1, + Live Scanner tab)
# ─────────────────────────────────────────────────────────────────────────────

MAIN_HTML = r"""<!DOCTYPE html>
<html lang="en"><head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width,initial-scale=1,maximum-scale=1">
<meta name="apple-mobile-web-app-capable" content="yes">
<meta name="mobile-web-app-capable" content="yes">
<meta name="theme-color" content="#0d1117">
<link rel="manifest" href="/manifest.json">
<link rel="apple-touch-icon" href="/icon.svg">
<title>ECC Trading</title>
<style>
*{box-sizing:border-box;margin:0;padding:0;-webkit-tap-highlight-color:transparent}
html,body{height:100%}
body{background:#0d1117;color:#e6edf3;font-family:-apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,sans-serif;font-size:14px;padding-bottom:72px}
.mono{font-family:ui-monospace,monospace}
.pos{color:#3fb950}.neg{color:#f85149}.muted{color:#8b949e}
#toast{position:fixed;top:12px;left:50%;transform:translateX(-50%) translateY(-80px);padding:10px 18px;border-radius:20px;font-size:13px;font-weight:500;transition:transform .3s;z-index:200;white-space:nowrap;pointer-events:none}
#toast.show{transform:translateX(-50%) translateY(0)}
#toast.ok{background:#1a5c30;color:#3fb950;border:1px solid #2a8c48}
#toast.err{background:#5c1a1a;color:#f85149;border:1px solid #8c2a2a}
#toast.alert{background:#1a3a5c;color:#58a6ff;border:1px solid #2a5a8c}
.hdr{background:#161b22;border-bottom:1px solid #21262d;padding:10px 14px;display:flex;justify-content:space-between;align-items:center;position:sticky;top:0;z-index:100;gap:10px;flex-wrap:wrap}
.brand{font-size:13px;font-weight:600}
.hdr-val{font-size:18px;font-weight:600;font-family:ui-monospace,monospace}
.btn{padding:8px 14px;border-radius:20px;border:none;cursor:pointer;font-weight:600;font-size:13px;min-width:44px;min-height:44px;display:flex;align-items:center;justify-content:center;gap:5px}
.btn-g{background:#1a5c30;color:#3fb950}
.btn-a{background:#5c4a1a;color:#d29922}
.btn-o{background:transparent;border:1px solid #30363d;color:#8b949e}
.btn-b{background:#1a3a5c;color:#58a6ff}
.bnav{position:fixed;bottom:0;left:0;right:0;background:#161b22;border-top:1px solid #21262d;display:flex;z-index:100}
.bnav-btn{flex:1;padding:8px 4px;border:none;background:transparent;color:#6e7681;cursor:pointer;font-size:10px;font-weight:500;min-height:56px;display:flex;flex-direction:column;align-items:center;gap:3px}
.bnav-btn svg{width:20px;height:20px;stroke:currentColor;fill:none;stroke-width:1.8;stroke-linecap:round;stroke-linejoin:round}
.bnav-btn.active{color:#58a6ff}
.rdot{width:7px;height:7px;border-radius:50%;flex-shrink:0;margin-left:3px;vertical-align:middle;display:inline-block}
.rdot.green{background:#3fb950}
.rdot.amber{background:#d29922}
.rdot.off{background:#444}
.tab{display:none;padding:12px}.tab.active{display:block}
.card{background:#161b22;border:1px solid #21262d;border-radius:12px;padding:12px;margin-bottom:12px}
.ctitle{font-weight:600;font-size:12px;color:#8b949e;text-transform:uppercase;letter-spacing:.5px;margin-bottom:8px}
.asset-row{display:flex;gap:8px;overflow-x:auto;padding-bottom:4px;margin-bottom:12px;scrollbar-width:none}
.asset-row::-webkit-scrollbar{display:none}
.asset-chip{flex:0 0 auto;padding:8px 12px;border-radius:20px;border:1.5px solid #21262d;background:transparent;cursor:pointer;min-width:80px;text-align:center}
.asset-chip.sel{background:#161b22}
.chip-sym{font-size:11px;font-weight:600;color:#8b949e}
.chip-price{font-size:13px;font-weight:600;font-family:ui-monospace,monospace;margin:2px 0}
canvas{width:100%;display:block;border-radius:8px}
.side-row{display:flex;gap:8px;margin-bottom:10px}
.side-btn{flex:1;padding:10px;border-radius:10px;border:1.5px solid #21262d;background:transparent;color:#8b949e;font-weight:600;font-size:13px;cursor:pointer;min-height:44px}
.side-btn.buy{background:#1a5c30;color:#3fb950;border-color:#1a5c30}
.side-btn.sell{background:#5c1a1a;color:#f85149;border-color:#5c1a1a}
.inp{width:100%;padding:10px 12px;border-radius:10px;font-size:14px;border:1px solid #30363d;background:#0d1117;color:#e6edf3;margin-bottom:8px;font-family:ui-monospace,monospace;min-height:44px}
select.inp{cursor:pointer}
.frow{display:flex;gap:8px}
.frow>*{flex:1}
.lbl{font-size:11px;color:#8b949e;margin-bottom:3px}
.exec-btn{width:100%;padding:14px;border-radius:12px;border:none;font-weight:700;font-size:15px;cursor:pointer;margin-top:6px;min-height:50px}
.exec-btn.buy{background:#1a5c30;color:#3fb950}
.exec-btn.sell{background:#5c1a1a;color:#f85149}
.tbl{width:100%;border-collapse:collapse;font-size:12px}
.tbl th{text-align:left;color:#6e7681;padding:4px 4px 8px;font-weight:500;font-size:11px}
.tbl td{padding:6px 4px;border-bottom:1px solid #1c2128}
.badge{font-size:9px;font-weight:700;padding:2px 6px;border-radius:10px}
.badge-b{background:#1a5c30;color:#3fb950}
.badge-s{background:#5c1a1a;color:#f85149}
.badge-bull{background:#1a5c30;color:#3fb950;font-size:10px;padding:3px 8px;border-radius:10px;font-weight:600}
.badge-bear{background:#5c1a1a;color:#f85149;font-size:10px;padding:3px 8px;border-radius:10px;font-weight:600}
.metrics{display:grid;grid-template-columns:1fr 1fr;gap:8px;margin-top:8px}
.metric{background:#0d1117;border-radius:8px;padding:10px;text-align:center}
.m-lbl{font-size:10px;color:#6e7681;margin-bottom:4px}
.m-val{font-size:16px;font-weight:600;font-family:ui-monospace,monospace}
.strat-row{display:flex;gap:8px;align-items:center;flex-wrap:wrap}
.alert-item{padding:12px;border-bottom:1px solid #21262d;display:flex;justify-content:space-between;align-items:flex-start;gap:8px}
.alert-sym{font-weight:700;font-size:15px;margin-bottom:2px}
.alert-pat{font-size:11px;color:#8b949e}
.alert-time{font-size:10px;color:#6e7681;margin-top:3px}
.empty-state{text-align:center;padding:40px 20px;color:#6e7681;font-size:13px;line-height:1.7}
.notif-banner{background:#1a3a5c;border:1px solid #1d4e8c;border-radius:10px;padding:12px;display:flex;justify-content:space-between;align-items:center;margin-bottom:12px;gap:10px}
.notif-text{font-size:12px;color:#a5c8ff;line-height:1.5}
.notif-banner.hidden{display:none}
.scan-info{background:#161b22;border:1px solid #21262d;border-radius:10px;padding:12px;margin-bottom:12px;font-size:12px;color:#8b949e;line-height:1.7}
.scan-info strong{color:#e6edf3}
.scan-ticker-inp{width:100%;padding:10px 12px;border-radius:10px;font-size:12px;border:1px solid #30363d;background:#0d1117;color:#e6edf3;font-family:ui-monospace,monospace;min-height:44px;margin-bottom:8px}
.bt-grid{display:grid;grid-template-columns:1fr 1fr;gap:6px;margin:10px 0}
.bt-m{background:#0d1117;border-radius:8px;padding:8px;text-align:center}
.bt-l{font-size:10px;color:#6e7681;margin-bottom:2px}
.bt-v{font-size:14px;font-weight:600;font-family:ui-monospace,monospace}
.two-charts{display:grid;grid-template-columns:1fr 1fr;gap:8px}
.info-box{background:#161b22;border:1px solid #21262d;border-radius:10px;padding:12px;margin-bottom:12px}
.info-title{font-weight:600;font-size:13px;color:#58a6ff;margin-bottom:6px}
.info-text{font-size:12px;color:#8b949e;line-height:1.7}
code{background:#0d1117;padding:1px 5px;border-radius:4px;font-family:ui-monospace,monospace;color:#d29922;font-size:12px}
@media(max-width:500px){.bt-grid,.two-charts,.frow{grid-template-columns:1fr;flex-direction:column}}
</style>
</head>
<body>
<div id="toast"></div>

<header class="hdr">
  <div>
    <div class="brand">📊 ECC Trading <span style="font-size:10px;color:#3fb950;font-weight:400">● Cloud</span></div>
    <div style="font-size:10px;color:#6e7681">24/7 · real market scanner · mobile</div>
  </div>
  <div style="text-align:center">
    <div id="hdrVal" class="hdr-val">$10,000.00</div>
    <div id="hdrPnl" style="font-size:12px;font-weight:500">+$0.00 (+0.00%)</div>
  </div>
  <div style="display:flex;gap:8px">
    <button id="runBtn" class="btn btn-g" onclick="toggleRun()">▶ Start</button>
    <button class="btn btn-o" onclick="resetBot()" style="padding:8px 10px">↺</button>
    <span id="tickLbl" style="font-size:10px;color:#6e7681;align-self:center">t0</span>
  </div>
</header>

<!-- TRADING TAB -->
<div id="tab-trade" class="tab active">
  <div id="notifBanner" class="notif-banner">
    <div class="notif-text">🔔 Allow notifications to get alerts on your phone when patterns are found.</div>
    <button class="btn btn-b" onclick="askNotif()" style="white-space:nowrap;flex:0 0 auto;font-size:12px;padding:8px 12px;min-height:36px">Allow</button>
  </div>
  <div class="asset-row" id="assetRow"></div>
  <div class="card" style="padding:10px">
    <div style="display:flex;justify-content:space-between;margin-bottom:6px;align-items:center">
      <span id="cname" style="font-weight:600;font-size:13px">Bitcoin (BTC)</span>
      <div style="display:flex;gap:10px;font-size:12px">
        <span id="cprice" class="mono"></span><span id="crsi" class="mono muted"></span>
      </div>
    </div>
    <canvas id="priceChart" style="height:160px"></canvas>
  </div>
  <div class="card">
    <div class="ctitle">Place order</div>
    <div class="side-row">
      <button id="buyBtn" class="side-btn buy" onclick="setSide('BUY')">BUY</button>
      <button id="sellBtn" class="side-btn" onclick="setSide('SELL')">SELL</button>
    </div>
    <select id="oType" class="inp" onchange="updateOType()">
      <option value="MARKET">Market order</option>
      <option value="LIMIT">Limit order</option>
    </select>
    <div class="lbl">Quantity</div>
    <input id="qty" type="number" step="any" min="0" placeholder="0.0000" class="inp">
    <div id="limitRow" style="display:none"><div class="lbl">Limit price ($)</div>
      <input id="limitPx" type="number" step="any" min="0" placeholder="0.00" class="inp"></div>
    <div id="slTpRow" class="frow">
      <div><div class="lbl">Stop-loss ($)</div><input id="sl" type="number" step="any" placeholder="optional" class="inp"></div>
      <div><div class="lbl">Take-profit ($)</div><input id="tp" type="number" step="any" placeholder="optional" class="inp"></div>
    </div>
    <button id="execBtn" class="exec-btn buy" onclick="placeOrder()">Execute BUY</button>
    <div id="pendingInfo" style="font-size:11px;color:#d29922;margin-top:4px;min-height:14px"></div>
  </div>
  <div class="card" style="padding:10px">
    <div style="display:flex;justify-content:space-between;margin-bottom:6px">
      <span class="ctitle" style="margin:0">Portfolio</span>
      <span id="cashLeft" class="mono muted" style="font-size:11px"></span>
    </div>
    <canvas id="portChart" style="height:90px"></canvas>
  </div>
  <div class="card">
    <div class="ctitle">Positions</div>
    <table class="tbl"><thead><tr><th>Asset</th><th>Qty</th><th>Value</th><th>uPnL</th></tr></thead>
    <tbody id="posTbl"></tbody></table>
  </div>
  <div class="card">
    <div class="ctitle">Trade log</div>
    <table class="tbl"><thead><tr><th>Trade</th><th>Qty</th><th>Price</th><th>PnL</th></tr></thead>
    <tbody id="tradeTbl"></tbody></table>
  </div>
  <div class="card">
    <div class="ctitle">Auto-strategy</div>
    <div class="strat-row">
      <select id="stratType" class="inp" style="flex:1;min-height:44px" onchange="updateStratUI()">
        <option value="manual">Manual only</option>
        <option value="sma">SMA Crossover</option>
        <option value="rsi">RSI Mean Reversion</option>
      </select>
    </div>
    <div id="smaP" style="display:none;margin-top:8px" class="frow">
      <div><div class="lbl">Fast</div><input id="fast" type="number" min="2" max="50" class="inp" value="5"></div>
      <div><div class="lbl">Slow</div><input id="slow" type="number" min="3" max="100" class="inp" value="20"></div>
    </div>
    <div id="activeWrap" style="display:none;margin-top:10px;justify-content:space-between;align-items:center">
      <label style="display:flex;align-items:center;gap:6px;cursor:pointer;font-size:13px">
        <input type="checkbox" id="stratActive" style="width:18px;height:18px"> Active
      </label>
      <button onclick="applyStrat()" class="btn btn-o" style="padding:8px 14px">Apply</button>
    </div>
    <div id="stratHint" style="font-size:11px;color:#6e7681;margin-top:6px"></div>
  </div>
  <div class="metrics">
    <div class="metric"><div class="m-lbl">Win rate</div><div id="mWin" class="m-val">—</div></div>
    <div class="metric"><div class="m-lbl">Total trades</div><div id="mTrades" class="m-val">0</div></div>
    <div class="metric"><div class="m-lbl">Max drawdown</div><div id="mDD" class="m-val">0%</div></div>
    <div class="metric"><div class="m-lbl">Cash left</div><div id="mCash" class="m-val">—</div></div>
  </div>
  <div style="padding:12px 0;text-align:center">
    <button onclick="window.location='/api/export'" class="btn btn-o">↓ Export trades CSV</button>
  </div>
</div>

<!-- SCANNER TAB -->
<div id="tab-scan" class="tab">
  <div class="scan-info">
    <strong>Live scanner</strong> — reads real market data from Yahoo Finance.<br>
    Scans every 5 minutes · RSI Divergence + Trendline Breakout<br>
    Scanner status: <span id="scanStatusTxt">loading...</span>
    <span id="scanDot" class="rdot off"></span>
    <span id="nextIn" style="color:#6e7681;font-size:11px"></span>
  </div>
  <div class="card">
    <div class="ctitle">Watchlist</div>
    <textarea id="watchlistInput" class="scan-ticker-inp" rows="3"
      placeholder="BTC-USD, RELIANCE.NS, ^NSEI, EURUSD=X ...">BTC-USD,ETH-USD,RELIANCE.NS,TCS.NS,^NSEI,EURUSD=X,AAPL,TSLA</textarea>
    <div style="font-size:11px;color:#6e7681;margin-bottom:8px">
      Indian stocks: add .NS &nbsp;·&nbsp; Indices: ^NSEI, ^BSESN &nbsp;·&nbsp; Crypto: BTC-USD &nbsp;·&nbsp; Forex: EURUSD=X
    </div>
    <div class="frow">
      <div>
        <div class="lbl">Interval</div>
        <select id="scanInterval" class="inp">
          <option value="15m">15 min</option>
          <option value="1h">1 hour</option>
          <option value="1d" selected>Daily</option>
        </select>
      </div>
      <div>
        <div class="lbl">Period</div>
        <select id="scanPeriod" class="inp">
          <option value="3mo">3 months</option>
          <option value="6mo" selected>6 months</option>
          <option value="1y">1 year</option>
        </select>
      </div>
    </div>
  </div>
  <div class="card" style="padding:0;overflow:hidden">
    <div style="padding:12px;border-bottom:1px solid #21262d;display:flex;justify-content:space-between;align-items:center">
      <span style="font-weight:600;font-size:13px">Detected signals</span>
      <button onclick="clearAlerts()" class="btn btn-o" style="font-size:11px;padding:6px 10px;min-height:32px">Clear</button>
    </div>
    <div id="alertList"></div>
    <div id="noAlerts" class="empty-state">
      No signals yet.<br>Scanner checks every 5 minutes.<br>
      <span style="font-size:11px">Alerts will appear here and notify your phone automatically.</span>
    </div>
  </div>
</div>

<!-- BACKTEST TAB -->
<div id="tab-bt" class="tab">
  <div class="card">
    <div class="ctitle">Backtest settings</div>
    <div class="lbl">Asset</div>
    <select id="btAsset" class="inp">
      <option value="BTC">Bitcoin (BTC)</option>
      <option value="ETH">Ethereum (ETH)</option>
      <option value="AAPL">Apple (AAPL)</option>
      <option value="TSLA">Tesla (TSLA)</option>
    </select>
    <div class="lbl">Strategy</div>
    <select id="btStrat" class="inp">
      <option value="sma">SMA Crossover</option>
      <option value="rsi">RSI Mean Reversion</option>
    </select>
    <div class="frow">
      <div><div class="lbl">Fast SMA</div><input id="btFast" type="number" value="5" min="2" class="inp"></div>
      <div><div class="lbl">Slow SMA</div><input id="btSlow" type="number" value="20" min="3" class="inp"></div>
    </div>
    <div class="frow">
      <div><div class="lbl">Ticks</div><input id="btTicks" type="number" value="500" min="10" max="5000" class="inp"></div>
      <div><div class="lbl">Seed</div><input id="btSeed" type="number" placeholder="random" class="inp"></div>
    </div>
    <button id="btBtn" onclick="runBT()" class="btn btn-b" style="width:100%;min-height:50px;font-size:15px;border-radius:12px;margin-top:4px">⚡ Run Backtest</button>
  </div>
  <div id="btResults" style="display:none">
    <div class="bt-grid">
      <div class="bt-m"><div class="bt-l">Final value</div><div id="btFV" class="bt-v"></div></div>
      <div class="bt-m"><div class="bt-l">P&L</div><div id="btPnl" class="bt-v"></div></div>
      <div class="bt-m"><div class="bt-l">Max drawdown</div><div id="btDD" class="bt-v"></div></div>
      <div class="bt-m"><div class="bt-l">Win rate</div><div id="btWR" class="bt-v"></div></div>
    </div>
    <div class="two-charts">
      <div class="card" style="padding:8px"><canvas id="btPriceC" style="height:90px"></canvas></div>
      <div class="card" style="padding:8px"><canvas id="btPortC"  style="height:90px"></canvas></div>
    </div>
  </div>
</div>

<!-- HELP TAB -->
<div id="tab-help" class="tab">
  <div class="info-box">
    <div class="info-title">🔔 Keep the bot awake 24/7 (free)</div>
    <div class="info-text">
      Render's free tier pauses after 15 min of inactivity.<br>
      Use <strong>UptimeRobot</strong> (free) to ping it every 5 min:<br><br>
      1. Go to <code>uptimerobot.com</code> → Sign up free<br>
      2. New monitor → HTTP(S)<br>
      3. URL: <code>YOUR-RENDER-URL/health</code><br>
      4. Interval: 5 minutes<br>
      5. Add phone number for SMS alerts if down
    </div>
  </div>
  <div class="info-box">
    <div class="info-title">📱 Install as phone app</div>
    <div class="info-text">
      <strong>Android (Chrome):</strong><br>
      Open the site → tap ⋮ menu → "Add to Home screen"<br><br>
      <strong>iPhone (Safari):</strong><br>
      Open the site → tap Share button → "Add to Home Screen"<br><br>
      The app icon will appear on your home screen like a native app.
    </div>
  </div>
  <div class="info-box">
    <div class="info-title">📡 Scanner ticker formats</div>
    <div class="info-text">
      Indian stocks: <code>RELIANCE.NS</code> <code>TCS.NS</code> <code>HDFCBANK.NS</code><br>
      Indian indices: <code>^NSEI</code> <code>^BSESN</code> <code>^NSEBANK</code><br>
      Crypto: <code>BTC-USD</code> <code>ETH-USD</code> <code>SOL-USD</code><br>
      Forex: <code>EURUSD=X</code> <code>USDINR=X</code><br>
      US stocks: <code>AAPL</code> <code>TSLA</code> <code>NVDA</code>
    </div>
  </div>
  <div class="info-box">
    <div class="info-title">📨 Telegram alerts (optional)</div>
    <div class="info-text">
      Get signal alerts on Telegram even when browser is closed.<br><br>
      1. Open Telegram → search <code>@BotFather</code> → send <code>/newbot</code><br>
      2. Follow steps → copy the <strong>Bot Token</strong><br>
      3. Search <code>@userinfobot</code> → send any message → copy your <strong>Chat ID</strong><br>
      4. On Render → your service → <strong>Environment</strong> tab → add:<br>
      &nbsp;&nbsp;<code>BOT_TOKEN</code> = your token<br>
      &nbsp;&nbsp;<code>CHAT_ID</code> = your chat id<br>
      5. Redeploy → tap Test button below
    </div>
    <button onclick="testTelegram()" class="btn btn-b" style="margin-top:10px;width:100%;min-height:44px">
      📨 Send Test Telegram Message
    </button>
    <div id="tgResult" style="font-size:12px;color:#8b949e;margin-top:6px"></div>
  </div>

  <div class="info-box">
    <div class="info-title">⚠️ Disclaimer</div>
    <div class="info-text">
      Paper Trading uses simulated prices only — not real markets.<br>
      Scanner shows historical patterns, not future predictions.<br>
      Nothing here is financial advice.<br>
      Do not trade real money based on this app alone.
    </div>
  </div>
</div>

<nav class="bnav">
  <button class="bnav-btn active" id="bnTrade" onclick="showTab('trade',this)">
    <svg viewBox="0 0 24 24"><polyline points="22 12 18 12 15 21 9 3 6 12 2 12"/></svg>
    Trading
  </button>
  <button class="bnav-btn" id="bnScan" onclick="showTab('scan',this)">
    <svg viewBox="0 0 24 24"><path d="M18 8A6 6 0 0 0 6 8c0 7-3 9-3 9h18s-3-2-3-9"/><path d="M13.73 21a2 2 0 0 1-3.46 0"/></svg>
    Alerts
    <span class="rdot off" id="alertDot"></span>
  </button>
  <button class="bnav-btn" id="bnBT" onclick="showTab('bt',this)">
    <svg viewBox="0 0 24 24"><polyline points="23 6 13.5 15.5 8.5 10.5 1 18"/><polyline points="17 6 23 6 23 12"/></svg>
    Backtest
  </button>
  <button class="bnav-btn" id="bnHelp" onclick="showTab('help',this)">
    <svg viewBox="0 0 24 24"><circle cx="12" cy="12" r="10"/><path d="M9.09 9a3 3 0 0 1 5.83 1c0 2-3 3-3 3"/><line x1="12" y1="17" x2="12.01" y2="17"/></svg>
    Help
  </button>
</nav>

<script>
const COLORS={BTC:'#f0883e',ETH:'#a371f7',AAPL:'#3fb950',TSLA:'#f85149'};
let tickTimer=null,selAsset='BTC',lastState=null,currentSide='BUY';

function showTab(id,btn){
  document.querySelectorAll('.tab').forEach(t=>t.classList.remove('active'));
  document.querySelectorAll('.bnav-btn').forEach(b=>b.classList.remove('active'));
  document.getElementById('tab-'+id).classList.add('active');
  btn.classList.add('active');
  if(id==='scan'){loadAlerts();pollScanStatus();}
}

function fm(v){if(v==null||isNaN(v))return'—';const s=v<0?'-':'',a=Math.abs(v);return s+'$'+(a>=10000?(a/1000).toFixed(2)+'k':a.toFixed(2));}
function fp(v){return v==null?'—':(v>=0?'+':'')+v.toFixed(2)+'%';}
function fa(v){return Math.abs(v)>=10000?(v/1000).toFixed(1)+'k':Math.abs(v)>=1?v.toFixed(0):v.toFixed(2);}

let toastT=null;
function toast(msg,cls='ok'){
  const el=document.getElementById('toast');
  el.textContent=msg;el.className='show '+cls;
  clearTimeout(toastT);toastT=setTimeout(()=>el.className='',3000);
}

async function api(path,method,body){
  const opts={method:method||'GET',headers:{}};
  if(body){opts.headers['Content-Type']='application/json';opts.body=JSON.stringify(body);}
  const res=await fetch(path,opts);
  let d;try{d=await res.json();}catch(e){d={};}
  if(!res.ok||d.ok===false)throw new Error(d.error||'Error '+res.status);
  return d;
}

function drawChart(id,series,h){
  const c=document.getElementById(id);if(!c)return;
  const dpr=window.devicePixelRatio||1,cw=c.clientWidth,ch=h||c.clientHeight;
  c.style.height=ch+'px';c.width=Math.round(cw*dpr);c.height=Math.round(ch*dpr);
  const ctx=c.getContext('2d');ctx.setTransform(dpr,0,0,dpr,0,0);ctx.clearRect(0,0,cw,ch);
  let all=[];series.forEach(s=>s.data.forEach(v=>{if(v!=null&&isFinite(v))all.push(v);}));
  if(all.length<2)return;
  let mn=Math.min(...all),mx=Math.max(...all);
  if(mn===mx){mn-=1;mx+=1;}
  const pad=(mx-mn)*0.08;mn-=pad;mx+=pad;
  const lp=40,rp=4,tp=4,bp=4,pw=cw-lp-rp,ph=ch-tp-bp;
  ctx.strokeStyle='#21262d';ctx.fillStyle='#6e7681';ctx.font='9px ui-monospace,monospace';ctx.lineWidth=0.5;
  for(let i=0;i<=2;i++){const y=tp+ph*i/2,val=mx-(mx-mn)*i/2;ctx.beginPath();ctx.moveTo(lp,y);ctx.lineTo(cw-rp,y);ctx.stroke();ctx.fillText('$'+fa(val),2,y+3);}
  series.forEach(s=>{
    const n=s.data.length;if(n<2)return;
    ctx.beginPath();ctx.strokeStyle=s.color;ctx.lineWidth=s.w||1.5;ctx.setLineDash(s.dash||[]);
    let started=false,fx=null,lx=lp;
    s.data.forEach((v,i)=>{
      const x=lp+pw*(i/(n-1));lx=x;
      if(v==null||!isFinite(v)){started=false;return;}
      if(fx===null)fx=x;
      const y=tp+ph*(1-(v-mn)/(mx-mn));
      if(!started){ctx.moveTo(x,y);started=true;}else ctx.lineTo(x,y);
    });
    ctx.stroke();ctx.setLineDash([]);
    if(s.fill&&fx!==null){ctx.lineTo(lx,tp+ph);ctx.lineTo(fx,tp+ph);ctx.closePath();ctx.fillStyle=s.color+'18';ctx.fill();}
  });
}

function askNotif(){
  if(!('Notification' in window)){toast('Not supported in this browser','err');return;}
  Notification.requestPermission().then(p=>{
    if(p==='granted'){
      document.getElementById('notifBanner').classList.add('hidden');
      toast('Notifications enabled ✓');
      new Notification('ECC Trading',{body:'Notifications are ON. You will be alerted when setups are found!'});
    }else{toast('Denied — enable in browser settings','err');}
  });
}
if(typeof Notification!=='undefined'&&Notification.permission==='granted')
  document.getElementById('notifBanner').classList.add('hidden');

function fireNotif(a){
  if(Notification.permission!=='granted')return;
  const bull=a.direction.includes('BULL');
  new Notification(`${bull?'🟢':'🔴'} ${a.asset} — ${a.pattern}`,{
    body:`${a.direction}\nPrice: $${a.price}\nTime: ${a.time}`,
    tag:a.asset+'_'+a.pattern,renotify:true
  });
}

function connectSSE(){
  const es=new EventSource('/api/events');
  es.onmessage=e=>{
    const a=JSON.parse(e.data);
    fireNotif(a);addAlert(a);
    document.getElementById('alertDot').className='rdot green';
    toast(`🔔 ${a.asset}: ${a.pattern} (${a.direction})`,'alert');
  };
  es.onerror=()=>{setTimeout(connectSSE,5000);es.close();};
}
connectSSE();

function addAlert(a){
  const list=document.getElementById('alertList');
  document.getElementById('noAlerts').style.display='none';
  const bull=a.direction.includes('BULL');
  const div=document.createElement('div');div.className='alert-item';
  div.innerHTML=`<div><div class="alert-sym">${a.asset}</div><div class="alert-pat">${a.pattern}</div><div class="alert-time">${a.time} · $${a.price}</div></div><span class="${bull?'badge-bull':'badge-bear'}">${a.direction}</span>`;
  list.insertBefore(div,list.firstChild);
  if(list.children.length>50)list.lastChild.remove();
}

async function loadAlerts(){
  try{
    const d=await api('/api/alerts');
    if(d.alerts&&d.alerts.length){
      document.getElementById('noAlerts').style.display='none';
      d.alerts.slice().reverse().forEach(addAlert);
    }
  }catch(e){}
}

function clearAlerts(){
  document.getElementById('alertList').innerHTML='';
  document.getElementById('noAlerts').style.display='block';
  document.getElementById('alertDot').className='rdot off';
}

async function pollScanStatus(){
  try{
    const d=await api('/api/scan/status');
    const s=d.status;
    const dot=document.getElementById('scanDot');
    const txt=document.getElementById('scanStatusTxt');
    const ni=document.getElementById('nextIn');
    if(!d.has_yf){
      txt.textContent='yfinance not installed (cloud only)';
      dot.className='rdot amber';
    }else if(s.running){
      txt.textContent='scanning...';dot.className='rdot green';
    }else{
      txt.textContent=`last: ${s.last}`;dot.className='rdot off';
      ni.textContent=` · next in ${Math.round(s.next_in/60)} min`;
    }
  }catch(e){}
}
setInterval(pollScanStatus,10000);

function setSide(s){
  currentSide=s;
  document.getElementById('buyBtn').className='side-btn'+(s==='BUY'?' buy':'');
  document.getElementById('sellBtn').className='side-btn'+(s==='SELL'?' sell':'');
  document.getElementById('execBtn').className='exec-btn '+(s==='BUY'?'buy':'sell');
  document.getElementById('execBtn').textContent='Execute '+s;
  document.getElementById('slTpRow').style.display=s==='BUY'?'flex':'none';
}
setSide('BUY');

function updateOType(){
  document.getElementById('limitRow').style.display=
    document.getElementById('oType').value==='LIMIT'?'block':'none';
}

function updateStratUI(){
  const t=document.getElementById('stratType').value;
  document.getElementById('smaP').style.display=t==='sma'?'flex':'none';
  document.getElementById('activeWrap').style.display=t==='manual'?'none':'flex';
  document.getElementById('stratHint').textContent=
    t==='sma'?'Golden cross = BUY · Death cross = SELL':
    t==='rsi'?'RSI < 30 = BUY · RSI > 70 = SELL':'Place orders manually.';
}
updateStratUI();

async function applyStrat(){
  try{
    const d=await api('/api/strategy','POST',{
      type:document.getElementById('stratType').value,
      fast:parseInt(document.getElementById('fast').value),
      slow:parseInt(document.getElementById('slow').value),
      active:document.getElementById('stratActive').checked,
    });
    lastState=d.state;render(d.state);toast('Strategy updated');
  }catch(e){toast(e.message,'err');}
}

async function placeOrder(){
  const qty=parseFloat(document.getElementById('qty').value);
  if(!qty||qty<=0){toast('Enter a valid quantity','err');return;}
  const otype=document.getElementById('oType').value;
  const body={asset:selAsset,side:currentSide,order_type:otype,qty};
  if(currentSide==='BUY'){body.sl=document.getElementById('sl').value||null;body.tp=document.getElementById('tp').value||null;}
  if(otype==='LIMIT'){body.limit_price=document.getElementById('limitPx').value||null;}
  try{
    const d=await api('/api/order','POST',body);
    lastState=d.state;render(d.state);toast(d.message);
    ['qty','sl','tp','limitPx'].forEach(id=>{const el=document.getElementById(id);if(el)el.value='';});
  }catch(e){toast(e.message,'err');}
}

async function refresh(){try{const d=await api('/api/state');lastState=d.state;render(d.state);}catch(e){}}
async function doTick(){try{const d=await api('/api/tick','POST');lastState=d.state;render(d.state);}catch(e){toast(e.message,'err');stopRun();}}
function startRun(){if(tickTimer)return;tickTimer=setInterval(doTick,900);const b=document.getElementById('runBtn');b.textContent='⏸ Pause';b.className='btn btn-a';}
function stopRun(){clearInterval(tickTimer);tickTimer=null;const b=document.getElementById('runBtn');b.textContent='▶ Start';b.className='btn btn-g';}
function toggleRun(){tickTimer?stopRun():startRun();}
async function resetBot(){stopRun();try{const d=await api('/api/reset','POST');lastState=d.state;render(d.state);toast('Reset');}catch(e){toast(e.message,'err');}}

function render(s){
  document.getElementById('tickLbl').textContent='t'+s.tick;
  document.getElementById('hdrVal').textContent=fm(s.tv);
  const pe=document.getElementById('hdrPnl');pe.textContent=fm(s.pnl)+' ('+fp(s.pnl_pct)+')';pe.style.color=s.pnl>=0?'#3fb950':'#f85149';
  const row=document.getElementById('assetRow');row.innerHTML='';
  Object.keys(s.assets).forEach(a=>{
    const pts=s.charts[a],pr=s.prices[a],chg=pts.length?((pr-pts[0].p)/pts[0].p*100):0;
    const d=document.createElement('div');d.className='asset-chip'+(a===selAsset?' sel':'');
    d.style.borderColor=a===selAsset?COLORS[a]:'#21262d';
    d.innerHTML=`<div class="chip-sym">${a}</div><div class="chip-price">${fm(pr)}</div><div style="font-size:10px" class="${chg>=0?'pos':'neg'}">${fp(chg)}</div>`;
    d.onclick=()=>{selAsset=a;if(lastState)render(lastState);};row.appendChild(d);
  });
  const pts=s.charts[selAsset];
  const series=[{data:pts.map(p=>p.p),color:COLORS[selAsset],w:1.8,fill:true}];
  if(s.strat.type==='sma'){series.push({data:pts.map(p=>p.f),color:'#d29922',w:1,dash:[4,3]});series.push({data:pts.map(p=>p.s),color:'#a371f7',w:1});}
  drawChart('priceChart',series,160);
  document.getElementById('cname').textContent=s.assets[selAsset].name+' ('+selAsset+')';
  document.getElementById('cprice').textContent=fm(s.prices[selAsset]);
  const lr=pts.length?pts[pts.length-1].r:50;
  const re=document.getElementById('crsi');re.textContent='RSI '+lr.toFixed(0);re.style.color=lr<30?'#3fb950':lr>70?'#f85149':'#8b949e';
  drawChart('portChart',[{data:s.pv_hist,color:s.pnl>=0?'#3fb950':'#f85149',w:1.5,fill:true}],90);
  document.getElementById('cashLeft').textContent='Cash: '+fm(s.cash);
  const pb=document.getElementById('posTbl');pb.innerHTML='';
  Object.entries(s.pos).forEach(([a,p])=>{
    const tr=document.createElement('tr');tr.style.opacity=p.qty>0?'1':'0.4';
    tr.innerHTML=`<td>${a}</td><td class="mono">${p.qty.toFixed(4)}</td><td>${fm(p.mv)}</td><td class="${p.upnl>=0?'pos':'neg'}">${fm(p.upnl)}</td>`;
    pb.appendChild(tr);
  });
  const tb=document.getElementById('tradeTbl');tb.innerHTML='';
  if(!s.trades.length){tb.innerHTML='<tr><td colspan="4" style="color:#6e7681;padding:8px">No trades yet — click ▶ Start</td></tr>';}
  else s.trades.slice(0,10).forEach(t=>{
    const tr=document.createElement('tr');
    const via=t.via!=='MARKET'?`<span style="font-size:9px;color:#6e7681"> ${t.via}</span>`:'';
    tr.innerHTML=`<td><span class="badge ${t.side==='BUY'?'badge-b':'badge-s'}">${t.side}</span> ${t.asset}${via}</td><td class="mono">${t.qty.toFixed(4)}</td><td>${fm(t.price)}</td><td class="${(t.pnl||0)>=0?'pos':'neg'}">${t.pnl!=null?fm(t.pnl):'—'}</td>`;
    tb.appendChild(tr);
  });
  document.getElementById('pendingInfo').textContent=s.pending.length?s.pending.length+' pending limit order(s)':'';
  document.getElementById('mWin').textContent=s.wr!=null?s.wr+'%':'—';
  document.getElementById('mTrades').textContent=s.trades.length;
  document.getElementById('mDD').textContent=s.dd_pct.toFixed(2)+'%';
  document.getElementById('mCash').textContent=fm(s.cash);
  const af=document.activeElement?document.activeElement.id:'';
  if(!['fast','slow'].includes(af)){
    document.getElementById('stratType').value=s.strat.type;
    document.getElementById('fast').value=s.strat.fast;
    document.getElementById('slow').value=s.strat.slow;
    document.getElementById('stratActive').checked=s.strat.active;
    updateStratUI();
  }
}

async function runBT(){
  const btn=document.getElementById('btBtn');btn.disabled=true;btn.textContent='Running...';
  try{
    const d=await api('/api/backtest','POST',{
      asset:document.getElementById('btAsset').value,strat:document.getElementById('btStrat').value,
      fast:parseInt(document.getElementById('btFast').value),slow:parseInt(document.getElementById('btSlow').value),
      nt:parseInt(document.getElementById('btTicks').value),seed:document.getElementById('btSeed').value||null,
    });
    const r=d.result;document.getElementById('btResults').style.display='block';
    document.getElementById('btFV').textContent=fm(r.fv);
    const pe=document.getElementById('btPnl');pe.textContent=fp(r.pnl_pct);pe.className='bt-v '+(r.pnl>=0?'pos':'neg');
    document.getElementById('btDD').textContent=r.dd_pct.toFixed(2)+'%';
    document.getElementById('btWR').textContent=r.wr!=null?r.wr+'%':'—';
    drawChart('btPriceC',[{data:r.ph,color:COLORS[r.asset]||'#58a6ff',w:1.5,fill:true}],90);
    drawChart('btPortC',[{data:r.pvh,color:r.pnl>=0?'#3fb950':'#f85149',w:1.5,fill:true}],90);
  }catch(e){toast(e.message,'err');}
  btn.disabled=false;btn.textContent='⚡ Run Backtest';
}

async function testTelegram(){
  const el=document.getElementById('tgResult');
  el.textContent='Sending...';el.style.color='#8b949e';
  try{
    const d=await api('/api/telegram/test','POST',{});
    el.textContent='✅ '+d.message;el.style.color='#3fb950';
  }catch(e){
    el.textContent='❌ '+e.message;el.style.color='#f85149';
  }
}

refresh();
window.addEventListener('resize',()=>{if(lastState)render(lastState);});
</script>
</body></html>"""

# ─────────────────────────────────────────────────────────────────────────────
# SELF-TEST
# ─────────────────────────────────────────────────────────────────────────────

def selftest():
    print("Running self-tests...")
    for _ in range(10): assert gbm(100,.0001,.02)>0
    print("  [ok] gbm()")
    assert sma([1,2,3,4,5],5)==3.0 and sma([],1) is None
    print("  [ok] sma()")
    assert rsi_val([float(i) for i in range(1,20)])==100.0
    print("  [ok] rsi_val()")
    assert maxdd([])==0.0 and abs(maxdd([100,50,100])-.5)<1e-9
    print("  [ok] maxdd()")
    s=mk_state()
    ok,_=exec_order(s,"BTC","BUY",.01); assert ok
    ok,_=exec_order(s,"BTC","SELL",.01); assert ok
    ok,_=exec_order(s,"BTC","SELL",999); assert not ok
    print("  [ok] exec_order()")
    b=s["tick"]; do_tick(s); assert s["tick"]==b+1
    print("  [ok] do_tick()")
    r1=backtest("BTC","sma",5,20,100,seed=42)
    r2=backtest("BTC","sma",5,20,100,seed=42)
    assert r1["fv"]==r2["fv"]
    print("  [ok] backtest() (reproducible)")
    print("\nAll self-tests passed ✓")

# ─────────────────────────────────────────────────────────────────────────────
# ENTRY POINT
# ─────────────────────────────────────────────────────────────────────────────

def main():
    import sys
    if "--selftest" in sys.argv:
        selftest(); return

    # Start background market scanner
    watchlist = DEFAULT_WATCHLIST
    t = threading.Thread(
        target=background_scanner, args=(watchlist,), daemon=True)
    t.start()

    print("=" * 50)
    print("  ECC Trading Suite — Cloud Edition")
    print(f"  Running on port {PORT}")
    print("  Scanner started — real data every 5 min")
    print("=" * 50)

    # Use Flask dev server (Render will use gunicorn automatically)
    app.run(host="0.0.0.0", port=PORT, debug=False, threaded=True)

if __name__ == "__main__":
    main()
