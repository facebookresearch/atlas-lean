# Black–Scholes zero-volatility limit

Zero-volatility limit: as `σ → 0+`, the Black-Scholes call price
approaches the discounted deterministic-payoff limit `max (S0 - K e^{-rT}) 0`.
Case on the sign of `A = log (S0 / K) + r T`: if `A > 0`, both `d₁, d₂ → +∞`
and `Φ → 1`; if `A < 0`, both `→ -∞` and `Φ → 0`; if `A = 0`, both `→ 0`
and `Φ → Φ(0) = 1/2`, and `S0 = K e^{-rT}` makes the limit `0` in that case.
No positivity hypothesis on `r` is needed.
