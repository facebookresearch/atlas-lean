# Black–Scholes price of a European put

For real `S0`, `K`, `r`, `σ` and `T`, the Black–Scholes price of a European put with spot `S0`,
strike `K`, interest rate `r`, volatility `σ` and maturity `T` is `K e^{-rT} Φ(-d₂) - S0 Φ(-d₁)`,
where `Φ` is the standard normal cdf, `d₁ = (log (S0 / K) + (r + σ²/2) T) / (σ √T)` and
`d₂ = d₁ - σ √T`. It is the usual price for `S0, K, σ, T > 0`. When `σ = 0` or `T ≤ 0`, the
conventions `x / 0 = 0` and `√T = 0` give `d₁ = d₂ = 0`, so the formula takes the value
`(K e^{-rT} - S0) / 2`. When `S0 / K ≤ 0`, [`d₁`](../black-scholes-formula/d1.md) uses the
conventions `log 0 = 0` and `log x = log |x|`.
