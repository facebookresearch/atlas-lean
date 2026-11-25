# Black–Scholes vega of a call option

For real `S0`, `K`, `r`, `σ` and `T`, the Black–Scholes vega of a call is `S0 φ(d₁) √T`, where `φ`
is the standard normal density and `d₁ = (log (S0 / K) + (r + σ²/2) T) / (σ √T)`. For
`S0, K, σ, T > 0` it is the sensitivity of the call price to the volatility `σ`. With the convention
`√T = 0` for `T ≤ 0`, it is `0` when `T ≤ 0`. When `σ = 0` and `T > 0`, the convention `x / 0 = 0`
gives `d₁ = 0`, so the formula takes the value `S0 φ(0) √T`. When `S0 / K ≤ 0`,
[`d₁`](../black-scholes-formula/d1.md) uses the conventions `log 0 = 0` and `log x = log |x|`.
