# Black–Scholes delta of a call option

For real `S0`, `K`, `r`, `σ` and `T`, the Black–Scholes delta of a call is `Φ(d₁)`, where `Φ` is the
standard normal cdf and `d₁ = (log (S0 / K) + (r + σ²/2) T) / (σ √T)`. For `S0, K, σ, T > 0` it is
the sensitivity of the call price to the spot price `S0`. With the conventions `x / 0 = 0` and
`√T = 0` for `T ≤ 0`, it is `Φ(0) = 1/2` when `σ = 0` or `T ≤ 0`. When `S0 / K ≤ 0`,
[`d₁`](../black-scholes-formula/d1.md) uses the conventions `log 0 = 0` and `log x = log |x|`.
