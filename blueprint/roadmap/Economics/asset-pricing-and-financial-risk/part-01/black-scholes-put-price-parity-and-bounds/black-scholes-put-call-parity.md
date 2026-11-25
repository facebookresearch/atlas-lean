# Put–call parity for Black–Scholes prices

For all real `S0`, `K`, `r`, `σ` and `T`, with no positivity assumed, the Black–Scholes call price
`C = S0 Φ(d₁) - K e^{-rT} Φ(d₂)` and put price `P = K e^{-rT} Φ(-d₂) - S0 Φ(-d₁)` satisfy
`C - P = S0 - K e^{-rT}`, where `Φ` is the standard normal cdf,
`d₁ = (log (S0 / K) + (r + σ²/2) T) / (σ √T)` and `d₂ = d₁ - σ √T` (read with `x / 0 = 0` and
`√T = 0` for `T ≤ 0`). The identity is algebra from the symmetry `Φ(-x) = 1 - Φ(x)`, whatever the
values of `d₁` and `d₂`.
