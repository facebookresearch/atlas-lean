# Bounds on the Black–Scholes put price

For `S0, K, σ, T > 0` and any real `r`, the Black–Scholes put price
`P = K e^{-rT} Φ(-d₂) - S0 Φ(-d₁)`, where `Φ` is the standard normal cdf,
`d₁ = (log (S0 / K) + (r + σ²/2) T) / (σ √T)` and `d₂ = d₁ - σ √T`, satisfies
`max(K e^{-rT} - S0, 0) ≤ P ≤ K e^{-rT}`. These bounds follow from put–call parity
`C - P = S0 - K e^{-rT}` and the bounds `max(S0 - K e^{-rT}, 0) ≤ C ≤ S0` on the call price
`C = S0 Φ(d₁) - K e^{-rT} Φ(d₂)`.
