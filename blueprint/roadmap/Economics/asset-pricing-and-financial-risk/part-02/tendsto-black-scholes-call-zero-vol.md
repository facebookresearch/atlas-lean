# As σ → 0⁺ the Black–Scholes call price tends to max(S0 − K e⁻ʳᵀ, 0)

For `S0, K, T > 0` and any real interest rate `r`, the Black–Scholes call price
`C(σ) = S0 Φ(d₁) - K e^{-rT} Φ(d₂)`, where `Φ` is the standard normal cdf,
`d₁ = (log (S0 / K) + (r + σ²/2) T) / (σ √T)` and `d₂ = d₁ - σ √T`, tends to
`max(S0 - K e^{-rT}, 0)` as `σ` tends to `0` through positive values. The formula at `σ = 0`
differs in general: there the convention `x / 0 = 0` gives `d₁ = d₂ = 0` and the value
`(S0 - K e^{-rT}) / 2`.

Proof sketch, with `A = log (S0 / K) + r T`: if `A > 0`, both `d₁` and `d₂` tend to `+∞` and `Φ`
to `1`; if `A < 0`, both tend to `-∞` and `Φ` to `0`; if `A = 0`, both tend to `0` and `Φ` to
`Φ(0) = 1/2`, and `S0 = K e^{-rT}` makes the limit `0`.
