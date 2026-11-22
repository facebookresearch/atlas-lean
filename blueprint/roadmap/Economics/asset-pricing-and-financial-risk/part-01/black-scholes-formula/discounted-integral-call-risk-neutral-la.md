# Black–Scholes price as the discounted expected call payoff

For `S0, K, σ, T > 0` and any real interest rate `r`, let `Q` be the log-normal law of the
terminal price `S_T = S0 exp((r - σ²/2) T + σ √T Z)`, with `Z` standard normal. The discounted
expected payoff of a European call with strike `K` under `Q` is the Black–Scholes price:
`e^{-rT} ∫ max(x - K, 0) dQ(x) = S0 Φ(d₁) - K e^{-rT} Φ(d₂)`, where `Φ` is the standard normal
cdf, `d₁ = (log (S0 / K) + (r + σ²/2) T) / (σ √T)` and `d₂ = d₁ - σ √T`. This is an identity for
an expectation under an assumed law, not a continuous-time pricing argument.
