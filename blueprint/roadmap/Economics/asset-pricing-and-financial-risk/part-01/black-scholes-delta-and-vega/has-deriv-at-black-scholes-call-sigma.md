# The volatility derivative of the Black–Scholes call is S0 φ(d₁) √T

For `S0, K, σ, T > 0` and any real `r`, the Black–Scholes call price as a function of the
volatility, `C(s) = S0 Φ(d₁(s)) - K e^{-rT} Φ(d₂(s))`, has derivative `S0 φ(d₁(σ)) √T` at `σ`,
where `Φ` and `φ` are the standard normal cdf and density,
`d₁(s) = (log (S0 / K) + (r + s²/2) T) / (s √T)` and `d₂(s) = d₁(s) - s √T`. By the chain rule
the derivative of `d₂` is that of `d₁` minus `√T`, and the density terms cancel by the identity
`S0 φ(d₁) = K e^{-rT} φ(d₂)`, leaving `K e^{-rT} φ(d₂) √T = S0 φ(d₁) √T`.
