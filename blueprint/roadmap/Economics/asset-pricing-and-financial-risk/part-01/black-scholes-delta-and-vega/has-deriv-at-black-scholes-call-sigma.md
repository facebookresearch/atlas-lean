# Vega is the volatility derivative of the call price

Vega: the derivative of the Black-Scholes call price with
respect to `σ` is `S0 φ(d₁) √T`. Chain rule: `d₂ = d₁ - σ √T`, so its
`σ`-derivative is the `d₁`-derivative minus `√T`; the density terms cancel
by the density identity `S0 φ(d₁) = K e^{-rT} φ(d₂)`, leaving `K e^{-rT} φ(d₂) √T = S0 φ(d₁) √T`.
