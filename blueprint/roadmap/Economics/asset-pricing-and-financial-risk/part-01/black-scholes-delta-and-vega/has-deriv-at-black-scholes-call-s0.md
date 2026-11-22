# The spot derivative of the Black–Scholes call price is Φ(d₁)

For `S0, K, σ, T > 0` and any real `r`, the Black–Scholes call price as a function of the spot,
`C(S) = S Φ(d₁(S)) - K e^{-rT} Φ(d₂(S))`, has derivative `Φ(d₁(S0))` at `S0`, where `Φ` is the
standard normal cdf, `d₁(S) = (log (S / K) + (r + σ²/2) T) / (σ √T)` and `d₂(S) = d₁(S) - σ √T`.
By the chain rule through `d₁` and `d₂`, which have the same derivative `1 / (S σ √T)`, the
density terms cancel by the identity `S0 φ(d₁) = K e^{-rT} φ(d₂)`, where `φ` is the standard
normal density.
