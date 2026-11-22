# Black–Scholes price of a European put

The Black-Scholes price of a European put with strike `K` and maturity `T`:
`K e^{-rT} Φ(-d₂) - S0 Φ(-d₁)`, with `Φ = cdf (gaussianReal 0 1)`.
