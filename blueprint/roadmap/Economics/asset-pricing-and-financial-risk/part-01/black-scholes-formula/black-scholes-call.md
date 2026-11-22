# Black Scholes Call

The Black-Scholes price of a European call with strike `K` and maturity `T`:
`S0 Φ(d₁) - K e^{-rT} Φ(d₂)`, with `Φ = cdf (gaussianReal 0 1)` the standard normal cdf.
