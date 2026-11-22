# Has Deriv At black Scholes Call S0

Delta (FI17.T03): the derivative of the Black-Scholes call price with
respect to `S0` is `Φ(d₁)`. Chain rule through `d₁` and `d₂`: both have the
same `S0`-derivative `1 / (S0 σ √T)`, so the density terms cancel by the
identity above.
