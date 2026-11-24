# Unicycle

No-lateral-velocity identity for the ideal unicycle. If a
planar trace satisfies the ideal unicycle equations
`x' = v * cos θ` and `y' = v * sin θ` at a point (as
`HasDerivAt` values), then the lateral velocity of the
trace vanishes:
`-sin θ * x' + cos θ * y' = 0` for the actual derivatives
`deriv x t` and `deriv y t`.
