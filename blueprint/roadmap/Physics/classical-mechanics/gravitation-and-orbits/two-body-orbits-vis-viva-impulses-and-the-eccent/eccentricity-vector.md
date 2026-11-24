# Eccentricity vector of a state

For a real `μ` and a state given by a position `x ∈ ℝ³` and a velocity `v ∈ ℝ³`, the eccentricity
vector is `e = (v × h) / μ − x / r`, with the specific angular momentum `h = x × v` (cross product)
and the [distance](radius.md) `r = √(x · x)`. Its intended domain is `μ > 0` and `r > 0`. With the
convention `1 / 0 = 0` it is `−x / r` when `μ = 0` and `r > 0`, and `0` at the collision point
`x = 0`.
