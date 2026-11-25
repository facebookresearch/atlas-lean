# Stable policy iterations converge to the fixed point

If `a ≠ d`, `|a| < 1` and `|d| < 1`, the affine policy iteration
`x(0) = x0`, `x(n + 1) = A x(n) + c` with `A = [[a, b], [0, d]]` converges, from any
starting state `x0` and for every `c = (c₁, c₂)`, to the fixed point
`x* = ((c₁ + b * c₂ / (1 - d)) / (1 - a), c₂ / (1 - d))`.
