# Candidate fixed point of the affine policy iteration

For the policy model `x(t + 1) = A x(t) + c` with `A = [[a, b], [0, d]]` and
`c = (c₁, c₂)`, the candidate fixed point is
`x* = ((c₁ + b * c₂ / (1 - d)) / (1 - a), c₂ / (1 - d))`, solved from the triangular
system (with the convention `x / 0 = 0`). When `a ≠ 1` and `d ≠ 1` it satisfies
`x* = A x* + c`.
