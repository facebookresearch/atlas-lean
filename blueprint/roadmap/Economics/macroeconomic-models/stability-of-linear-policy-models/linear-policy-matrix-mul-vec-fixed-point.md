# The explicit fixed point solves the policy recursion

If `a ≠ 1` and `d ≠ 1`, the point `x* = ((c₁ + b * c₂ / (1 - d)) / (1 - a), c₂ / (1 - d))`
satisfies `A x* + c = x*` for the policy matrix `A = [[a, b], [0, d]]` and every
`c = (c₁, c₂)`.
