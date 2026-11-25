# Iteration error is a matrix power times the initial error

Let `a ≠ 1` and `d ≠ 1`, and let `x(0) = x0`, `x(n + 1) = A x(n) + c` be the affine
policy iteration with `A = [[a, b], [0, d]]`. Then for every `n` the iteration error
is the matrix power applied to the initial error: `x(n) - x* = A ^ n (x0 - x*)`,
where `x* = ((c₁ + b * c₂ / (1 - d)) / (1 - a), c₂ / (1 - d))`.
