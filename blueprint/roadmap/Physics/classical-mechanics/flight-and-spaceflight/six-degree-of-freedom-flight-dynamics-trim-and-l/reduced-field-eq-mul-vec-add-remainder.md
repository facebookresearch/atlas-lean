# The reduced field is its linear part plus the remainder

At every state `e = (x, z, θ, q) ∈ ℝ⁴`, the [reduced field](reduced-field.md) is the Jacobian part
plus the nonlinear remainder:

`f(e) = A e + (−x³, 0, 0, θ − sin θ)`,

with `A` the [longitudinal Jacobian](longitudinal-jacobian.md) and the second term the
[remainder](longitudinal-remainder.md) `N(e)`. The same identity holds on the Euclidean state space:
the coordinates of the [nonlinear reduced field](nonlinear-reduced-field.md) are those of the
[reduced linear plant](linear-reduced-field.md) plus `N(e)`.
