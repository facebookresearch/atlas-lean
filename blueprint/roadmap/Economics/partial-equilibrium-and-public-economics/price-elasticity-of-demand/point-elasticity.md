# Point Elasticity

The point price elasticity formula `ε(p) = p q'(p) / q(p)` for a demand curve `q` at price
`p`, as a total function. It is the economic (percentage) elasticity when `p > 0`, `q p > 0` and
`q` is differentiable at `p`. If `q` is not differentiable at `p` or `q p = 0`, the total
`deriv` and division may yield Mathlib's junk values.
