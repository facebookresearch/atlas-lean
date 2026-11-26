# The LP objective of an encoded dispatch is minus its cost

For cost coefficients `c`, every generation `p` and angles `θ`, the value of the
[LP objective](lp-objective.md) at the [encoded point](encode.md) `x = (max(z, 0), max(-z, 0))` of
`z = (p, θ)` is `-c · p`, minus the [dispatch cost](dispatch-cost.md).
