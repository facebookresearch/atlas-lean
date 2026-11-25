# Feasible dispatches encode to feasible LP points

Consider a network with finitely many buses `v` and branches `e` (each with a tail and a head bus
and a real susceptance `b_e`), finitely many generators `g` placed at buses, a demand `d`, a
reference bus `r`, generator limits `p_min`, `p_max` and branch-flow limits `f_min`, `f_max`. If
`(p, θ)` is a [feasible dispatch](is-dispatch-feasible.md), then the [encoded point](encode.md)
`x = (max(z, 0), max(-z, 0))` of `z = (p, θ)` is a feasible point of the
[dispatch linear program](lp-matrix.md): a vector `x ≥ 0` with `A x ≤ rhs` for the
[constraint matrix](lp-matrix.md) `A` and the [right-hand side](lp-rhs.md).
