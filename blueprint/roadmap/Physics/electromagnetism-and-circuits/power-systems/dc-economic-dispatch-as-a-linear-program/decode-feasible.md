# Feasible LP points decode to feasible dispatches

Consider a network with finitely many buses `v` and branches `e` (each with a tail and a head bus
and a real susceptance `b_e`), finitely many generators `g` placed at buses, a demand `d`, a
reference bus `r`, generator limits `p_min`, `p_max` and branch-flow limits `f_min`, `f_max`. If `x`
is a feasible point of the [dispatch linear program](lp-matrix.md): a vector `x ≥ 0` with
`A x ≤ rhs` for the [constraint matrix](lp-matrix.md) `A` and the [right-hand side](lp-rhs.md), then
its [decoded generation](decode-generation.md) and [decoded angles](decode-angle.md) form a
[feasible dispatch](is-dispatch-feasible.md). No positivity of the susceptances and no ordering of
the bounds is assumed; inconsistent data make both problems infeasible.
