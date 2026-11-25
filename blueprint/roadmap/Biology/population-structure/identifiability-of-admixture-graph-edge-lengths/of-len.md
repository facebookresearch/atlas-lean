# Drift model on the edge set with given weights and lengths

For a finite edge set `E`, a function `w(X, e)` of populations `X` and edges `e` (any real values)
and a length vector `ℓ` with `ℓ(e) ≥ 0` for every edge define a
[drift model](../patterson-s-f-statistics/drift-model.md) whose sample space is `E` itself, with
every subset measurable and the counting measure (which is not normalized: its total mass is the
number of edges). Its lineage weights are `w`, its drift lengths are `ℓ`, its root frequency is the
constant `1/2`, and the drift increment of edge `e` is `√(ℓ(e))` at the point `e` and `0` at every
other point. The increments of distinct edges have disjoint supports, so they are orthogonal in L²
(the integral of the product of two of them is `0`), and the increment of `e` has second moment
`ℓ(e)`. These integrals are against the counting measure, so they are expectations only when there
is a single edge.
