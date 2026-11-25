# A minimum-cost dispatch encodes to an optimal LP point

Consider a network with finitely many buses `v` and branches `e` (each with a tail and a head bus
and a real susceptance `b_e`), finitely many generators `g` placed at buses, a demand `d`, a
reference bus `r`, generator limits `p_min`, `p_max` and branch-flow limits `f_min`, `f_max`, and
cost coefficients `c`. If `(p, θ)` is a [feasible dispatch](is-dispatch-feasible.md) whose
[cost](dispatch-cost.md) is at most that of every feasible dispatch, then the
[encoded point](encode.md) `x = (max(z, 0), max(-z, 0))` of `z = (p, θ)` is a feasible point of the
[dispatch linear program](lp-matrix.md): a vector `x ≥ 0` with `A x ≤ rhs` for the
[constraint matrix](lp-matrix.md) `A` and the [right-hand side](lp-rhs.md), and it maximizes the
[LP objective](lp-objective.md) over all such points.
