# An optimal LP point decodes to a cost below every feasible dispatch

Consider a network with finitely many buses `v` and branches `e` (each with a tail and a head bus
and a real susceptance `b_e`), finitely many generators `g` placed at buses, a demand `d`, a
reference bus `r`, generator limits `p_min`, `p_max` and branch-flow limits `f_min`, `f_max`, and
cost coefficients `c`. Let `x` be a feasible point of the [dispatch linear program](lp-matrix.md): a
vector `x ≥ 0` with `A x ≤ rhs` for the [constraint matrix](lp-matrix.md) `A` and the
[right-hand side](lp-rhs.md). Suppose that `x` maximizes the [LP objective](lp-objective.md) over
all feasible points. Then the [cost](dispatch-cost.md) of its
[decoded generation](decode-generation.md) is at most the cost of every
[feasible dispatch](is-dispatch-feasible.md). The decoded dispatch is itself feasible
([decoding](decode-feasible.md)), so it is a minimum-cost dispatch.
