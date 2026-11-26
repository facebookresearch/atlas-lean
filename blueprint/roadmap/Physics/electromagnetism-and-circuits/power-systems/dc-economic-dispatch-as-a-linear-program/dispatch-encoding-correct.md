# The DC dispatch problem and its linear program correspond

Consider a network with finitely many buses `v` and branches `e` (each with a tail and a head bus
and a real susceptance `b_e`), finitely many generators `g` placed at buses, a demand `d`, a
reference bus `r`, generator limits `p_min`, `p_max` and branch-flow limits `f_min`, `f_max`, and
cost coefficients `c`. Then:

- for every [feasible dispatch](is-dispatch-feasible.md) `(p, θ)`, the [encoded point](encode.md)
  `x = (max(z, 0), max(-z, 0))` of `z = (p, θ)` is nonnegative and satisfies `A x ≤ rhs`, it decodes
  to `(p, θ)`, and the [LP objective](lp-objective.md) at it is `-c · p`;
- for every LP point `x ≥ 0` with `A x ≤ rhs`, its decoded generation and angles form a feasible
  dispatch, and the LP objective at `x` is minus the cost of its decoded generation.

Here `A` is the [LP constraint matrix](lp-matrix.md) and `rhs` the [right-hand side](lp-rhs.md); the
minimized cost becomes the maximized objective. No positivity of the susceptances and no ordering of
the bounds is assumed; inconsistent data make both problems infeasible.
