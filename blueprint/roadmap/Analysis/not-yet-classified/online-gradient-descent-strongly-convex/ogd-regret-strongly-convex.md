# Ogd regret strongly convex

Regret of online gradient descent for `α`-strongly convex losses.

With step sizes `η t = 1 / (α * (t + 1))` and subgradients bounded by `G`,
the regret against any comparator fixed by the projection is at most
`(G ^ 2 / (2 * α)) * (1 + log T)`.

Indexing starts at `t = 0`, so the classical schedule `η t = 1 / (α * t)`
for `t = 1, .., T` appears here as `η t = 1 / (α * (t + 1))` for
`t = 0, .., T - 1`. The iterate sequence is not constructed here: any
sequence satisfying the projected-gradient update hypothesis `hupd` (whose
existence is elementary by recursion) enjoys the bound.

Only the comparator instance of strong convexity is assumed: no
strong-convexity inequality outside the comparator instance is assumed.
Feasible-set strong convexity supplies this hypothesis for feasible iterates
and comparator.

As `α → 0` both the step-size schedule and the regret bound blow up; there
is no claim at `α = 0` (the bound is infinite and the schedule undefined).
