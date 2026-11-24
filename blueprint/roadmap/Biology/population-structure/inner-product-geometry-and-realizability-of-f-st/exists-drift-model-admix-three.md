# Drift model realizing a symmetric zero-diagonal 3×3 CND matrix

Let `D` be a symmetric real matrix with zero diagonal on three populations `0, 1, 2`,
[conditionally negative semidefinite](is-cond-neg-semidef.md) (CND), with `D 0 2 ≤ D 0 1` and
`D 1 2 ≤ D 0 1`. Then there are `0 ≤ α ≤ 1` and `a, b, c ≥ 0` with `a + b = D 0 1` (and, when
`D 0 1 > 0`, `1 - α = (D 0 1 + D 0 2 - D 1 2) / (2 * D 0 1)` and `c = D 0 2 - (1 - α) ^ 2 * D 0 1`),
and a [drift model](../patterson-s-f-statistics/drift-model.md) on a probability space with three
edges, the
[admixture lineage weights](../centred-population-covariance-and-f-statistics/admix-weight.md) for
`α` and drift lengths `(a, b, c)`, whose [f2 statistics](../patterson-s-f-statistics/f2.md) are
`f2(X, Y) = D X Y` for all populations `X, Y`. So `D` is [realizable](is-f2-realizable.md) by an
admixture graph in which population `2` is the `α : 1 - α` mixture of populations `0` and `1`
followed by drift on its private edge. The ordering hypothesis holds once the populations are
relabelled so that the largest off-diagonal entry is `D 0 1`.
