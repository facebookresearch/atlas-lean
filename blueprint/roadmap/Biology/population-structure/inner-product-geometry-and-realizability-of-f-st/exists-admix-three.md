# Admixture fit of a symmetric zero-diagonal 3×3 CND matrix

Let `D` be a symmetric real matrix with zero diagonal on three populations `0, 1, 2`,
[conditionally negative semidefinite](is-cond-neg-semidef.md) (CND), with `D 0 1` at least the other two
off-diagonal entries: `D 0 2 ≤ D 0 1` and `D 1 2 ≤ D 0 1`. Then there are an admixture proportion
`0 ≤ α ≤ 1` and edge lengths `a, b, c ≥ 0` with `a + b = D 0 1` such that
`D X Y = ∑ e, (w X e - w Y e) ^ 2 * ℓ e` for all `X, Y`, where `w` are the
[admixture lineage weights](../centred-population-covariance-and-f-statistics/admix-weight.md) for
`α` (population `2` is the `α : 1 - α` mixture of populations `0` and `1` followed by drift on its
private edge) and `ℓ = (a, b, c)`. This is the
[f2 formula of the drift model](../patterson-s-f-statistics/f2-freq.md); explicitly,
`D 0 1 = a + b`, `D 0 2 = (1 - α) ^ 2 * (a + b) + c` and `D 1 2 = α ^ 2 * (a + b) + c`. When
`D 0 1 > 0`, `1 - α = (D 0 1 + D 0 2 - D 1 2) / (2 * D 0 1)` and `c = D 0 2 - (1 - α) ^ 2 * D 0 1`;
the lengths `a` and `b` enter only through `a + b`. Every symmetric zero-diagonal conditionally
negative semidefinite matrix on three populations satisfies the ordering hypothesis once the
populations are relabelled so that its largest off-diagonal entry is `D 0 1`.
