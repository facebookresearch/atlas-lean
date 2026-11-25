# Bonferroni bound for the SKAT-O minimum p-value under the null

Let `X` be a real `n × q` covariate matrix and `V` a real `n × n` matrix such that `Xᵀ V⁻¹ X` is
invertible, where `V⁻¹` is the inverse of `V`, or `0` when `V` is singular. Let `G` be a real
`n × m` genotype matrix, `a ∈ ℝᵐ` variant weights, `α ∈ ℝ^q` and a nonempty finite grid of real
numbers `ρ`. Under the null model `y ~ N(X α, V)` the
[minimum SKAT-O p-value](skat-omin-p.md) satisfies, for every `t ∈ [0, 1]`,

`ℙ₀(min_{ρ ∈ grid} p_ρ(y) ≤ t) ≤ |grid| t`,

where `|grid|` is the number of grid points: the event is the union over the grid of the events
`{p_ρ ≤ t}`, each of probability at most `t` because each
[SKAT-O p-value is valid](is-valid-pvalue-skat-opvalue.md). The bound is informative only for
`t < 1 / |grid|`. Here `N(X α, V)` is the image of the standard Gaussian law on `ℝⁿ` under
`z ↦ X α + V^{1/2} z`: when `V` is positive semidefinite, `V^{1/2}` is its positive semidefinite
square root and `N(X α, V)` is the Gaussian law with mean `X α` and covariance `V`; for any other
`V`, `V^{1/2}` is taken to be `0` and `N(X α, V)` is the point mass at `X α`.
