# Gaussian surrogate law of population allele frequencies

For finitely many populations `P` and edges `E`, a root mean `m ∈ ℝ`, real lineage weights `w X e`
and nonnegative edge lengths `ℓ e`, the Gaussian drift surrogate (TreeMix) is the multivariate
normal law `N(m 1, Σ)` on `ℝ^P` with its Euclidean structure: its mean vector is `m 1 = (m, …, m)`
and its covariance matrix is the [drift covariance matrix](drift-cov.md) `Σ = W diag(ℓ) Wᵀ`. It is a
probability measure, read as a law of the vector of population allele frequencies. As `Σ` is
[positive semidefinite](pos-semidef-drift-cov.md) for all weights and lengths, it is a genuine
Gaussian law, degenerate when `Σ` is singular: with all lengths `0` it is the Dirac mass at `m 1`.
Unlike genuine allele frequencies, its coordinates need not be confined to `[0, 1]`: a coordinate
of positive variance is [negative with positive probability](gaussian-surrogate-coord-neg-pos.md),
while a coordinate of zero variance [equals `m` almost surely](gaussian-surrogate-coord-ae-eq.md).
