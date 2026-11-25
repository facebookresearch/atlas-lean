# The drift covariance matrix is positive semidefinite

For finitely many populations and edges, real lineage weights `w` and nonnegative edge lengths `ℓ`,
the [drift covariance matrix](drift-cov.md) `Σ = W diag(ℓ) Wᵀ` is positive semidefinite: it is
symmetric and `∑ X, ∑ Y, x X * Σ X Y * x Y ≥ 0` for every real vector `x` indexed by the
populations.
