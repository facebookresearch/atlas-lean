# Entries of the drift covariance matrix

For a finite set of edges, real lineage weights `w X e` and nonnegative edge lengths `ℓ e`, the
entries of the [drift covariance matrix](drift-cov.md) `Σ = W diag(ℓ) Wᵀ` are
`Σ X Y = ∑ e, w X e * w Y e * ℓ e` for all populations `X`, `Y`.
