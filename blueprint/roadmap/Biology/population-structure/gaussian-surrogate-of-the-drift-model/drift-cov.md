# Drift covariance matrix of lineage weights and edge lengths

For a finite set `E` of edges, a set `P` of populations, real lineage weights `w X e` (`X ∈ P`,
`e ∈ E`) and nonnegative edge lengths `ℓ e ≥ 0`, the drift covariance is the `P × P` matrix
`Σ = W diag(ℓ) Wᵀ`, where `W` is the `P × E` matrix of the weights. Its
[entries](drift-cov-apply.md) are `Σ X Y = ∑ e, w X e * w Y e * ℓ e`. It is the covariance matrix of
the [Gaussian surrogate](gaussian-surrogate.md) (TreeMix) when `P` is finite.
