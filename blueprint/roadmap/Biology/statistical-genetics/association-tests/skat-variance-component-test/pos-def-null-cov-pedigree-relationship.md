# With residual noise the pedigree null covariance is positive definite

For every [pedigree](../../../quantitative-genetics/pedigree-kinship-and-inbreeding/pedigree.md) on
`N` individuals, `σ_g² ≥ 0` and `σ_e² > 0`, the famSKAT [null covariance](null-cov.md)
`Σ₀ = σ_g² · 2φ + σ_e² I`, with `2φ` the [additive relationship matrix](pedigree-relationship.md) of
the pedigree, is positive definite.
