# The null covariance is the BOLT-LMM marginal covariance

For [variance components](../../bolt-lmm-mixed-model-association/model.md) `(Φ, σ_g², σ_e²)` of the
BOLT-LMM model on `N` individuals, with `Φ` positive semidefinite, `σ_g² ≥ 0` and `σ_e² > 0`, the
[null covariance](null-cov.md) `σ_g² Φ + σ_e² I` is, by definition, the model's
[marginal phenotypic covariance matrix](../../bolt-lmm-mixed-model-association/v.md).
