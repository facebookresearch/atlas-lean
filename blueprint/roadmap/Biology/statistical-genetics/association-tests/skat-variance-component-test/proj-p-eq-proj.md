# The null projection is the BOLT-LMM residual-forming matrix

For [variance components](../../bolt-lmm-mixed-model-association/model.md) `(Φ, σ_g², σ_e²)` of the
BOLT-LMM model on `N` individuals and every real `N × p` covariate matrix `X`, the
[null projection](proj-p.md) built from the model's
[marginal phenotypic covariance](../../bolt-lmm-mixed-model-association/v.md) `V = σ_g² Φ + σ_e² I`
is the model's [residual-forming matrix](../../bolt-lmm-mixed-model-association/proj.md)
`V⁻¹ - V⁻¹ X (Xᵀ V⁻¹ X)⁻¹ Xᵀ V⁻¹`.
