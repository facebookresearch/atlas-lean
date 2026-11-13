# Additive batch/biology design

The samples × features matrix
`X = E + 𝟙 μᵀ + b βᵀ + s δᵀ`: a residual matrix `E`, a feature-wise baseline `μ`, a batch
covariate `b` (e.g. the batch indicator) with batch effect `β`, and a biological covariate `s`
(e.g. the condition indicator) with biological signal `δ`. The design is *confounded* when
`s = b`, i.e. every sample of one condition was processed in one batch.
