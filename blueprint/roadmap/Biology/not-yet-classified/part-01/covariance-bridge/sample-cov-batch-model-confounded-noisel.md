# What `S` does see

Without residual noise, the covariance of a confounded design is
`var(b) • (β + δ)(β + δ)ᵀ`: the combined effect `β + δ` is visible (when `b` is not constant),
only the split is not; `S` has rank at most one
(`rank_sampleCov_batchModel_confounded_noiseless_le`), a singular boundary case for `2 ≤ p`.
