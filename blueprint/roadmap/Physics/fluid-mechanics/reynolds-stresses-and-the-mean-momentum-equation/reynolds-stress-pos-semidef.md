# Reynolds Stress pos Semidef

The Reynolds stress is positive semidefinite: `∑ⱼ ∑ᵢ aⱼ aᵢ 𝔼[u'ⱼ u'ᵢ] ≥ 0` for every vector
`a`, for `L²` velocity components. It is the covariance form of the law of the velocity at
`(τ, y)`, so this is Mathlib's `isPosSemidef_covarianceBilin`, not a new proof.
