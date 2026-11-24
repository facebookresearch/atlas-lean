# Cond Distrib load Parameter corrected Reading

Gaussian posterior of the load parameters given the corrected
sensor reading: under a proper Gaussian prior `θ ~ N(m, Sθ)`,
independent Gaussian sensor noise `v ~ N(0, R)` and an invertible
innovation covariance, the conditional law of `θ` given the corrected
reading `toLp (Cmat *ᵥ u) + v - toLp (Cmat *ᵥ (K⁻¹ *ᵥ f0))` is, for
almost every reading `y`, Gaussian with mean
`m + Sθ Hᵀ (H Sθ Hᵀ + R)⁻¹ (y - H m)` and covariance
`Sθ - Sθ Hᵀ (H Sθ Hᵀ + R)⁻¹ H Sθ`, with `H` the load observation
matrix. No identifiability hypothesis is made. Uses the supported
inverse characterization `supported_mulVec_eq_iff_inv_mulVec` and the
linear-Gaussian conditioning theorem
`MetaMathlibExt.condDistrib_linear_add_of_indepFun`.
