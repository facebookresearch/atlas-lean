# Conditional estimate of second-block effects (COJO)

The unconditional algebraic formula from Yang et al. 2012, eq. (15):
`(X₂ᵀX₂)⁻¹ X₂ᵀ y - (X₂ᵀX₂)⁻¹ X₂ᵀX₁ (X₁ᵀX₁)⁻¹ X₁ᵀ y`. When both Gram determinants are units,
this has the usual interpretation as the block-2 fit conditional on the block-1 fit. For a
singular Gram matrix, Mathlib's nonsingular inverse is zero and the value can be a junk value.
