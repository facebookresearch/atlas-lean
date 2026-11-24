# The normal matrix is injective

**The normal matrix is injective** when `A` is identifiable: from
`(Aᵀ * A) *ᵥ θ = 0`, the quadratic form `θ ⬝ᵥ (Aᵀ * A) *ᵥ θ` rewrites (via
`Matrix.mulVec_mulVec`, `Matrix.dotProduct_mulVec` and `Matrix.vecMul_transpose`)
to `(A *ᵥ θ) ⬝ᵥ (A *ᵥ θ) = 0`, so `A *ᵥ θ = 0` by Mathlib's `dotProduct_self_eq_zero` and
then `θ = 0`.
