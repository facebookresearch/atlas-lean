# Signed insertion on two exterior factors

Let `R` be a commutative ring, `M` an `R`-module, and `E = ExteriorAlgebra R M`. Write `ι : M
→ E` for the generators, `γ` for the grade involution, and `Δ : E →ₗ[R] E ⊗[R] E` for the
exterior coproduct. For `x : M`, `signedInsertion R M x` is the endomorphism `a⊗b ↦ ι(x)*a ⊗ b
+ γ(a) ⊗ ι(x)*b`. The assignment `x ↦ signedInsertion x` is `R`-linear.
