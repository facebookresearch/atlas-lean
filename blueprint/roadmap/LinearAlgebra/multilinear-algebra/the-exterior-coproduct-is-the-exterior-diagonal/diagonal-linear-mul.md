# The linear diagonal has signed insertion recursion

Let `R` be a commutative ring, `M` an `R`-module, and `E = ExteriorAlgebra R M`. Write `ι : M
→ E` for the generators, `γ` for the grade involution, and `Δ : E →ₗ[R] E ⊗[R] E` for the
exterior coproduct. Let `G` be the graded tensor algebra of the exterior degree families and
`τ : E ⊗[R] E ≃ₗ[R] G` its linear identification. Its homogeneous product is
`(a_p⊗b_q)(c_r⊗d_s)=(-1)^(q*r)(a_pc_r⊗b_qd_s)`. For `x : M` and `a : E`, `diagonalLinear R M
(ι(x)*a)=signedInsertion R M x (diagonalLinear R M a)`.
