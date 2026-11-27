# The exterior diagonal into the graded tensor algebra

Let `R` be a commutative ring, `M` an `R`-module, and `E = ExteriorAlgebra R M`. Write `ι : M
→ E` for the generators, `γ` for the grade involution, and `Δ : E →ₗ[R] E ⊗[R] E` for the
exterior coproduct. Let `G` be the graded tensor algebra of the exterior degree families and
`τ : E ⊗[R] E ≃ₗ[R] G` its linear identification. Its homogeneous product is
`(a_p⊗b_q)(c_r⊗d_s)=(-1)^(q*r)(a_pc_r⊗b_qd_s)`. The `R`-algebra map `diagonalGraded R M : E
→ₐ[R] G` is induced by `x ↦ (x,x)` followed by the exterior-algebra product equivalence. It
sends a generator to `ι(x)⊗1+1⊗ι(x)` in `G`.
