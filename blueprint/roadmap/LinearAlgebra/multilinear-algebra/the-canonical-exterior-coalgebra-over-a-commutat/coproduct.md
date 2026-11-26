# The exterior coproduct

Let `R` be a commutative ring, `M` an `R`-module, and `E = ExteriorAlgebra R M`. Write `ι : M
→ E` for the generators, `γ` for the grade involution, and `Δ : E →ₗ[R] E ⊗[R] E` for the
exterior coproduct. The coproduct is determined by `Δ(1)=1⊗1` and `Δ(ι(x)*a)=D_x(Δ a)`, where
`D_x(a⊗b)=ι(x)a⊗b+γ(a)⊗ι(x)b`. In particular its generators have coproduct `1⊗ι(x)+ι(x)⊗1`.
