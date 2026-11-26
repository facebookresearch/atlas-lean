# Linear maps preserve exterior coproducts

Let `R` be a commutative ring, `M` an `R`-module, and `E = ExteriorAlgebra R M`. Write `ι : M
→ E` for the generators, `γ` for the grade involution, and `Δ : E →ₗ[R] E ⊗[R] E` for the
exterior coproduct. For an `R`-module `N`, `f : M →ₗ[R] N`, and `a : E`, `(Λf ⊗ Λf)(Δ_M
a)=Δ_N(Λf a)`, where `Λf=ExteriorAlgebra.map f`.
