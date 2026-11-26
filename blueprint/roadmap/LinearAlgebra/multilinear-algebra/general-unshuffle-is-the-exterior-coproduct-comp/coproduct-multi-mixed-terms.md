# The coproduct word expands over every subset

Let `R` be a commutative ring, `M` an `R`-module, and `E=ExteriorAlgebra R M`. Write `Δ` for
the exterior coproduct and `π_r : E → Λ^r_R M` for degree projection. For `N : ℕ` and `w : Fin
N → M`, `Δ(ExteriorAlgebra.ιMulti R N w) = ∑ s : Finset(Fin N), coproductMixedTerm R M N s w`.
