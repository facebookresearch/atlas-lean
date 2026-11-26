# Finite reconstruction from antidiagonal bidegrees

Let `R` be a commutative ring, `M` an `R`-module, and `E = ExteriorAlgebra R M`. Write `ι : M
→ E` for the generators, `γ` for the grade involution, and `Δ : E →ₗ[R] E ⊗[R] E` for the
exterior coproduct. Write `E_r = Λ^r_R M`, `π_r : E → E_r` for degree projection, and `j_r :
E_r → E` for inclusion. Let `D_n` be the span of `a_p ⊗ b_q` with `p+q=n`. For `n : ℕ`, the
reconstruction endomorphism of `E⊗E` is `R_n=∑ p : Fin(n+1), (j_p ⊗ j_(n-p)) ∘ (π_p ⊗
π_(n-p))`.
