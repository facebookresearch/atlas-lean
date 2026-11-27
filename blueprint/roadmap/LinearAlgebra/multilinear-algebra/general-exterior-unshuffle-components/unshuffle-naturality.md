# Linear maps commute with exterior unshuffle

Let `R` be a commutative ring, `M` an `R`-module, and `p,q : ℕ`. Write `L(i)=Fin.castAdd q i`,
`R_b(j)=Fin.natAdd p j`, and `U_(p,q) : Λ^(p+q)_R M → Λ^p_R M ⊗[R] Λ^q_R M` for unshuffle. For
an `R`-module `N` and `f : M →ₗ[R] N`, `(Λ^p f ⊗ Λ^q f) ∘ U_(p,q)^M = U_(p,q)^N ∘ Λ^(p+q) f`.
