# A coset representative gives the signed two-block tensor

Let `R` be a commutative ring, `M` an `R`-module, and `p,q : ℕ`. Write `L(i)=Fin.castAdd q i`,
`R_b(j)=Fin.natAdd p j`, and `U_(p,q) : Λ^(p+q)_R M → Λ^p_R M ⊗[R] Λ^q_R M` for unshuffle. Let
`σ ∈ Perm(Fin p ⊕ Fin q)` and `v : Fin(p+q) → M`. Its coset summand is `sign(σ) •
(ιMulti_R(fun i ↦ v(finSumFinEquiv(σ(Sum.inl i)))) ⊗ ιMulti_R(fun j ↦
v(finSumFinEquiv(σ(Sum.inr j)))))`.
