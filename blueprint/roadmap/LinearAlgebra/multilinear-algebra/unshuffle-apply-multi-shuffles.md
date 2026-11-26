# The full ordered-shuffle unshuffle formula

Let `R` be a commutative ring, `M` an `R`-module, and `p,q : ℕ`. Write `L(i)=Fin.castAdd q i`,
`R_b(j)=Fin.natAdd p j`, and `U_(p,q) : Λ^(p+q)_R M → Λ^p_R M ⊗[R] Λ^q_R M` for unshuffle. For
`w : Fin(p+q) → M`, the value is `∑ s : Shuffle p q, sign(s.perm) • (ιMulti_R(fun i ↦
w(s.perm(L i))) ⊗ ιMulti_R(fun j ↦ w(s.perm(R_b j))))`.
