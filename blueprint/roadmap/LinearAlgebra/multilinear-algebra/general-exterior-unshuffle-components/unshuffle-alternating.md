# The alternating unshuffle word map

Let `R` be a commutative ring, `M` an `R`-module, and `p,q : ℕ`. Put `u=finSumFinEquiv : Fin p
⊕ Fin q ≃ Fin(p+q)`. The alternating map on `v : Fin(p+q) → M` is the sum over
block-permutation cosets, with representative `σ` contributing `sign(σ) • (ιMulti_R(fun i ↦
v(u(σ(Sum.inl i)))) ⊗ ιMulti_R(fun j ↦ v(u(σ(Sum.inr j)))))`. Alternation makes each summand
independent of the chosen representative.
