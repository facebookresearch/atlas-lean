# The exterior unshuffle component

Let `R` be a commutative ring, `M` an `R`-module, and `p,q : ℕ`. The `R`-linear map `unshuffle
R M p q : Λ^(p+q)_R M → Λ^p_R M ⊗[R] Λ^q_R M` sends `ιMulti_R(w)` to `∑ s : Shuffle p q,
sign(s.perm) • (ιMulti_R(fun i ↦ w(s.perm(Fin.castAdd q i))) ⊗ ιMulti_R(fun j ↦
w(s.perm(Fin.natAdd p j)))))`. The empty block has its unit wedge.
