# The matching projection retains a shuffle term

Let `R` be a commutative ring, `M` an `R`-module, `p,q : ℕ`, `s : Shuffle p q`, and `w :
Fin(p+q) → M`. For degree projections `π_r : ExteriorAlgebra R M → Λ^r_R M`, `(π_p ⊗
π_q)(coproductMixedTerm R M (p+q) s.leftPositions w)` is `sign(s.perm) • (ιMulti_R(fun i ↦
w(s.perm(Fin.castAdd q i))) ⊗ ιMulti_R(fun j ↦ w(s.perm(Fin.natAdd p j)))))`.
