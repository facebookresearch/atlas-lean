# A selected subset has the signed shuffle tensor

Let `R` be a commutative ring, `M` an `R`-module, and `E=ExteriorAlgebra R M`. Write `Δ` for
the exterior coproduct and `π_r : E → Λ^r_R M` for degree projection. Let `p,q : ℕ`, `s :
Shuffle p q`, and `w : Fin(p+q) → M`. The mixed term at `s.leftPositions` equals `sign(s.perm)
• (ExteriorAlgebra.ιMulti_R(fun i ↦ w(s.perm(Fin.castAdd q i))) ⊗ ExteriorAlgebra.ιMulti_R(fun
j ↦ w(s.perm(Fin.natAdd p j)))))`.
