# The projected coproduct is the full signed shuffle sum

Let `R` be a commutative ring, `M` an `R`-module, and `E=ExteriorAlgebra R M`. Write `Δ` for
the exterior coproduct and `π_r : E → Λ^r_R M` for degree projection. Let `p,q : ℕ`,
`L(i)=Fin.castAdd q i`, and `R_b(j)=Fin.natAdd p j`. For `w : Fin(p+q) → M`, `(π_p ⊗
π_q)(Δ(ExteriorAlgebra.ιMulti R (p+q) w)) = ∑ s : Shuffle p q, sign(s.perm) • (ιMulti_R(w ∘
s.perm ∘ L) ⊗ ιMulti_R(w ∘ s.perm ∘ R_b))`.
