/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.Alternating.DomCoprod

/-!
# Exterior unshuffle maps in all bidegrees

For a commutative ring `R` and an `R`-module `M`, unshuffle is the `R`-linear map `Λ^(p+q)_R M
→ Λ^p_R M ⊗[R] Λ^q_R M`. It is the alternating shuffle sum of the two exterior word maps,
indexed by block-permutation cosets.

A representative contributes its sign times the ordered first-block wedge tensor the ordered
second-block wedge. Each coset contributes once. The empty block has its unit wedge, and the
maps commute with arbitrary linear maps of modules.

Reference: Bourbaki, *Algebra*, Chapter III.
-/

@[expose] public section

noncomputable section

open Function
open scoped TensorProduct

universe u v w

namespace exteriorPower

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- Let `R` be a commutative ring, `M` an `R`-module, and `p,q : ℕ`. Put `u=finSumFinEquiv : Fin p
⊕ Fin q ≃ Fin(p+q)`. The alternating map on `v : Fin(p+q) → M` is the sum over
block-permutation cosets, with representative `σ` contributing `sign(σ) • (ιMulti_R(fun i ↦
v(u(σ(Sum.inl i)))) ⊗ ιMulti_R(fun j ↦ v(u(σ(Sum.inr j)))))`. Alternation makes each summand
independent of the chosen representative. -/
def unshuffleAlternating (p q : ℕ) :
    M [⋀^Fin (p + q)]→ₗ[R] ((⋀[R]^p M) ⊗[R] (⋀[R]^q M)) :=
  ((ιMulti R p).domCoprod (ιMulti R q)).domDomCongr
    (finSumFinEquiv : Fin p ⊕ Fin q ≃ Fin (p + q))

/-- Let `R` be a commutative ring, `M` an `R`-module, and `p,q : ℕ`. The `R`-linear map `unshuffle
R M p q : Λ^(p+q)_R M → Λ^p_R M ⊗[R] Λ^q_R M` sends `ιMulti_R(w)` to `∑ s : Shuffle p q,
sign(s.perm) • (ιMulti_R(fun i ↦ w(s.perm(Fin.castAdd q i))) ⊗ ιMulti_R(fun j ↦
w(s.perm(Fin.natAdd p j)))))`. The empty block has its unit wedge. -/
def unshuffle (p q : ℕ) :
    (⋀[R]^(p + q) M) →ₗ[R] ((⋀[R]^p M) ⊗[R] (⋀[R]^q M)) :=
  alternatingMapLinearEquiv (R := R) (n := p + q) (M := M)
    (N := (⋀[R]^p M) ⊗[R] (⋀[R]^q M)) (unshuffleAlternating R M p q)

/-- Let `R` be a commutative ring, `M` an `R`-module, `p,q : ℕ`, `v : Fin(p+q) → M`, and
`u=finSumFinEquiv`. Then `unshuffle R M p q (ιMulti_R v)` is the sum over `Perm.ModSumCongr
(Fin p) (Fin q)`. For a representative `σ` of a coset, the summand is `sign(σ) • (ιMulti_R(fun
i ↦ v(u(σ(Sum.inl i)))) ⊗ ιMulti_R(fun j ↦ v(u(σ(Sum.inr j)))))`. -/
theorem unshuffle_apply_ιMulti (p q : ℕ) (v : Fin (p + q) → M) :
    unshuffle R M p q (ιMulti R (p + q) v) =
      ∑ σ : Equiv.Perm.ModSumCongr (Fin p) (Fin q),
        AlternatingMap.domCoprod.summand (ιMulti R p) (ιMulti R q) σ
          (v ∘ (finSumFinEquiv : Fin p ⊕ Fin q ≃ Fin (p + q))) := by
  rw [unshuffle, alternatingMapLinearEquiv_apply_ιMulti]
  change ((ιMulti R p).domCoprod (ιMulti R q))
    (v ∘ (finSumFinEquiv : Fin p ⊕ Fin q ≃ Fin (p + q))) = _
  rw [AlternatingMap.domCoprod_apply, _root_.sum_apply]

/-- Let `R` be a commutative ring, `M` an `R`-module, and `p,q : ℕ`. Write `L(i)=Fin.castAdd q i`,
`R_b(j)=Fin.natAdd p j`, and `U_(p,q) : Λ^(p+q)_R M → Λ^p_R M ⊗[R] Λ^q_R M` for unshuffle. Let
`σ ∈ Perm(Fin p ⊕ Fin q)` and `v : Fin(p+q) → M`. Its coset summand is `sign(σ) •
(ιMulti_R(fun i ↦ v(finSumFinEquiv(σ(Sum.inl i)))) ⊗ ιMulti_R(fun j ↦
v(finSumFinEquiv(σ(Sum.inr j)))))`. -/
theorem unshuffle_summand_representative (p q : ℕ)
    (σ : Equiv.Perm (Fin p ⊕ Fin q)) (v : Fin (p + q) → M) :
    AlternatingMap.domCoprod.summand (ιMulti R p) (ιMulti R q) (Quotient.mk'' σ)
        (v ∘ (finSumFinEquiv : Fin p ⊕ Fin q ≃ Fin (p + q))) =
      Equiv.Perm.sign σ •
        (ιMulti R p (fun i => v (finSumFinEquiv (σ (Sum.inl i)))) ⊗ₜ[R]
          ιMulti R q (fun j => v (finSumFinEquiv (σ (Sum.inr j))))) := by
  rw [AlternatingMap.domCoprod.summand_mk'', _root_.smul_apply]
  simp only [MultilinearMap.domDomCongr_apply, MultilinearMap.domCoprod_apply,
    Function.comp_apply]
  exact (TensorProduct.smul_tmul' (Equiv.Perm.sign σ) _ _).symm

section Naturality

variable {N : Type w} [AddCommGroup N] [Module R N]

private theorem unshuffle_summand_naturality (p q : ℕ) (f : M →ₗ[R] N)
    (σ : Equiv.Perm.ModSumCongr (Fin p) (Fin q)) (v : Fin p ⊕ Fin q → M) :
    TensorProduct.map (map p f) (map q f)
        (AlternatingMap.domCoprod.summand (ιMulti R p) (ιMulti R q) σ v) =
      AlternatingMap.domCoprod.summand (ιMulti R p) (ιMulti R q) σ (f ∘ v) := by
  induction σ using Quotient.inductionOn' with
  | _ σ =>
      rw [AlternatingMap.domCoprod.summand_mk'',
        AlternatingMap.domCoprod.summand_mk'', _root_.smul_apply, _root_.smul_apply]
      simp only [Units.smul_def, map_zsmul, MultilinearMap.domDomCongr_apply,
        MultilinearMap.domCoprod_apply, TensorProduct.map_tmul, map_apply_ιMulti]
      change (TensorProduct.map (map p f) (map q f))
        ((Equiv.Perm.sign σ : ℤ) •
          (ιMulti R p (fun i => v (σ (Sum.inl i))) ⊗ₜ[R]
            ιMulti R q (fun i => v (σ (Sum.inr i))))) = _
      rw [map_zsmul, TensorProduct.map_tmul, map_apply_ιMulti, map_apply_ιMulti]
      rfl

/-- Let `R` be a commutative ring, `M` an `R`-module, and `p,q : ℕ`. Write `L(i)=Fin.castAdd q i`,
`R_b(j)=Fin.natAdd p j`, and `U_(p,q) : Λ^(p+q)_R M → Λ^p_R M ⊗[R] Λ^q_R M` for unshuffle. For
an `R`-module `N` and `f : M →ₗ[R] N`, `(Λ^p f ⊗ Λ^q f) ∘ U_(p,q)^M = U_(p,q)^N ∘ Λ^(p+q) f`. -/
theorem unshuffle_naturality (p q : ℕ) (f : M →ₗ[R] N) :
    (TensorProduct.map (map p f) (map q f)).comp (unshuffle R M p q) =
      (unshuffle R N p q).comp (map (p + q) f) := by
  apply exteriorPower.linearMap_ext (R := R) (n := p + q) (M := M)
    (N := (⋀[R]^p N) ⊗[R] (⋀[R]^q N))
  apply AlternatingMap.ext
  intro v
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    unshuffle_apply_ιMulti, map_apply_ιMulti, map_sum]
  apply Finset.sum_congr rfl
  intro σ _
  exact unshuffle_summand_naturality R M p q f σ
    (v ∘ (finSumFinEquiv : Fin p ⊕ Fin q ≃ Fin (p + q)))

end Naturality

end exteriorPower
