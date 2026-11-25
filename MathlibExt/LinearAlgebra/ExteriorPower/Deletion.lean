/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
-- Original authors: @toskua, Avocado
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.Alternating.DomCoprod
public import Mathlib.GroupTheory.Perm.Fin

/-!
# Deletion from an exterior power

This file defines the positive-degree component of the exterior
comultiplication that deletes one factor and records it in a right tensor
factor. On a decomposable wedge it is given by

```text
v₀ ∧ ... ∧ vₙ ↦ ∑ r, (-1)ʳ
  (v₀ ∧ ... ∧ v̂ᵣ ∧ ... ∧ vₙ) ⊗ vᵣ.
```

The construction uses `AlternatingMap.domCoprod`, so it is independent of a
basis and natural in the module. Degree zero is deliberately not part of the
API: `deletion R M n` has source degree `n + 1`.
-/

@[expose] public section


noncomputable section

open Function
open scoped TensorProduct

universe u v

namespace exteriorPower

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- The identity map regarded as a one-variable alternating map. -/
private def oneAlternating : M [⋀^Fin 1]→ₗ[R] M :=
  (AlternatingMap.ofSubsingleton R M M (0 : Fin 1)) LinearMap.id

/-- Put the singleton block first and identify the block sum with `Fin (n + 1)`. -/
private def deletionBlockEquiv (n : ℕ) : Fin 1 ⊕ Fin n ≃ Fin (n + 1) :=
  finSumFinEquiv.trans (finCongr (Nat.one_add n))

/-- The position occupied by the singleton block in a `(1,n)` shuffle. -/
private def deletionShufflePosition (n : ℕ)
    (q : Equiv.Perm.ModSumCongr (Fin 1) (Fin n)) : Fin (n + 1) :=
  Quotient.liftOn' q
    (fun σ => deletionBlockEquiv n (σ (Sum.inl 0)))
    (fun σ₁ σ₂ h => by
      rw [QuotientGroup.leftRel_apply] at h
      obtain ⟨⟨sl, sr⟩, h⟩ := h
      replace h := inv_mul_eq_iff_eq_mul.mp h.symm
      rw [h]
      simp only [Fin.isValue, Equiv.Perm.sumCongrHom_apply,
        Equiv.Perm.coe_mul, comp_apply, Equiv.sumCongr_apply, Sum.map_inl,
        EmbeddingLike.apply_eq_iff_eq, Sum.inl.injEq]
      exact Subsingleton.elim _ _)

/-- The order-preserving representative of the shuffle whose singleton
occupies position `r`. -/
private noncomputable def deletionShuffleRep (n : ℕ) (r : Fin (n + 1)) :
    Equiv.Perm (Fin 1 ⊕ Fin n) :=
  (Equiv.permCongr (deletionBlockEquiv n)).symm r.cycleRange.symm

private lemma deletionShuffleRep_singleton (n : ℕ) (r : Fin (n + 1)) :
    deletionShuffleRep n r (Sum.inl 0) = (deletionBlockEquiv n).symm r := by
  apply (deletionBlockEquiv n).injective
  rw [(deletionBlockEquiv n).apply_symm_apply]
  calc
    (deletionBlockEquiv n) (deletionShuffleRep n r (Sum.inl 0)) =
        ((deletionBlockEquiv n).permCongr (deletionShuffleRep n r))
          (deletionBlockEquiv n (Sum.inl 0)) := by
            rw [Equiv.permCongr_apply, (deletionBlockEquiv n).symm_apply_apply]
    _ = r.cycleRange.symm 0 := by
      rw [show (deletionBlockEquiv n).permCongr (deletionShuffleRep n r) =
          r.cycleRange.symm by
        exact (Equiv.permCongr (deletionBlockEquiv n)).apply_symm_apply _]
      rfl
    _ = r := Fin.cycleRange_symm_zero r

private lemma deletionShuffleRep_tail (n : ℕ) (r : Fin (n + 1)) (j : Fin n) :
    deletionShuffleRep n r (Sum.inr j) =
      (deletionBlockEquiv n).symm (r.succAbove j) := by
  apply (deletionBlockEquiv n).injective
  rw [(deletionBlockEquiv n).apply_symm_apply]
  calc
    (deletionBlockEquiv n) (deletionShuffleRep n r (Sum.inr j)) =
        ((deletionBlockEquiv n).permCongr (deletionShuffleRep n r))
          (deletionBlockEquiv n (Sum.inr j)) := by
            rw [Equiv.permCongr_apply, (deletionBlockEquiv n).symm_apply_apply]
    _ = r.cycleRange.symm j.succ := by
      rw [show (deletionBlockEquiv n).permCongr (deletionShuffleRep n r) =
          r.cycleRange.symm by
        exact (Equiv.permCongr (deletionBlockEquiv n)).apply_symm_apply _]
      congr 1
      apply Fin.ext
      simp [deletionBlockEquiv]
    _ = r.succAbove j := Fin.cycleRange_symm_succ r j

private lemma deletionShuffleRep_sign (n : ℕ) (r : Fin (n + 1)) :
    Equiv.Perm.sign (deletionShuffleRep n r) = (-1) ^ r.val := by
  calc
    Equiv.Perm.sign (deletionShuffleRep n r) =
        Equiv.Perm.sign ((deletionBlockEquiv n).permCongr
          (deletionShuffleRep n r)) :=
      (Equiv.Perm.sign_permCongr (deletionBlockEquiv n)
        (deletionShuffleRep n r)).symm
    _ = Equiv.Perm.sign r.cycleRange.symm := by
      rw [show (deletionBlockEquiv n).permCongr (deletionShuffleRep n r) =
          r.cycleRange.symm by
        exact (Equiv.permCongr (deletionBlockEquiv n)).apply_symm_apply _]
    _ = Equiv.Perm.sign r.cycleRange := Equiv.Perm.sign_inv _
    _ = (-1) ^ r.val := Fin.sign_cycleRange r

private lemma deletionShufflePosition_rep (n : ℕ) (r : Fin (n + 1)) :
    deletionShufflePosition n (Quotient.mk'' (deletionShuffleRep n r)) = r := by
  simp [deletionShufflePosition, deletionShuffleRep_singleton]

private theorem deletionShufflePosition_injective (n : ℕ) :
    Function.Injective (deletionShufflePosition n) := by
  intro q₁ q₂ hq
  induction q₁ using Quotient.inductionOn' with
  | _ σ₁ =>
      induction q₂ using Quotient.inductionOn' with
      | _ σ₂ =>
          simp only [deletionShufflePosition, Quotient.liftOn'_mk''] at hq
          have hσ : σ₁ (Sum.inl 0) = σ₂ (Sum.inl 0) :=
            (deletionBlockEquiv n).injective hq
          rw [Quotient.eq'', QuotientGroup.leftRel_apply]
          apply Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl
          rintro _ ⟨a, rfl⟩
          obtain rfl : a = 0 := Subsingleton.elim _ _
          refine ⟨0, ?_⟩
          simp only [Equiv.Perm.coe_mul, Function.comp_apply]
          rw [← hσ]
          simp

private theorem deletionShufflePosition_surjective (n : ℕ) :
    Function.Surjective (deletionShufflePosition n) := by
  intro r
  exact ⟨Quotient.mk'' (deletionShuffleRep n r), deletionShufflePosition_rep n r⟩

/-- The `(1,n)` shuffle cosets are indexed by the position of the singleton
block. -/
private noncomputable def deletionShuffleEquiv (n : ℕ) :
    Equiv.Perm.ModSumCongr (Fin 1) (Fin n) ≃ Fin (n + 1) :=
  Equiv.ofBijective (deletionShufflePosition n)
    ⟨deletionShufflePosition_injective n, deletionShufflePosition_surjective n⟩

private lemma deletionShuffleEquiv_symm_apply (n : ℕ) (r : Fin (n + 1)) :
    (deletionShuffleEquiv n).symm r =
      Quotient.mk'' (deletionShuffleRep n r) := by
  apply deletionShufflePosition_injective n
  change (deletionShuffleEquiv n) ((deletionShuffleEquiv n).symm r) =
    deletionShufflePosition n (Quotient.mk'' (deletionShuffleRep n r))
  rw [(deletionShuffleEquiv n).apply_symm_apply]
  exact (deletionShufflePosition_rep n r).symm

private lemma deletion_summand_rep (n : ℕ) (v : Fin (n + 1) → M)
    (r : Fin (n + 1)) :
    (TensorProduct.comm R M (⋀[R]^n M))
        ((AlternatingMap.domCoprod.summand (oneAlternating R M) (ιMulti R n)
          (Quotient.mk'' (deletionShuffleRep n r)))
            (v ∘ deletionBlockEquiv n)) =
      (-1 : R) ^ r.val •
        ((ιMulti R n (v ∘ r.succAbove)) ⊗ₜ[R] v r) := by
  rw [AlternatingMap.domCoprod.summand_mk'']
  rw [_root_.smul_apply, deletionShuffleRep_sign]
  rw [@Units.smul_def _ _ (_) (_), ← Int.cast_smul_eq_zsmul R,
    LinearEquiv.map_smul]
  simp only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one,
    Int.cast_pow, Int.cast_neg, Int.cast_one]
  change (-1 : R) ^ r.val •
      (TensorProduct.comm R M (⋀[R]^n M))
        (((oneAlternating R M).toMultilinearMap.domCoprod
          (ιMulti R n).toMultilinearMap).domDomCongr
            (deletionShuffleRep n r) (v ∘ deletionBlockEquiv n)) = _
  rw [MultilinearMap.domDomCongr_apply, MultilinearMap.domCoprod_apply,
    TensorProduct.comm_tmul]
  have hargs :
      (fun j : Fin n =>
        (v ∘ deletionBlockEquiv n) (deletionShuffleRep n r (Sum.inr j))) =
        v ∘ r.succAbove := by
    funext j
    rw [Function.comp_apply, Function.comp_apply, deletionShuffleRep_tail]
    simp
  have hright :
      (oneAlternating R M)
          (fun i : Fin 1 =>
            (v ∘ deletionBlockEquiv n) (deletionShuffleRep n r (Sum.inl i))) =
        v r := by
    rw [oneAlternating, AlternatingMap.ofSubsingleton_apply_apply]
    change (v ∘ deletionBlockEquiv n) (deletionShuffleRep n r (Sum.inl 0)) = v r
    rw [Function.comp_apply, deletionShuffleRep_singleton]
    simp
  rw [hargs]
  change (-1 : R) ^ r.val •
      ((ιMulti R n (v ∘ r.succAbove)) ⊗ₜ[R]
        (oneAlternating R M)
          (fun i : Fin 1 =>
            (v ∘ deletionBlockEquiv n) (deletionShuffleRep n r (Sum.inl i)))) = _
  rw [hright]

/-- The `(1,n)` exterior coproduct followed by tensor-factor exchange. -/
private def deletionAlternating (n : ℕ) :
    M [⋀^Fin (n + 1)]→ₗ[R] ((⋀[R]^n M) ⊗[R] M) :=
  (TensorProduct.comm R M (⋀[R]^n M)).toLinearMap.compAlternatingMap
    (((oneAlternating R M).domCoprod (ιMulti R n)).domDomCongr
      (deletionBlockEquiv n))

/-- Delete one factor from a positive exterior power and record it in a
right tensor factor. -/
@[no_expose]
def deletion (n : ℕ) :
    (⋀[R]^(n + 1) M) →ₗ[R] ((⋀[R]^n M) ⊗[R] M) :=
  alternatingMapLinearEquiv (R := R) (n := n + 1) (M := M)
    (N := (⋀[R]^n M) ⊗[R] M) (deletionAlternating R M n)

private theorem deletion_apply_ιMulti_raw (n : ℕ) (v : Fin (n + 1) → M) :
    deletion R M n (ιMulti R (n + 1) v) = deletionAlternating R M n v := by
  apply alternatingMapLinearEquiv_apply_ιMulti

/-- Signed deletion formula on a decomposable wedge. -/
theorem deletion_apply_ιMulti (n : ℕ) (v : Fin (n + 1) → M) :
    deletion R M n (ιMulti R (n + 1) v) =
      ∑ r : Fin (n + 1), (-1 : R) ^ r.val •
        ((ιMulti R n (v ∘ r.succAbove)) ⊗ₜ[R] v r) := by
  rw [deletion_apply_ιMulti_raw]
  change (TensorProduct.comm R M (⋀[R]^n M))
      (((oneAlternating R M).domCoprod (ιMulti R n))
        (v ∘ deletionBlockEquiv n)) = _
  rw [AlternatingMap.domCoprod_apply, _root_.sum_apply, map_sum]
  calc
    (∑ q : Equiv.Perm.ModSumCongr (Fin 1) (Fin n),
        (TensorProduct.comm R M (⋀[R]^n M))
          ((AlternatingMap.domCoprod.summand
            (oneAlternating R M) (ιMulti R n) q)
              (v ∘ deletionBlockEquiv n))) =
        ∑ r : Fin (n + 1),
          (TensorProduct.comm R M (⋀[R]^n M))
            ((AlternatingMap.domCoprod.summand
              (oneAlternating R M) (ιMulti R n)
                ((deletionShuffleEquiv n).symm r))
                  (v ∘ deletionBlockEquiv n)) := by
      exact ((deletionShuffleEquiv n).symm.sum_comp
        (fun q => (TensorProduct.comm R M (⋀[R]^n M))
          ((AlternatingMap.domCoprod.summand
            (oneAlternating R M) (ιMulti R n) q)
              (v ∘ deletionBlockEquiv n)))).symm
    _ = ∑ r : Fin (n + 1), (-1 : R) ^ r.val •
          ((ιMulti R n (v ∘ r.succAbove)) ⊗ₜ[R] v r) := by
      apply Finset.sum_congr rfl
      intro r _
      rw [deletionShuffleEquiv_symm_apply]
      exact deletion_summand_rep R M n v r

/-- Naturality of deletion under a linear map. -/
theorem deletion_naturality {N : Type*} [AddCommGroup N] [Module R N]
    (n : ℕ) (f : M →ₗ[R] N) :
    (TensorProduct.map (map n f) f).comp (deletion R M n) =
      (deletion R N n).comp (map (n + 1) f) := by
  apply exteriorPower.linearMap_ext
    (R := R) (n := n + 1) (M := M)
    (N := (⋀[R]^n N) ⊗[R] N)
  apply AlternatingMap.ext
  intro v
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.coe_comp,
    Function.comp_apply, deletion_apply_ιMulti, map_apply_ιMulti,
    map_sum, map_smul, TensorProduct.map_tmul]
  apply Finset.sum_congr rfl
  intro r _
  congr 2

end exteriorPower
