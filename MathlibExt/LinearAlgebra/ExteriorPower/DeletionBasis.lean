/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.LinearAlgebra.ExteriorPower.Deletion
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Injectivity of exterior-power deletion

The deletion map is injective whenever the module has a basis. The proof
recovers each exterior-basis vector from one distinguished coordinate of the
tensor-product basis. It works over every commutative ring and requires no
finite-generation or invertibility hypothesis.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable section

open Function
open scoped TensorProduct

universe u v

namespace exteriorPower

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

section Basis

variable {I : Type*} [LinearOrder I]

/-- The ordered basis subset left after deleting position `r`. -/
private noncomputable def deletionEraseIndex (n : ℕ)
    (s : Set.powersetCard I (n + 1)) (r : Fin (n + 1)) :
    Set.powersetCard I n :=
  Set.powersetCard.ofFinEmbEquiv
    ((Fin.succAboveOrderEmb r).trans
      (Set.powersetCard.ofFinEmbEquiv.symm s))

private lemma deletionEraseIndex_insert (n : ℕ)
    (s : Set.powersetCard I (n + 1)) (r : Fin (n + 1)) :
    insert (Set.powersetCard.ofFinEmbEquiv.symm s r)
        (deletionEraseIndex n s r).val = s.val := by
  ext x
  rw [Finset.mem_insert]
  rw [Set.powersetCard.mem_coe_iff, Set.powersetCard.mem_coe_iff]
  rw [show deletionEraseIndex n s r =
      Set.powersetCard.ofFinEmbEquiv
        ((Fin.succAboveOrderEmb r).trans
          (Set.powersetCard.ofFinEmbEquiv.symm s)) by rfl,
    Set.powersetCard.mem_ofFinEmbEquiv_iff_mem_range]
  change x = Set.powersetCard.ofFinEmbEquiv.symm s r ∨
      x ∈ Set.range ((Fin.succAboveOrderEmb r).trans
        (Set.powersetCard.ofFinEmbEquiv.symm s)) ↔ x ∈ s
  rw [← Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem]
  constructor
  · rintro (rfl | ⟨j, hj⟩)
    · exact ⟨r, rfl⟩
    · refine ⟨r.succAbove j, ?_⟩
      simpa [deletionEraseIndex] using hj
  · rintro ⟨k, hk⟩
    rcases r.eq_self_or_eq_succAbove k with (rfl | ⟨j, rfl⟩)
    · exact Or.inl hk.symm
    · exact Or.inr ⟨j, by simpa [deletionEraseIndex] using hk⟩

/-- Signed deletion formula on the exterior basis induced by `b`. -/
private theorem deletion_apply_basis (n : ℕ) (b : Module.Basis I R M)
    (s : Set.powersetCard I (n + 1)) :
    deletion R M n (b.exteriorPower (n + 1) s) =
      ∑ r : Fin (n + 1), (-1 : R) ^ r.val •
        ((b.exteriorPower n (deletionEraseIndex n s r)) ⊗ₜ[R]
          b (Set.powersetCard.ofFinEmbEquiv.symm s r)) := by
  rw [exteriorPower.basis_apply]
  change deletion R M n
      (ιMulti R (n + 1) (b ∘ Set.powersetCard.ofFinEmbEquiv.symm s)) = _
  rw [exteriorPower.deletion_apply_ιMulti]
  apply Finset.sum_congr rfl
  intro r _
  have homit :
      ιMulti R n
          ((b ∘ Set.powersetCard.ofFinEmbEquiv.symm s) ∘ r.succAbove) =
        b.exteriorPower n (deletionEraseIndex n s r) := by
    rw [exteriorPower.basis_apply]
    apply congrArg (ιMulti R n)
    funext j
    simp [deletionEraseIndex]
  rw [homit]
  rfl

private noncomputable def deletionInitIndex (n : ℕ)
    (s : Set.powersetCard I (n + 1)) : Set.powersetCard I n :=
  deletionEraseIndex n s (Fin.last n)

private noncomputable def deletionLastIndex (n : ℕ)
    (s : Set.powersetCard I (n + 1)) : I :=
  Set.powersetCard.ofFinEmbEquiv.symm s (Fin.last n)

private lemma deletion_tensorBasis_coord (n : ℕ) (b : Module.Basis I R M)
    (s t : Set.powersetCard I (n + 1)) (r : Fin (n + 1)) :
    Module.Basis.coord ((b.exteriorPower n).tensorProduct b)
        (deletionInitIndex n s, deletionLastIndex n s)
        ((b.exteriorPower n (deletionEraseIndex n t r)) ⊗ₜ[R]
          b (Set.powersetCard.ofFinEmbEquiv.symm t r)) =
      if deletionEraseIndex n t r = deletionInitIndex n s ∧
          Set.powersetCard.ofFinEmbEquiv.symm t r = deletionLastIndex n s
        then 1 else 0 := by
  rw [Module.Basis.coord_apply,
    Module.Basis.tensorProduct_repr_tmul_apply]
  simp only [Module.Basis.repr_self, Finsupp.single_apply, smul_eq_mul]
  by_cases hleft : deletionEraseIndex n t r = deletionInitIndex n s <;>
    by_cases hright : Set.powersetCard.ofFinEmbEquiv.symm t r =
      deletionLastIndex n s <;> simp [hleft, hright]

private lemma deletion_pair_eq_imp (n : ℕ)
    (s t : Set.powersetCard I (n + 1)) (r : Fin (n + 1))
    (hleft : deletionEraseIndex n t r = deletionInitIndex n s)
    (hright : Set.powersetCard.ofFinEmbEquiv.symm t r =
      deletionLastIndex n s) : t = s := by
  apply Subtype.ext
  calc
    t.val = insert (Set.powersetCard.ofFinEmbEquiv.symm t r)
        (deletionEraseIndex n t r).val :=
      (deletionEraseIndex_insert n t r).symm
    _ = insert (deletionLastIndex n s) (deletionInitIndex n s).val := by
      rw [hleft, hright]
    _ = s.val := by
      exact deletionEraseIndex_insert n s (Fin.last n)

private def deletionDual (n : ℕ) (b : Module.Basis I R M)
    (s : Set.powersetCard I (n + 1)) :
    Module.Dual R ((⋀[R]^n M) ⊗[R] M) :=
  (-1 : R) ^ n •
    Module.Basis.coord ((b.exteriorPower n).tensorProduct b)
      (deletionInitIndex n s, deletionLastIndex n s)

private lemma deletionDual_apply_same (n : ℕ) (b : Module.Basis I R M)
    (s : Set.powersetCard I (n + 1)) :
    deletionDual R M n b s
        (deletion R M n (b.exteriorPower (n + 1) s)) = 1 := by
  rw [deletionDual, LinearMap.smul_apply,
    deletion_apply_basis, map_sum]
  simp only [map_smul]
  rw [Finset.sum_eq_single (Fin.last n)]
  · rw [deletion_tensorBasis_coord]
    simp only [Fin.val_last, deletionInitIndex, deletionLastIndex,
      and_self, ↓reduceIte, smul_eq_mul]
    rw [mul_one, ← mul_pow]
    simp
  · intro r _ hr
    rw [deletion_tensorBasis_coord]
    have hright : Set.powersetCard.ofFinEmbEquiv.symm s r ≠
        deletionLastIndex n s := by
      exact (Set.powersetCard.ofFinEmbEquiv.symm s).injective.ne hr
    simp [hright]
  · simp

private lemma deletionDual_apply_ne (n : ℕ) (b : Module.Basis I R M)
    (s t : Set.powersetCard I (n + 1)) (hst : s ≠ t) :
    deletionDual R M n b s
        (deletion R M n (b.exteriorPower (n + 1) t)) = 0 := by
  rw [deletionDual, LinearMap.smul_apply,
    deletion_apply_basis, map_sum]
  simp only [map_smul]
  suffices
      (∑ r : Fin (n + 1), (-1 : R) ^ r.val •
        Module.Basis.coord ((b.exteriorPower n).tensorProduct b)
          (deletionInitIndex n s, deletionLastIndex n s)
          ((b.exteriorPower n (deletionEraseIndex n t r)) ⊗ₜ[R]
            b (Set.powersetCard.ofFinEmbEquiv.symm t r))) = 0 by
    rw [this, smul_zero]
  apply Finset.sum_eq_zero
  intro r _
  rw [deletion_tensorBasis_coord]
  have hpair : ¬(deletionEraseIndex n t r = deletionInitIndex n s ∧
      Set.powersetCard.ofFinEmbEquiv.symm t r = deletionLastIndex n s) := by
    rintro ⟨hleft, hright⟩
    exact hst (deletion_pair_eq_imp n s t r hleft hright).symm
  simp [hpair]

private theorem deletion_basis_linearIndependent (n : ℕ)
    (b : Module.Basis I R M) :
    LinearIndependent R (fun s : Set.powersetCard I (n + 1) =>
      deletion R M n (b.exteriorPower (n + 1) s)) := by
  apply LinearIndependent.of_pairwise_dual_eq_zero_one
    (v := fun s : Set.powersetCard I (n + 1) =>
      deletion R M n (b.exteriorPower (n + 1) s))
    (f := fun s => deletionDual R M n b s)
  · intro s t hst
    exact deletionDual_apply_ne R M n b s t hst
  · intro s
    exact deletionDual_apply_same R M n b s

private theorem injective_of_exteriorBasis_images_linearIndependent (n : ℕ)
    (b : Module.Basis I R M)
    (f : (⋀[R]^(n + 1) M) →ₗ[R] ((⋀[R]^n M) ⊗[R] M))
    (hli : LinearIndependent R (fun s : Set.powersetCard I (n + 1) =>
      f (b.exteriorPower (n + 1) s))) : Function.Injective f := by
  have hli' : LinearIndependent R
      (f ∘ fun s : Set.powersetCard I (n + 1) =>
        b.exteriorPower (n + 1) s) := by
    rw [show (f ∘ fun s : Set.powersetCard I (n + 1) =>
        b.exteriorPower (n + 1) s) =
      (fun s => f (b.exteriorPower (n + 1) s)) by rfl]
    exact hli
  exact @LinearMap.injective_of_linearIndependent
    R (⋀[R]^(n + 1) M) inferInstance inferInstance inferInstance
    ((⋀[R]^n M) ⊗[R] M) inferInstance inferInstance
    f (Set.powersetCard I (n + 1))
    (fun s => b.exteriorPower (n + 1) s)
    (b.exteriorPower (n + 1)).span_eq hli'

set_option backward.isDefEq.respectTransparency true in
/-- Deletion is injective when an ordered basis is supplied. -/
theorem deletion_injective_of_basis (n : ℕ) (b : Module.Basis I R M) :
    Function.Injective (deletion R M n) := by
  exact injective_of_exteriorBasis_images_linearIndependent R M n b
    (deletion R M n) (deletion_basis_linearIndependent R M n b)

end Basis

/-- Deletion is injective on every free module over a commutative ring. -/
theorem deletion_injective [Module.Free R M] (n : ℕ) :
    Function.Injective (deletion R M n) := by
  classical
  let _ : LinearOrder (Module.Free.ChooseBasisIndex R M) :=
    linearOrderOfSTO WellOrderingRel
  exact deletion_injective_of_basis R M n (Module.Free.chooseBasis R M)

end exteriorPower
