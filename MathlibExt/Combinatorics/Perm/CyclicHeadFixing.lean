/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



module

public import MathlibExt.Combinatorics.Perm.CyclicDescentNumber
public import MathlibExt.GroupTheory.Perm.OrderedDeletion
public import MathlibExt.Logic.Equiv.Fin.Rotate
public import Mathlib.Algebra.Group.Fin.Basic

/-!
# Actual cyclic rotation and head-fixing decomposition

The native rotation powers enumerate every original position. A head-fixing
permutation acts on the original remaining positions, and actual rotation
followed by head fixing gives a permutation decomposition in every
degree. The inverse is constructed from finite injectivity/cardinality;
no decomposition or coefficient-count certificate is supplied.
-/

@[expose] public section
noncomputable section

open scoped BigOperators
open Fin.NatCast

namespace Equiv.Perm

open Fin.NatCast in
/-- Every original rotation power has its actual cyclic-addition coordinate. -/
theorem rotationPower_apply (n r : ℕ) (i : Fin (n + 1)) :
    (finRotate (n + 1) ^ r) i = i + (r : Fin (n + 1)) := by
  induction r with
  | zero => simp
  | succ r hr =>
    simp only [pow_succ', Equiv.Perm.mul_apply, hr, finRotate_apply,
      Nat.cast_succ, add_assoc]

/-- Native rotation powers retain every actual finite position coordinate. -/
theorem rotationPower_atFin_apply (n : ℕ) (r i : Fin (n + 1)) :
    (finRotate (n + 1) ^ r.val) i = i + r := by
  rw [rotationPower_apply]
  congr 1
  apply Fin.ext
  change r.val % (n + 1) = r.val
  exact Nat.mod_eq_of_lt r.isLt

/-- The actual inverse rotation has the actual negative finite coordinate. -/
theorem rotationPower_inverse (n : ℕ) (r : Fin (n + 1)) :
    (finRotate (n + 1) ^ r.val)⁻¹ = finRotate (n + 1) ^ (-r).val := by
  apply Equiv.ext
  intro i
  have h : (finRotate (n + 1) ^ r.val) ((finRotate (n + 1) ^ (-r).val) i) = i := by
    rw [rotationPower_atFin_apply, rotationPower_atFin_apply]
    simp only [add_assoc, neg_add_cancel, add_zero]
  exact ((finRotate (n + 1) ^ r.val).injective
    ((Equiv.apply_symm_apply _ i).trans h.symm))

/-- The actual first-position rotation coordinate is the original rotation index. -/
theorem rotationPower_zero (n : ℕ) (r : Fin (n + 1)) :
    (finRotate (n + 1) ^ r.val) 0 = r := by
  rw [rotationPower_apply, zero_add]
  apply Fin.ext
  change r.val % (n + 1) = r.val
  exact Nat.mod_eq_of_lt r.isLt

/-- The actual closing-cut rotation coordinate is cyclic translation by the original last position. -/
theorem rotationPower_last (n : ℕ) (r : Fin (n + 1)) :
    (finRotate (n + 1) ^ r.val) (Fin.last n) = Fin.last n + r := by
  rw [rotationPower_apply]
  congr 1
  apply Fin.ext
  change r.val % (n + 1) = r.val
  exact Nat.mod_eq_of_lt r.isLt

/-- The closing-cut coordinate equivalence. -/
def closingCutEquiv (n : ℕ) : Fin (n + 1) ≃ Fin (n + 1) :=
  Equiv.addLeft (Fin.last n)

/-- The coordinate equivalence has exactly the native closing-cut rotation value. -/
theorem closingCutEquiv_apply (n : ℕ) (r : Fin (n + 1)) :
    closingCutEquiv n r = (finRotate (n + 1) ^ r.val) (Fin.last n) :=
  (rotationPower_last n r).symm

/-- The actual first position is fixed and every old tail position is retained in order. -/
def headFixingPermutation (n : ℕ) (π : Perm (Fin n)) : Perm (Fin (n + 1)) := orderedFirst 0 π

@[simp]
theorem headFixingPermutation_zero (n : ℕ) (π : Perm (Fin n)) : headFixingPermutation n π 0 = 0 :=
  orderedFirst_zero 0 π

@[simp]
theorem headFixingPermutation_succ (n : ℕ) (π : Perm (Fin n)) (i : Fin n) :
    headFixingPermutation n π i.succ = (π i).succ := by
  rw [headFixingPermutation, orderedFirst_succ,
    Fin.succAbove_of_le_castSucc 0 (π i) (Fin.zero_le _)]

/-- The actual head-fixing permutation retains the original tail sign. -/
theorem headFixingPermutation_sign (n : ℕ) (π : Perm (Fin n)) :
    (headFixingPermutation n π).sign = π.sign := by
  rw [headFixingPermutation, sign_orderedFirst, Fin.val_zero, pow_zero, one_mul]

/-- The head-fixing embedding into the next symmetric group. -/
def headFixingHom (n : ℕ) : Perm (Fin n) →* Perm (Fin (n + 1)) where
  toFun := headFixingPermutation n
  map_one' := by
    ext i
    cases i using Fin.cases with
    | zero => rw [headFixingPermutation_zero]; rfl
    | succ i => rw [headFixingPermutation_succ]; rfl
  map_mul' π τ := by
    ext i
    cases i using Fin.cases with
    | zero => simp only [Equiv.Perm.mul_apply, headFixingPermutation_zero]
    | succ i => simp only [Equiv.Perm.mul_apply, headFixingPermutation_succ]

/-- Actual tail positions determine the entire head-fixing permutation. -/
theorem headFixingHom_injective (n : ℕ) : Function.Injective (headFixingHom n) := by
  intro π τ h
  apply Equiv.ext
  intro i
  have hi := congrArg (fun p : Perm (Fin (n + 1)) => p i.succ) h
  change headFixingPermutation n π i.succ = headFixingPermutation n τ i.succ at hi
  rw [headFixingPermutation_succ, headFixingPermutation_succ] at hi
  exact (Fin.succ_injective n) hi

/-- The original rotation index and original tail permutation determine the full permutation. -/
theorem rotationHead_uncurry_injective (n : ℕ) :
    Function.Injective (fun z : Fin (n + 1) × Perm (Fin n) =>
      finRotate (n + 1) ^ z.1.val * headFixingHom n z.2) := by
  rintro ⟨r, π⟩ ⟨s, τ⟩ h
  have hrs : r = s := by
    have h0 := congrArg (fun p : Perm (Fin (n + 1)) => p 0) h
    change (finRotate (n + 1) ^ r.val) (headFixingPermutation n π 0) =
      (finRotate (n + 1) ^ s.val) (headFixingPermutation n τ 0) at h0
    rw [headFixingPermutation_zero, headFixingPermutation_zero,
      rotationPower_zero, rotationPower_zero] at h0
    exact h0
  subst s
  have hπτ : π = τ := headFixingHom_injective n (mul_left_cancel h)
  subst τ
  rfl

/-- The actual all-degree rotation/head-fixing permutation decomposition. -/
def rotationHeadEquiv (n : ℕ) : Fin (n + 1) × Perm (Fin n) ≃ Perm (Fin (n + 1)) :=
  Equiv.ofBijective (fun z => finRotate (n + 1) ^ z.1.val * headFixingHom n z.2) (by
    rw [Nat.bijective_iff_injective_and_card]
    refine ⟨rotationHead_uncurry_injective n, ?_⟩
    simp only [Nat.card_eq_fintype_card]
    calc
      Fintype.card (Fin (n + 1) × Perm (Fin n)) = (n + 1) * Nat.factorial n := by
        rw [Fintype.card_prod, Fintype.card_perm, Fintype.card_fin, Fintype.card_fin]
      _ = Fintype.card (Perm (Fin (n + 1))) := by
        rw [Fintype.card_perm, Fintype.card_fin, Nat.factorial_succ])

/-- Every original complete permutation sum is the actual rotation/head-fixing sum. -/
theorem sum_rotationHead {T : Type*} [AddCommMonoid T] (n : ℕ)
    (f : Perm (Fin (n + 1)) → T) :
    ∑ σ : Perm (Fin (n + 1)), f σ =
      ∑ r : Fin (n + 1), ∑ π : Perm (Fin n), f (finRotate (n + 1) ^ r.val * headFixingHom n π) := by
  rw [← (rotationHeadEquiv n).sum_comp f, Fintype.sum_prod_type]
  rfl

end Equiv.Perm
