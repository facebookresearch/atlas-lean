/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.KTheory.Ring.K2.MatsumotoTitsBruhatExtension
public import MathlibExt.KTheory.Ring.K2.MatsumotoBruhatLeftTransition
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Finite root lifts in the Matsumoto Bruhat extension

Weyl elements and upper-root transvections have explicit lifts to the finite-
rank left Bruhat extension. Their projection formulas include lower-root lifts
formed from two adjacent roots, with an explicit specialization to rank three.
-/

@[expose] public section

universe u

open Matrix
open Matrix.GeneralLinearGroup
open MatsumotoTitsBruhatFiber
open MatsumotoBruhatLeftTransition
open scoped commutatorElement

namespace MatsumotoTitsBruhatFiber

noncomputable def leftWeylLift (F : Type u) [Field F] (n : ℕ) {i j : Fin n}
    (hij : i ⋖ j) : leftExtensionSubgroup F n :=
  ⟨(Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ),
      leftWeylPerm (F := F) (n := n) hij),
    leftWeylPair_mem_leftExtensionSubgroup (F := F) (n := n) hij⟩

@[simp]
theorem leftWeylLift_val (F : Type u) [Field F] (n : ℕ) {i j : Fin n}
    (hij : i ⋖ j) :
    (leftWeylLift F n hij).val =
      (Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ),
        leftWeylPerm (F := F) (n := n) hij) :=
  rfl

@[simp]
theorem leftWeylLift_val_fst (F : Type u) [Field F] (n : ℕ) {i j : Fin n}
    (hij : i ⋖ j) :
    (leftWeylLift F n hij).val.1 =
      Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ) :=
  rfl

@[simp]
theorem leftWeylLift_val_snd (F : Type u) [Field F] (n : ℕ) {i j : Fin n}
    (hij : i ⋖ j) :
    (leftWeylLift F n hij).val.2 = leftWeylPerm (F := F) (n := n) hij :=
  rfl

@[simp]
theorem leftExtensionProjHom_leftWeylLift (F : Type u) [Field F] (n : ℕ)
    {i j : Fin n} (hij : i ⋖ j) :
    leftExtensionProjHom F n (leftWeylLift F n hij) =
      Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ) :=
  rfl

noncomputable def leftUpperRootLift (F : Type u) [Field F] (n : ℕ)
    (i j : Fin n) (hij : i < j) (r : F) : leftExtensionSubgroup F n :=
  ⟨(UpperElementary.toSLHom (UpperElementary.elementary i j hij r),
      leftUpperPerm (F := F) (n := n)
        (UpperElementary.elementary i j hij r)),
    leftUpperPair_mem_leftExtensionSubgroup
      (F := F) (n := n) (UpperElementary.elementary i j hij r)⟩

@[simp]
theorem leftUpperRootLift_val (F : Type u) [Field F] (n : ℕ)
    (i j : Fin n) (hij : i < j) (r : F) :
    (leftUpperRootLift F n i j hij r).val =
      (UpperElementary.toSLHom (UpperElementary.elementary i j hij r),
        leftUpperPerm (F := F) (n := n)
          (UpperElementary.elementary i j hij r)) :=
  rfl

@[simp]
theorem leftExtensionProjHom_leftUpperRootLift (F : Type u) [Field F] (n : ℕ)
    (i j : Fin n) (hij : i < j) (r : F) :
    leftExtensionProjHom F n (leftUpperRootLift F n i j hij r) =
      Matrix.SpecialLinearGroup.transvection (ne_of_lt hij) r := by
  simp only [leftUpperRootLift, leftExtensionProjHom_apply,
    MatsumotoBruhatLeftTransition.toSLHom_elementary_eq_transvection]

noncomputable def leftLowerAdjacentRootLift (F : Type u) [Field F] (n : ℕ)
    {i j : Fin n} (hij : i ⋖ j) (r : F) : leftExtensionSubgroup F n :=
  leftWeylLift F n hij * leftUpperRootLift F n i j hij.lt (-r) *
    (leftWeylLift F n hij)⁻¹

@[simp]
theorem leftExtensionProjHom_leftLowerAdjacentRootLift (F : Type u) [Field F]
    (n : ℕ) {i j : Fin n} (hij : i ⋖ j) (r : F) :
    leftExtensionProjHom F n (leftLowerAdjacentRootLift F n hij r) =
      Matrix.SpecialLinearGroup.transvection hij.ne.symm r := by
  unfold leftLowerAdjacentRootLift
  simp only [map_mul, map_inv, leftExtensionProjHom_leftWeylLift,
    leftExtensionProjHom_leftUpperRootLift]
  have h := Matrix.GeneralLinearGroup.weylSLUnit_one_conj_transvection_neg
    (R := F) (i := i) (j := j) hij.ne r
  simpa using h

@[simp]
theorem leftUpperRootLift_zero (F : Type u) [Field F] (n : ℕ)
    (i j : Fin n) (hij : i < j) :
    leftUpperRootLift F n i j hij 0 = 1 := by
  have hElemZero :
      UpperElementary.elementary i j hij (0 : F) = 1 := by
    apply Subtype.ext
    simp [UpperElementary.coe_elementary]
  have hSL :
      UpperElementary.toSLHom
          (UpperElementary.elementary i j hij (0 : F)) = 1 := by
    rw [hElemZero, map_one]
  have hPerm :
      leftUpperPerm
          (UpperElementary.elementary i j hij (0 : F)) = 1 := by
    rw [hElemZero, leftUpperPerm_one]
  apply Subtype.ext
  simp [leftUpperRootLift_val, hSL, hPerm]

theorem leftUpperRootLift_add (F : Type u) [Field F] (n : ℕ)
    (i j : Fin n) (hij : i < j) (r s : F) :
    leftUpperRootLift F n i j hij (r + s) =
      leftUpperRootLift F n i j hij r *
        leftUpperRootLift F n i j hij s := by
  have hElemAdd :
      UpperElementary.elementary i j hij (r + s) =
        UpperElementary.elementary i j hij r *
          UpperElementary.elementary i j hij s := by
    apply Subtype.ext
    apply Units.ext
    simp [UpperElementary.coe_elementary,
      Matrix.GeneralLinearGroup.elementary_mul_same]
  have hSL :
      UpperElementary.toSLHom
          (UpperElementary.elementary i j hij (r + s)) =
        UpperElementary.toSLHom
            (UpperElementary.elementary i j hij r) *
          UpperElementary.toSLHom
            (UpperElementary.elementary i j hij s) := by
    rw [hElemAdd, map_mul]
  have hPerm :
      leftUpperPerm
          (UpperElementary.elementary i j hij (r + s)) =
        leftUpperPerm (UpperElementary.elementary i j hij r) *
          leftUpperPerm (UpperElementary.elementary i j hij s) := by
    rw [hElemAdd, leftUpperPerm_mul]
  apply Subtype.ext
  simp [leftUpperRootLift_val, hSL, hPerm]

theorem leftUpperRootLift_neg (F : Type u) [Field F] (n : ℕ)
    (i j : Fin n) (hij : i < j) (r : F) :
    leftUpperRootLift F n i j hij (-r) =
      (leftUpperRootLift F n i j hij r)⁻¹ := by
  have hAdd :
      leftUpperRootLift F n i j hij (r + -r) =
        leftUpperRootLift F n i j hij r *
          leftUpperRootLift F n i j hij (-r) :=
    leftUpperRootLift_add F n i j hij r (-r)
  have hZero :
      leftUpperRootLift F n i j hij (0 : F) = 1 :=
    leftUpperRootLift_zero F n i j hij
  have hSumZero : r + -r = (0 : F) := by simp
  have hMulOne :
      leftUpperRootLift F n i j hij r *
          leftUpperRootLift F n i j hij (-r) = 1 := by
    calc leftUpperRootLift F n i j hij r *
            leftUpperRootLift F n i j hij (-r)
        = leftUpperRootLift F n i j hij (r + -r) := hAdd.symm
      _ = leftUpperRootLift F n i j hij (0 : F) := by
          rw [hSumZero]
      _ = 1 := hZero
  calc leftUpperRootLift F n i j hij (-r)
      = 1 * leftUpperRootLift F n i j hij (-r) := by simp
    _ = ((leftUpperRootLift F n i j hij r)⁻¹ *
          leftUpperRootLift F n i j hij r) *
        leftUpperRootLift F n i j hij (-r) := by
        rw [← inv_mul_cancel]
    _ = (leftUpperRootLift F n i j hij r)⁻¹ *
        (leftUpperRootLift F n i j hij r *
          leftUpperRootLift F n i j hij (-r)) := by
        rw [mul_assoc]
    _ = (leftUpperRootLift F n i j hij r)⁻¹ * 1 := by
        rw [hMulOne]
    _ = (leftUpperRootLift F n i j hij r)⁻¹ := by simp

@[simp]
theorem leftLowerAdjacentRootLift_zero (F : Type u) [Field F]
    (n : ℕ) {i j : Fin n} (hij : i ⋖ j) :
    leftLowerAdjacentRootLift F n hij 0 = 1 := by
  unfold leftLowerAdjacentRootLift
  have hNegZero : -(0 : F) = 0 := neg_zero
  rw [hNegZero]
  have hUpperZero :
      leftUpperRootLift F n i j hij.lt (0 : F) = 1 :=
    leftUpperRootLift_zero F n i j hij.lt
  rw [hUpperZero]
  simp

theorem leftLowerAdjacentRootLift_add (F : Type u) [Field F]
    (n : ℕ) {i j : Fin n} (hij : i ⋖ j) (r s : F) :
    leftLowerAdjacentRootLift F n hij (r + s) =
      leftLowerAdjacentRootLift F n hij r *
        leftLowerAdjacentRootLift F n hij s := by
  unfold leftLowerAdjacentRootLift
  have hNegAdd : (-(r + s) : F) = (-r) + (-s) := by
    rw [neg_add, add_comm]
  have hUpperAdd :
      leftUpperRootLift F n i j hij.lt (-(r + s)) =
        leftUpperRootLift F n i j hij.lt (-r) *
          leftUpperRootLift F n i j hij.lt (-s) := by
    calc leftUpperRootLift F n i j hij.lt (-(r + s))
        = leftUpperRootLift F n i j hij.lt ((-r) + (-s)) := by
            rw [hNegAdd]
      _ = leftUpperRootLift F n i j hij.lt (-r) *
            leftUpperRootLift F n i j hij.lt (-s) := by
            rw [leftUpperRootLift_add]
  calc leftWeylLift F n hij *
          leftUpperRootLift F n i j hij.lt (-(r + s)) *
          (leftWeylLift F n hij)⁻¹
      = leftWeylLift F n hij *
          (leftUpperRootLift F n i j hij.lt (-r) *
            leftUpperRootLift F n i j hij.lt (-s)) *
          (leftWeylLift F n hij)⁻¹ := by
          rw [hUpperAdd]
    _ = leftWeylLift F n hij *
          leftUpperRootLift F n i j hij.lt (-r) *
          (leftWeylLift F n hij)⁻¹ *
          (leftWeylLift F n hij *
            leftUpperRootLift F n i j hij.lt (-s) *
            (leftWeylLift F n hij)⁻¹) := by
          calc leftWeylLift F n hij *
                  (leftUpperRootLift F n i j hij.lt (-r) *
                    leftUpperRootLift F n i j hij.lt (-s)) *
                  (leftWeylLift F n hij)⁻¹
              = leftWeylLift F n hij *
                  leftUpperRootLift F n i j hij.lt (-r) *
                  leftUpperRootLift F n i j hij.lt (-s) *
                  (leftWeylLift F n hij)⁻¹ := by
                simp only [mul_assoc]
            _ = leftWeylLift F n hij *
                  leftUpperRootLift F n i j hij.lt (-r) *
                  (1 * leftUpperRootLift F n i j hij.lt (-s)) *
                  (leftWeylLift F n hij)⁻¹ := by
                simp
            _ = leftWeylLift F n hij *
                  leftUpperRootLift F n i j hij.lt (-r) *
                  ((leftWeylLift F n hij)⁻¹ *
                    leftWeylLift F n hij *
                    leftUpperRootLift F n i j hij.lt (-s)) *
                  (leftWeylLift F n hij)⁻¹ := by
                rw [← inv_mul_cancel]
            _ = leftWeylLift F n hij *
                  leftUpperRootLift F n i j hij.lt (-r) *
                  (leftWeylLift F n hij)⁻¹ *
                  (leftWeylLift F n hij *
                    leftUpperRootLift F n i j hij.lt (-s) *
                    (leftWeylLift F n hij)⁻¹) := by
                simp only [mul_assoc]

theorem leftLowerAdjacentRootLift_neg (F : Type u) [Field F]
    (n : ℕ) {i j : Fin n} (hij : i ⋖ j) (r : F) :
    leftLowerAdjacentRootLift F n hij (-r) =
      (leftLowerAdjacentRootLift F n hij r)⁻¹ := by
  have hAdd :
      leftLowerAdjacentRootLift F n hij (r + -r) =
        leftLowerAdjacentRootLift F n hij r *
          leftLowerAdjacentRootLift F n hij (-r) :=
    leftLowerAdjacentRootLift_add F n hij r (-r)
  have hZero :
      leftLowerAdjacentRootLift F n hij (0 : F) = 1 :=
    leftLowerAdjacentRootLift_zero F n hij
  have hSumZero : r + -r = (0 : F) := by simp
  have hMulOne :
      leftLowerAdjacentRootLift F n hij r *
          leftLowerAdjacentRootLift F n hij (-r) = 1 := by
    calc leftLowerAdjacentRootLift F n hij r *
            leftLowerAdjacentRootLift F n hij (-r)
        = leftLowerAdjacentRootLift F n hij (r + -r) := hAdd.symm
      _ = leftLowerAdjacentRootLift F n hij (0 : F) := by
          rw [hSumZero]
      _ = 1 := hZero
  calc leftLowerAdjacentRootLift F n hij (-r)
      = 1 * leftLowerAdjacentRootLift F n hij (-r) := by simp
    _ = ((leftLowerAdjacentRootLift F n hij r)⁻¹ *
          leftLowerAdjacentRootLift F n hij r) *
        leftLowerAdjacentRootLift F n hij (-r) := by
        rw [← inv_mul_cancel]
    _ = (leftLowerAdjacentRootLift F n hij r)⁻¹ *
        (leftLowerAdjacentRootLift F n hij r *
          leftLowerAdjacentRootLift F n hij (-r)) := by
        rw [mul_assoc]
    _ = (leftLowerAdjacentRootLift F n hij r)⁻¹ * 1 := by
        rw [hMulOne]
    _ = (leftLowerAdjacentRootLift F n hij r)⁻¹ := by simp

noncomputable def leftLowerTwoStepRootLift (F : Type u) [Field F] (n : ℕ)
    {a b c : Fin n} (hab : a ⋖ b) (hbc : b ⋖ c) (r : F) :
    leftExtensionSubgroup F n :=
  ⁅leftLowerAdjacentRootLift F n hbc r,
    leftLowerAdjacentRootLift F n hab (1 : F)⁆

@[simp]
theorem leftExtensionProjHom_leftLowerTwoStepRootLift (F : Type u) [Field F]
    (n : ℕ) {a b c : Fin n} (hab : a ⋖ b) (hbc : b ⋖ c) (r : F) :
    leftExtensionProjHom F n (leftLowerTwoStepRootLift F n hab hbc r) =
      Matrix.SpecialLinearGroup.transvection
        (ne_of_gt (lt_trans hab.lt hbc.lt)) r := by
  unfold leftLowerTwoStepRootLift
  rw [map_commutatorElement]
  simp only [leftExtensionProjHom_leftLowerAdjacentRootLift]
  exact Matrix.GeneralLinearGroup.transvection_commutator_lower
    (R := F) hab.lt hbc.lt r

theorem fin3_01_covBy : (0 : Fin 3) ⋖ (1 : Fin 3) := by
  constructor
  · decide
  · intro c hc
    fin_cases c <;> simp_all

theorem fin3_12_covBy : (1 : Fin 3) ⋖ (2 : Fin 3) := by
  constructor
  · decide
  · intro c hc
    fin_cases c <;> simp_all

noncomputable def leftLowerRootLift20 (F : Type u) [Field F] (r : F) :
    leftExtensionSubgroup F 3 :=
  leftLowerTwoStepRootLift F 3 fin3_01_covBy fin3_12_covBy r

@[simp]
theorem leftExtensionProjHom_leftLowerRootLift20 (F : Type u) [Field F]
    (r : F) :
    leftExtensionProjHom F 3 (leftLowerRootLift20 F r) =
      Matrix.SpecialLinearGroup.transvection
        (show (2 : Fin 3) ≠ 0 by decide) r := by
  unfold leftLowerRootLift20
  have h := leftExtensionProjHom_leftLowerTwoStepRootLift
    (F := F) (n := 3)
    (a := (0 : Fin 3)) (b := (1 : Fin 3)) (c := (2 : Fin 3))
    fin3_01_covBy fin3_12_covBy r
  have h_eq :
      Matrix.SpecialLinearGroup.transvection
          (ne_of_gt
            (lt_trans
              (show (0 : Fin 3) < 1 by decide)
              (show (1 : Fin 3) < 2 by decide))) r =
        Matrix.SpecialLinearGroup.transvection
          (show (2 : Fin 3) ≠ (0 : Fin 3) by decide) r := by
    apply Subtype.ext
    rfl
  rw [h, h_eq]

end MatsumotoTitsBruhatFiber

end
