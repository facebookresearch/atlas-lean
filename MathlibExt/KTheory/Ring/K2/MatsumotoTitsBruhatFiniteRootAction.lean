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

public import MathlibExt.KTheory.Ring.K2.MatsumotoTitsBruhatFiniteRootLifts
public import MathlibExt.KTheory.Ring.K2.MatsumotoTitsBruhatKernelEquality

/-!
# Finite root calculations in the Tits Bruhat action

Computes lower-root lifts, their inverses and their matrix and monomial
coordinates. Explicit rank-three calculations establish two lifted root
commutator identities by tracking these coordinates through each action stage.
-/

@[expose] public section

universe u

open Matrix
open Matrix.GeneralLinearGroup
open MatsumotoTitsMonomialExtension
open MatsumotoTitsWeylLift
open MatsumotoBruhatLeftTransition
open MatsumotoTitsBruhatFiber
open PermutationBilinearCocycle
open scoped commutatorElement

namespace MatsumotoTitsBruhatFiber

theorem leftLowerAdjacentRootLift_snd_X_one_of_ne_zero
    (F : Type u) [Field F] (n : ℕ) {i j : Fin n}
    (hij : i ⋖ j) (r : F) (hr : r ≠ 0) :
    X.snd
        ((leftLowerAdjacentRootLift F n hij r).val.2 (X_one F n)) =
      (hTits F n i j hij.ne (Units.mk0 r hr))⁻¹ *
        (weylHMTits F n i j hij.ne (1 : Fˣ))⁻¹ := by
  have hNeg : (-r) ≠ 0 := neg_ne_zero.mpr hr
  have hUnitsEq : torusUnitOfNegCoeff (-r) hNeg = Units.mk0 r hr := by
    apply Units.ext
    simp [torusUnitOfNegCoeff]
  have hPerm : (leftLowerAdjacentRootLift F n hij r).val.2 =
      leftWeylPerm (F := F) (n := n) hij *
      leftUpperPerm (F := F) (UpperElementary.elementary i j hij.lt (-r)) *
      (leftWeylPerm (F := F) (n := n) hij)⁻¹ := by
    simp [leftLowerAdjacentRootLift, leftWeylLift_val, leftUpperRootLift_val]
  have hSym : (leftWeylPerm (F := F) (n := n) hij)⁻¹ = (leftWeylPerm (F := F) hij).symm := rfl
  calc X.snd ((leftLowerAdjacentRootLift F n hij r).val.2 (X_one F n))
      = X.snd ((leftWeylPerm (F := F) (n := n) hij *
          leftUpperPerm (F := F) (UpperElementary.elementary i j hij.lt (-r)) *
          (leftWeylPerm (F := F) (n := n) hij)⁻¹) (X_one F n)) := by
        rw [hPerm]
    _ = X.snd (leftWeylPerm (F := F) (n := n) hij
          (leftUpperPerm (F := F) (UpperElementary.elementary i j hij.lt (-r))
            ((leftWeylPerm (F := F) (n := n) hij)⁻¹ (X_one F n)))) := by
        simp only [Equiv.Perm.mul_apply]
    _ = leftWeylMultiplier hij
            (X.fst (leftUpperPerm (F := F) (UpperElementary.elementary i j hij.lt (-r))
              ((leftWeylPerm (F := F) (n := n) hij)⁻¹ (X_one F n)))) *
          X.snd (leftUpperPerm (F := F) (UpperElementary.elementary i j hij.lt (-r))
            ((leftWeylPerm (F := F) (n := n) hij)⁻¹ (X_one F n))) := by
        rw [leftWeylPerm_snd]
    _ = leftWeylMultiplier hij
            (X.fst (leftUpperPerm (F := F) (UpperElementary.elementary i j hij.lt (-r))
              ((leftWeylPerm (F := F) (n := n) hij)⁻¹ (X_one F n)))) *
          X.snd ((leftWeylPerm (F := F) (n := n) hij)⁻¹ (X_one F n)) := by
        have hSnd : X.snd (leftUpperPerm (F := F) (UpperElementary.elementary i j hij.lt (-r))
              ((leftWeylPerm (F := F) (n := n) hij)⁻¹ (X_one F n))) =
            X.snd ((leftWeylPerm (F := F) (n := n) hij)⁻¹ (X_one F n)) := by
          rw [leftUpperPerm_apply, leftUpper_snd]
        rw [hSnd]
    _ = leftWeylMultiplier hij
            (Matrix.SpecialLinearGroup.transvection hij.ne (-r) *
              (Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ))⁻¹) *
          X.snd ((leftWeylPerm (F := F) (n := n) hij)⁻¹ (X_one F n)) := by
        have hFstMid : X.fst (leftUpperPerm (F := F) (UpperElementary.elementary i j hij.lt (-r))
              ((leftWeylPerm (F := F) (n := n) hij)⁻¹ (X_one F n))) =
            Matrix.SpecialLinearGroup.transvection hij.ne (-r) *
              (Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ))⁻¹ := by
          rw [leftUpperPerm_apply, leftUpper_fst]
          have hEq : X.fst ((leftWeylPerm (F := F) (n := n) hij)⁻¹ (X_one F n)) =
              (Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ))⁻¹ * X.fst (X_one F n) := by
            rw [hSym, leftWeylPerm_symm_fst]
          rw [hEq, toSLHom_elementary_eq_transvection, X_one_fst, mul_one]
        rw [hFstMid]
    _ = (hTits F n i j hij.ne (torusUnitOfNegCoeff (-r) hNeg))⁻¹ *
          X.snd ((leftWeylPerm (F := F) (n := n) hij)⁻¹ (X_one F n)) := by
        have hCoeffEq : leftSimpleRootCoeff F n
                  (Matrix.SpecialLinearGroup.transvection hij.ne (-r) *
                    (Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ))⁻¹) hij = -r :=
            leftSimpleRootCoeff_transvection_neg_mul_weylSLUnit_inv hij r
        have hNotPos : ¬ ((Matrix.GeneralLinearGroup.bruhatMiddle
                  (Matrix.SpecialLinearGroup.transvection hij.ne (-r) *
                    (Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ))⁻¹) :
                  PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)).right.symm i <
                (Matrix.GeneralLinearGroup.bruhatMiddle
                  (Matrix.SpecialLinearGroup.transvection hij.ne (-r) *
                    (Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ))⁻¹) :
                  PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)).right.symm j) :=
            bruhatMiddle_transvection_neg_mul_weylSLUnit_inv_not_pos hij r
        have hPos : leftWeylMultiplier hij
                (Matrix.SpecialLinearGroup.transvection hij.ne (-r) *
                  (Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ))⁻¹) =
              (hTits F n i j hij.ne (torusUnitOfNegCoeff (-r) hNeg))⁻¹ := by
          have hrNe : leftSimpleRootCoeff F n
                  (Matrix.SpecialLinearGroup.transvection hij.ne (-r) *
                    (Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ))⁻¹) hij ≠ 0 := by
            rw [hCoeffEq]
            exact hNeg
          have hEq : torusUnitOfNegCoeff
                  (leftSimpleRootCoeff F n
                    (Matrix.SpecialLinearGroup.transvection hij.ne (-r) *
                      (Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ))⁻¹) hij) hrNe =
                  torusUnitOfNegCoeff (-r) hNeg := by
            apply Units.ext
            simp [torusUnitOfNegCoeff, hCoeffEq]
          have hMul := leftWeylMultiplier_of_neg hij
              (Matrix.SpecialLinearGroup.transvection hij.ne (-r) *
                (Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ))⁻¹) hrNe hNotPos
          rw [hEq] at hMul
          exact hMul
        rw [hPos]
    _ = (hTits F n i j hij.ne (torusUnitOfNegCoeff (-r) hNeg))⁻¹ *
          ((leftWeylMultiplier hij
              ((Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ))⁻¹ *
                X.fst (X_one F n)))⁻¹ * X.snd (X_one F n)) := by
        have hSndInv : X.snd ((leftWeylPerm (F := F) (n := n) hij)⁻¹ (X_one F n)) =
            (leftWeylMultiplier hij
              ((Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ))⁻¹ *
                X.fst (X_one F n)))⁻¹ * X.snd (X_one F n) := by
          rw [hSym, leftWeylPerm_symm_snd]
        rw [hSndInv]
    _ = (hTits F n i j hij.ne (torusUnitOfNegCoeff (-r) hNeg))⁻¹ *
          ((leftWeylMultiplier hij
              ((Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ))⁻¹ *
                X.fst (X_one F n)))⁻¹ * (1 : HMTits F n)) := by
        rw [X_one_snd]
    _ = (hTits F n i j hij.ne (torusUnitOfNegCoeff (-r) hNeg))⁻¹ *
          (leftWeylMultiplier hij
              ((Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ))⁻¹ *
                X.fst (X_one F n)))⁻¹ := by
        rw [mul_one]
    _ = (hTits F n i j hij.ne (torusUnitOfNegCoeff (-r) hNeg))⁻¹ *
          (weylHMTits F n i j hij.ne (1 : Fˣ))⁻¹ := by
        have hZeroCoeff : leftSimpleRootCoeff F n
                ((Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ))⁻¹ *
                  X.fst (X_one F n)) hij = 0 := by
          have hS0_eq : (weylSLUnit i j hij.ne (1 : Fˣ))⁻¹ *
                  X.fst (X_one F n) =
                SpecialLinearGroup.transvection hij.ne (-(0 : F)) *
                  (weylSLUnit i j hij.ne (1 : Fˣ))⁻¹ := by
            calc (weylSLUnit i j hij.ne (1 : Fˣ))⁻¹ *
                    X.fst (X_one F n)
                = (weylSLUnit i j hij.ne (1 : Fˣ))⁻¹ *
                    (1 : Matrix.SpecialLinearGroup (Fin n) F) := by
                  rw [X_one_fst]
              _ = (weylSLUnit i j hij.ne (1 : Fˣ))⁻¹ := by
                  rw [mul_one]
              _ = (1 : Matrix.SpecialLinearGroup (Fin n) F) *
                    (weylSLUnit i j hij.ne (1 : Fˣ))⁻¹ := by
                  rw [one_mul]
              _ = SpecialLinearGroup.transvection hij.ne (-(0 : F)) *
                    (weylSLUnit i j hij.ne (1 : Fˣ))⁻¹ := by
                  rw [neg_zero, SpecialLinearGroup.transvection_coeff_zero]
          rw [hS0_eq, leftSimpleRootCoeff_transvection_neg_mul_weylSLUnit_inv, neg_zero]
        have hMulZero : leftWeylMultiplier hij
                ((Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ))⁻¹ *
                  X.fst (X_one F n)) = weylHMTits F n i j hij.ne (1 : Fˣ) := by
          exact leftWeylMultiplier_of_zero hij
              ((Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne (1 : Fˣ))⁻¹ *
                X.fst (X_one F n)) hZeroCoeff
        rw [hMulZero]
    _ = (hTits F n i j hij.ne (Units.mk0 r hr))⁻¹ *
          (weylHMTits F n i j hij.ne (1 : Fˣ))⁻¹ := by
        rw [hUnitsEq]

@[simp] theorem leftLowerAdjacentRootLift_snd_X_one_one
    (F : Type u) [Field F] (n : ℕ) {i j : Fin n} (hij : i ⋖ j) :
    X.snd
        ((leftLowerAdjacentRootLift F n hij (1 : F)).val.2 (X_one F n)) =
      (hTits F n i j hij.ne (1 : Fˣ))⁻¹ *
        (weylHMTits F n i j hij.ne (1 : Fˣ))⁻¹ := by
  have hr : (1 : F) ≠ 0 := one_ne_zero
  have h := leftLowerAdjacentRootLift_snd_X_one_of_ne_zero F n hij (1 : F) hr
  have hEq : Units.mk0 (1 : F) hr = (1 : Fˣ) := by
    apply Units.ext
    simp
  rw [hEq] at h
  exact h

theorem leftLowerAdjacentRootLift_fst_apply
    (F : Type u) [Field F] (n : ℕ) {i j : Fin n}
    (hij : i ⋖ j) (r : F) (x : X F n) :
    X.fst ((leftLowerAdjacentRootLift F n hij r).val.2 x) =
      Matrix.SpecialLinearGroup.transvection hij.ne.symm r *
        X.fst x := by
  have h :=
    leftExtensionProjHom_coe
      (F := F) (n := n) (leftLowerAdjacentRootLift F n hij r) x
  have hProj :
      leftExtensionProjHom F n (leftLowerAdjacentRootLift F n hij r) =
        Matrix.SpecialLinearGroup.transvection hij.ne.symm r := by
    exact leftExtensionProjHom_leftLowerAdjacentRootLift F n hij r
  rw [hProj] at h
  exact h

theorem leftLowerAdjacentRootLift_snd_apply
    (F : Type u) [Field F] (n : ℕ) {i j : Fin n}
    (hij : i ⋖ j) (r : F) (x : X F n) :
    X.snd ((leftLowerAdjacentRootLift F n hij r).val.2 x) =
      leftWeylMultiplier (F := F) hij
          (Matrix.SpecialLinearGroup.transvection hij.ne (-r) *
            (Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne
                (1 : Fˣ))⁻¹ *
            X.fst x) *
        (leftWeylMultiplier (F := F) hij
          ((Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne
              (1 : Fˣ))⁻¹ *
            X.fst x))⁻¹ *
        X.snd x := by
  have hPerm :
      (leftLowerAdjacentRootLift F n hij r).val.2 =
        leftWeylPerm (F := F) (n := n) hij *
          leftUpperPerm (F := F)
            (UpperElementary.elementary i j hij.lt (-r)) *
          (leftWeylPerm (F := F) (n := n) hij)⁻¹ := by
    simp [leftLowerAdjacentRootLift, leftWeylLift_val,
      leftUpperRootLift_val]
  have hSym :
      (leftWeylPerm (F := F) (n := n) hij)⁻¹ =
        (leftWeylPerm (F := F) (n := n) hij).symm := rfl
  calc X.snd ((leftLowerAdjacentRootLift F n hij r).val.2 x)
      = X.snd
          ((leftWeylPerm (F := F) (n := n) hij *
            leftUpperPerm (F := F)
              (UpperElementary.elementary i j hij.lt (-r)) *
            (leftWeylPerm (F := F) (n := n) hij)⁻¹) x) := by
        rw [hPerm]
    _ = X.snd
          (leftWeylPerm (F := F) (n := n) hij
            (leftUpperPerm (F := F)
              (UpperElementary.elementary i j hij.lt (-r))
              ((leftWeylPerm (F := F) (n := n) hij)⁻¹ x))) := by
        simp only [Equiv.Perm.mul_apply]
    _ = leftWeylMultiplier (F := F) hij
            (X.fst
              (leftUpperPerm (F := F)
                (UpperElementary.elementary i j hij.lt (-r))
                ((leftWeylPerm (F := F) (n := n) hij)⁻¹ x))) *
          X.snd
            (leftUpperPerm (F := F)
              (UpperElementary.elementary i j hij.lt (-r))
              ((leftWeylPerm (F := F) (n := n) hij)⁻¹ x)) := by
        rw [leftWeylPerm_snd]
    _ = leftWeylMultiplier (F := F) hij
            (X.fst
              (leftUpperPerm (F := F)
                (UpperElementary.elementary i j hij.lt (-r))
                ((leftWeylPerm (F := F) (n := n) hij)⁻¹ x))) *
          X.snd ((leftWeylPerm (F := F) (n := n) hij)⁻¹ x) := by
        have hSnd :
            X.snd
              (leftUpperPerm (F := F)
                (UpperElementary.elementary i j hij.lt (-r))
                ((leftWeylPerm (F := F) (n := n) hij)⁻¹ x)) =
            X.snd ((leftWeylPerm (F := F) (n := n) hij)⁻¹ x) := by
          rw [leftUpperPerm_apply, leftUpper_snd]
        rw [hSnd]
    _ = leftWeylMultiplier (F := F) hij
            (Matrix.SpecialLinearGroup.transvection hij.ne (-r) *
              X.fst ((leftWeylPerm (F := F) (n := n) hij)⁻¹ x)) *
          X.snd ((leftWeylPerm (F := F) (n := n) hij)⁻¹ x) := by
        have hFstMid :
            X.fst
              (leftUpperPerm (F := F)
                (UpperElementary.elementary i j hij.lt (-r))
                ((leftWeylPerm (F := F) (n := n) hij)⁻¹ x)) =
            Matrix.SpecialLinearGroup.transvection hij.ne (-r) *
              X.fst ((leftWeylPerm (F := F) (n := n) hij)⁻¹ x) := by
          rw [leftUpperPerm_apply, leftUpper_fst,
            toSLHom_elementary_eq_transvection]
        rw [hFstMid]
    _ = leftWeylMultiplier (F := F) hij
            (Matrix.SpecialLinearGroup.transvection hij.ne (-r) *
              ((Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne
                  (1 : Fˣ))⁻¹ * X.fst x)) *
          X.snd ((leftWeylPerm (F := F) (n := n) hij)⁻¹ x) := by
        have hFstInv :
            X.fst ((leftWeylPerm (F := F) (n := n) hij)⁻¹ x) =
              (Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne
                  (1 : Fˣ))⁻¹ * X.fst x := by
          rw [hSym, leftWeylPerm_symm_fst]
        rw [hFstInv]
    _ = leftWeylMultiplier (F := F) hij
            (Matrix.SpecialLinearGroup.transvection hij.ne (-r) *
              (Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne
                  (1 : Fˣ))⁻¹ * X.fst x) *
          X.snd ((leftWeylPerm (F := F) (n := n) hij)⁻¹ x) := by
        have hAssoc :
            Matrix.SpecialLinearGroup.transvection hij.ne (-r) *
                ((Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne
                    (1 : Fˣ))⁻¹ * X.fst x) =
              Matrix.SpecialLinearGroup.transvection hij.ne (-r) *
                (Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne
                    (1 : Fˣ))⁻¹ * X.fst x := by
          rw [← mul_assoc]
        rw [hAssoc]
    _ = leftWeylMultiplier (F := F) hij
            (Matrix.SpecialLinearGroup.transvection hij.ne (-r) *
              (Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne
                  (1 : Fˣ))⁻¹ * X.fst x) *
          ((leftWeylMultiplier (F := F) hij
              ((Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne
                  (1 : Fˣ))⁻¹ * X.fst x))⁻¹ *
            X.snd x) := by
        have hSndInv :
            X.snd ((leftWeylPerm (F := F) (n := n) hij)⁻¹ x) =
              (leftWeylMultiplier (F := F) hij
                  ((Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne
                      (1 : Fˣ))⁻¹ * X.fst x))⁻¹ *
                X.snd x := by
          rw [hSym, leftWeylPerm_symm_snd]
        rw [hSndInv]
    _ = leftWeylMultiplier (F := F) hij
            (Matrix.SpecialLinearGroup.transvection hij.ne (-r) *
              (Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne
                  (1 : Fˣ))⁻¹ * X.fst x) *
          (leftWeylMultiplier (F := F) hij
            ((Matrix.GeneralLinearGroup.weylSLUnit i j hij.ne
                (1 : Fˣ))⁻¹ * X.fst x))⁻¹ *
          X.snd x := by
        rw [← mul_assoc]

theorem leftWeylMultiplier_weyl12_inv_mul_transvection10_neg_one
    (F : Type u) [Field F] :
    leftWeylMultiplier (F := F) (n := 3) fin3_12_covBy
        ((Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3)
            (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
          Matrix.SpecialLinearGroup.transvection
            fin3_01_covBy.ne.symm (-1 : F)) =
      weylHMTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne
        (1 : Fˣ) := by
  have hZero :
      leftSimpleRootCoeff F 3
          ((Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3)
              (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
            Matrix.SpecialLinearGroup.transvection
              fin3_01_covBy.ne.symm (-1 : F)) fin3_12_covBy = 0 :=
    leftSimpleRootCoeff_weyl12_inv_mul_transvection10_neg_one F
      fin3_01_covBy fin3_12_covBy
  exact leftWeylMultiplier_of_zero fin3_12_covBy _ hZero

theorem leftWeylMultiplier_transvection12_one_mul_weyl12_inv_mul_transvection10_neg_one
    (F : Type u) [Field F] :
    leftWeylMultiplier (F := F) (n := 3) fin3_12_covBy
        (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne
            (1 : F) *
          (Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3)
              (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
          Matrix.SpecialLinearGroup.transvection
            fin3_01_covBy.ne.symm (-1 : F)) =
      (hTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne
          (-1 : Fˣ))⁻¹ := by
  have hCoeff :
      leftSimpleRootCoeff F 3
          (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne
              (1 : F) *
            (Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3)
                (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
            Matrix.SpecialLinearGroup.transvection
              fin3_01_covBy.ne.symm (-1 : F)) fin3_12_covBy = 1 :=
    leftSimpleRootCoeff_transvection12_one_mul_weyl12_inv_mul_transvection10_neg_one
      F fin3_01_covBy fin3_12_covBy
  have hNotPos :
      ¬ ((Matrix.GeneralLinearGroup.bruhatMiddle
            (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne
                (1 : F) *
              (Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3)
                  (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
              Matrix.SpecialLinearGroup.transvection
                fin3_01_covBy.ne.symm (-1 : F)) :
          MonomialBase Fˣ (Fin 3)).right.symm (1 : Fin 3) <
        (Matrix.GeneralLinearGroup.bruhatMiddle
            (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne
                (1 : F) *
              (Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3)
                  (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
              Matrix.SpecialLinearGroup.transvection
                fin3_01_covBy.ne.symm (-1 : F)) :
          MonomialBase Fˣ (Fin 3)).right.symm (2 : Fin 3)) :=
    bruhatMiddle_transvection12_one_mul_weyl12_inv_mul_transvection10_neg_one_not_pos
      F fin3_01_covBy fin3_12_covBy
  have hNe :
      leftSimpleRootCoeff F 3
          (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne
              (1 : F) *
            (Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3)
                (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
            Matrix.SpecialLinearGroup.transvection
              fin3_01_covBy.ne.symm (-1 : F)) fin3_12_covBy ≠ 0 := by
    rw [hCoeff]
    exact one_ne_zero
  have hMul :=
    leftWeylMultiplier_of_neg fin3_12_covBy _ hNe hNotPos
  have hOneNe : (1 : F) ≠ 0 := one_ne_zero
  have hUnitsEq :
      torusUnitOfNegCoeff (1 : F) hOneNe = (-1 : Fˣ) := by
    apply Units.ext
    simp [torusUnitOfNegCoeff]
  have hCoeffUnits :
      torusUnitOfNegCoeff
          (leftSimpleRootCoeff F 3
            (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne
                (1 : F) *
              (Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3)
                  (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
              Matrix.SpecialLinearGroup.transvection
                fin3_01_covBy.ne.symm (-1 : F)) fin3_12_covBy) hNe =
        (-1 : Fˣ) := by
    have hEq :
        torusUnitOfNegCoeff
            (leftSimpleRootCoeff F 3
              (Matrix.SpecialLinearGroup.transvection
                  fin3_12_covBy.ne (1 : F) *
                (Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3)
                    (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
                Matrix.SpecialLinearGroup.transvection
                  fin3_01_covBy.ne.symm (-1 : F)) fin3_12_covBy) hNe =
          torusUnitOfNegCoeff (1 : F) hOneNe := by
      apply Units.ext
      simp [torusUnitOfNegCoeff, hCoeff]
    rw [hEq, hUnitsEq]
  rw [hCoeffUnits] at hMul
  exact hMul

theorem leftLowerRootLift20_inverse_prefix_snd_X_one
    (F : Type u) [Field F] :
    X.snd
        (((leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F)).val.2 *
          (leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F)).val.2)
          (X_one F 3)) =
      (hTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne
          (-1 : Fˣ))⁻¹ *
        (weylHMTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne
            (1 : Fˣ))⁻¹ *
          ((hTits F 3 (0 : Fin 3) (1 : Fin 3) fin3_01_covBy.ne
              (-1 : Fˣ))⁻¹ *
            (weylHMTits F 3 (0 : Fin 3) (1 : Fin 3)
                fin3_01_covBy.ne (1 : Fˣ))⁻¹) := by
  let y : X F 3 :=
    (leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F)).val.2
      (X_one F 3)
  have hY_eq :
      ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F)).val.2 *
        (leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F)).val.2)
        (X_one F 3) =
      (leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F)).val.2 y := by
    simp only [Equiv.Perm.mul_apply, y]
  have hFstY :
      X.fst y =
        Matrix.SpecialLinearGroup.transvection
          fin3_01_covBy.ne.symm (-1 : F) := by
    have hFst :=
      leftLowerAdjacentRootLift_fst_apply F 3 fin3_01_covBy
        (-1 : F) (X_one F 3)
    have hOne : X.fst (X_one F 3) = 1 := X_one_fst F 3
    calc X.fst y
        = X.fst
            ((leftLowerAdjacentRootLift F 3 fin3_01_covBy
                (-1 : F)).val.2 (X_one F 3)) := rfl
      _ = Matrix.SpecialLinearGroup.transvection
            fin3_01_covBy.ne.symm (-1 : F) * X.fst (X_one F 3) := hFst
      _ = Matrix.SpecialLinearGroup.transvection
            fin3_01_covBy.ne.symm (-1 : F) := by
        rw [hOne, mul_one]
  have hSndY :
      X.snd y =
        (hTits F 3 (0 : Fin 3) (1 : Fin 3) fin3_01_covBy.ne
            (-1 : Fˣ))⁻¹ *
          (weylHMTits F 3 (0 : Fin 3) (1 : Fin 3)
              fin3_01_covBy.ne (1 : Fˣ))⁻¹ := by
    have hr : (-1 : F) ≠ 0 := neg_ne_zero.mpr one_ne_zero
    have h :=
      leftLowerAdjacentRootLift_snd_X_one_of_ne_zero F 3
        fin3_01_covBy (-1 : F) hr
    have hUnits : Units.mk0 (-1 : F) hr = (-1 : Fˣ) := by
      apply Units.ext
      simp
    rw [hUnits] at h
    calc X.snd y
        = X.snd
            ((leftLowerAdjacentRootLift F 3 fin3_01_covBy
                (-1 : F)).val.2 (X_one F 3)) := rfl
      _ = (hTits F 3 (0 : Fin 3) (1 : Fin 3) fin3_01_covBy.ne
              (-1 : Fˣ))⁻¹ *
            (weylHMTits F 3 (0 : Fin 3) (1 : Fin 3)
                fin3_01_covBy.ne (1 : Fˣ))⁻¹ := h
  have hSndApply :=
    leftLowerAdjacentRootLift_snd_apply F 3 fin3_12_covBy
      (-1 : F) y
  have hTransNeg : (-(-1 : F)) = (1 : F) := by simp
  have hWeylFst :
      (Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3)
          (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ * X.fst y =
        (Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3)
            (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
          Matrix.SpecialLinearGroup.transvection
            fin3_01_covBy.ne.symm (-1 : F) := by
    rw [hFstY]
  have hTransFst :
      Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne
          (-(-1 : F)) *
          (Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3)
              (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
          X.fst y =
        Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne
            (1 : F) *
          (Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3)
              (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
          Matrix.SpecialLinearGroup.transvection
            fin3_01_covBy.ne.symm (-1 : F) := by
    rw [hTransNeg, hFstY]
  calc X.snd
        (((leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F)).val.2 *
          (leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F)).val.2)
          (X_one F 3))
      = X.snd
          ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F)).val.2
            y) := by
        rw [hY_eq]
    _ = leftWeylMultiplier fin3_12_covBy
            (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne
                (-(-1 : F)) *
              (Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3)
                  (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
              X.fst y) *
          (leftWeylMultiplier fin3_12_covBy
              ((Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3)
                  (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
                X.fst y))⁻¹ *
          X.snd y := hSndApply
    _ = leftWeylMultiplier fin3_12_covBy
            (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne
                (1 : F) *
              (Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3)
                  (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
              Matrix.SpecialLinearGroup.transvection
                fin3_01_covBy.ne.symm (-1 : F)) *
          (leftWeylMultiplier fin3_12_covBy
              ((Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3)
                  (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
                Matrix.SpecialLinearGroup.transvection
                  fin3_01_covBy.ne.symm (-1 : F)))⁻¹ *
          X.snd y := by
        rw [hTransFst, hWeylFst]
    _ = (hTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne
            (-1 : Fˣ))⁻¹ *
          (weylHMTits F 3 (1 : Fin 3) (2 : Fin 3)
              fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
            X.snd y := by
        have hMul12 :=
          leftWeylMultiplier_transvection12_one_mul_weyl12_inv_mul_transvection10_neg_one
            (F := F)
        have hMulWeyl :=
          leftWeylMultiplier_weyl12_inv_mul_transvection10_neg_one
            (F := F)
        rw [hMul12, hMulWeyl]
    _ = (hTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne
            (-1 : Fˣ))⁻¹ *
          (weylHMTits F 3 (1 : Fin 3) (2 : Fin 3)
              fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
            ((hTits F 3 (0 : Fin 3) (1 : Fin 3) fin3_01_covBy.ne
                (-1 : Fˣ))⁻¹ *
              (weylHMTits F 3 (0 : Fin 3) (1 : Fin 3)
                  fin3_01_covBy.ne (1 : Fˣ))⁻¹) := by
        rw [hSndY, mul_assoc]

theorem leftWeylMultiplier_of_order_pos {F} [Field F] {n}
    {i j : Fin n} (hij : i ⋖ j)
    (s : Matrix.SpecialLinearGroup (Fin n) F)
    (hPos : (Matrix.GeneralLinearGroup.bruhatMiddle s :
        MonomialBase Fˣ (Fin n)).right.symm i <
      (Matrix.GeneralLinearGroup.bruhatMiddle s :
        MonomialBase Fˣ (Fin n)).right.symm j) :
    leftWeylMultiplier hij s = weylHMTits F n i j hij.ne 1 := by
  by_cases hZero : leftSimpleRootCoeff F n s hij = 0
  · exact leftWeylMultiplier_of_zero hij s hZero
  · exact leftWeylMultiplier_of_pos hij s hZero hPos

theorem leftWeylMultiplier_fin3LowerStageThree_S30
    (F : Type u) [Field F] :
    leftWeylMultiplier (F := F) (n := 3) fin3_01_covBy
        ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3)
            (1 : Fin 3) fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              fin3_12_covBy.ne.symm (-1 : F) *
            Matrix.SpecialLinearGroup.transvection
              fin3_01_covBy.ne.symm (-1 : F))) =
      weylHMTits F 3 (0 : Fin 3) (1 : Fin 3)
        fin3_01_covBy.ne 1 := by
  have hZero :
      leftSimpleRootCoeff F 3
          ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3)
              (1 : Fin 3) fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                fin3_12_covBy.ne.symm (-1 : F) *
              Matrix.SpecialLinearGroup.transvection
                fin3_01_covBy.ne.symm (-1 : F))) fin3_01_covBy = 0 :=
    leftSimpleRootCoeff_weyl01_inv_mul_transvection21_neg_one_mul_transvection10_neg_one
      F fin3_01_covBy fin3_12_covBy
  exact leftWeylMultiplier_of_zero fin3_01_covBy _ hZero

theorem leftWeylMultiplier_fin3LowerStageThree_S31
    (F : Type u) [Field F] :
    leftWeylMultiplier (F := F) (n := 3) fin3_01_covBy
        (Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne
            (-1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3)
              (1 : Fin 3) fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                fin3_12_covBy.ne.symm (-1 : F) *
              Matrix.SpecialLinearGroup.transvection
                fin3_01_covBy.ne.symm (-1 : F)))) =
      (hTits F 3 (0 : Fin 3) (1 : Fin 3) fin3_01_covBy.ne
          (1 : Fˣ))⁻¹ := by
  have hCoeff :
      leftSimpleRootCoeff F 3
          (Matrix.SpecialLinearGroup.transvection
              fin3_01_covBy.ne (-1 : F) *
            ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3)
                (1 : Fin 3) fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
              (Matrix.SpecialLinearGroup.transvection
                  fin3_12_covBy.ne.symm (-1 : F) *
                Matrix.SpecialLinearGroup.transvection
                  fin3_01_covBy.ne.symm (-1 : F)))) fin3_01_covBy =
        -1 :=
    leftSimpleRootCoeff_transvection01_neg_one_mul_weyl01_inv_mul_transvection21_10_neg_one
      F fin3_01_covBy fin3_12_covBy
  have hNotPos :
      ¬ ((Matrix.GeneralLinearGroup.bruhatMiddle
            (Matrix.SpecialLinearGroup.transvection
                fin3_01_covBy.ne (-1 : F) *
              ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3)
                  (1 : Fin 3) fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
                (Matrix.SpecialLinearGroup.transvection
                    fin3_12_covBy.ne.symm (-1 : F) *
                  Matrix.SpecialLinearGroup.transvection
                    fin3_01_covBy.ne.symm (-1 : F)))) :
          MonomialBase Fˣ (Fin 3)).right.symm (0 : Fin 3) <
        (Matrix.GeneralLinearGroup.bruhatMiddle
            (Matrix.SpecialLinearGroup.transvection
                fin3_01_covBy.ne (-1 : F) *
              ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3)
                  (1 : Fin 3) fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
                (Matrix.SpecialLinearGroup.transvection
                    fin3_12_covBy.ne.symm (-1 : F) *
                  Matrix.SpecialLinearGroup.transvection
                    fin3_01_covBy.ne.symm (-1 : F)))) :
          MonomialBase Fˣ (Fin 3)).right.symm (1 : Fin 3)) := by
    have hEq :
        Matrix.SpecialLinearGroup.transvection
            fin3_01_covBy.ne (-1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3)
              (1 : Fin 3) fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                fin3_12_covBy.ne.symm (-1 : F) *
              Matrix.SpecialLinearGroup.transvection
                fin3_01_covBy.ne.symm (-1 : F))) =
        Matrix.SpecialLinearGroup.transvection
            fin3_01_covBy.ne (-1 : F) *
          (Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3)
              (1 : Fin 3) fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
          Matrix.SpecialLinearGroup.transvection
            fin3_12_covBy.ne.symm (-1 : F) *
          Matrix.SpecialLinearGroup.transvection
            fin3_01_covBy.ne.symm (-1 : F) := by
      simp only [mul_assoc]
    have hNotPos' :
        ¬ ((Matrix.GeneralLinearGroup.bruhatMiddle
              (Matrix.SpecialLinearGroup.transvection
                  fin3_01_covBy.ne (-1 : F) *
                (Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3)
                    (1 : Fin 3) fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
                Matrix.SpecialLinearGroup.transvection
                  fin3_12_covBy.ne.symm (-1 : F) *
                Matrix.SpecialLinearGroup.transvection
                  fin3_01_covBy.ne.symm (-1 : F)) :
            MonomialBase Fˣ (Fin 3)).right.symm (0 : Fin 3) <
          (Matrix.GeneralLinearGroup.bruhatMiddle
              (Matrix.SpecialLinearGroup.transvection
                  fin3_01_covBy.ne (-1 : F) *
                (Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3)
                    (1 : Fin 3) fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
                Matrix.SpecialLinearGroup.transvection
                  fin3_12_covBy.ne.symm (-1 : F) *
                Matrix.SpecialLinearGroup.transvection
                  fin3_01_covBy.ne.symm (-1 : F)) :
            MonomialBase Fˣ (Fin 3)).right.symm (1 : Fin 3)) :=
      bruhatMiddle_transvection01_neg_one_mul_weyl01_inv_mul_transvection21_10_neg_one_not_pos
        F fin3_01_covBy fin3_12_covBy
    rw [← hEq] at hNotPos'
    exact hNotPos'
  have hNe :
      leftSimpleRootCoeff F 3
          (Matrix.SpecialLinearGroup.transvection
              fin3_01_covBy.ne (-1 : F) *
            ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3)
                (1 : Fin 3) fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
              (Matrix.SpecialLinearGroup.transvection
                  fin3_12_covBy.ne.symm (-1 : F) *
                Matrix.SpecialLinearGroup.transvection
                  fin3_01_covBy.ne.symm (-1 : F)))) fin3_01_covBy ≠
        0 := by
    rw [hCoeff]
    exact neg_ne_zero.mpr one_ne_zero
  have hMul :=
    leftWeylMultiplier_of_neg fin3_01_covBy _ hNe hNotPos
  have hOneNe : (-1 : F) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have hUnitsEq :
      torusUnitOfNegCoeff (-1 : F) hOneNe = (1 : Fˣ) := by
    apply Units.ext
    simp [torusUnitOfNegCoeff]
  have hCoeffUnits :
      torusUnitOfNegCoeff
          (leftSimpleRootCoeff F 3
            (Matrix.SpecialLinearGroup.transvection
                fin3_01_covBy.ne (-1 : F) *
              ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3)
                  (1 : Fin 3) fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
                (Matrix.SpecialLinearGroup.transvection
                    fin3_12_covBy.ne.symm (-1 : F) *
                  Matrix.SpecialLinearGroup.transvection
                    fin3_01_covBy.ne.symm (-1 : F)))) fin3_01_covBy)
          hNe =
        (1 : Fˣ) := by
    have hEq :
        torusUnitOfNegCoeff
            (leftSimpleRootCoeff F 3
              (Matrix.SpecialLinearGroup.transvection
                  fin3_01_covBy.ne (-1 : F) *
                ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3)
                    (1 : Fin 3) fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
                  (Matrix.SpecialLinearGroup.transvection
                      fin3_12_covBy.ne.symm (-1 : F) *
                    Matrix.SpecialLinearGroup.transvection
                      fin3_01_covBy.ne.symm (-1 : F)))) fin3_01_covBy)
            hNe =
          torusUnitOfNegCoeff (-1 : F) hOneNe := by
      apply Units.ext
      simp [torusUnitOfNegCoeff, hCoeff]
    rw [hEq, hUnitsEq]
  rw [hCoeffUnits] at hMul
  exact hMul

theorem leftWeylMultiplier_fin3LowerStageFour_S40
    (F : Type u) [Field F] :
    leftWeylMultiplier (F := F) (n := 3) fin3_12_covBy
        ((Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3)
            (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              fin3_01_covBy.ne.symm (1 : F) *
            Matrix.SpecialLinearGroup.transvection
              fin3_12_covBy.ne.symm (-1 : F) *
            Matrix.SpecialLinearGroup.transvection
              fin3_01_covBy.ne.symm (-1 : F))) =
      weylHMTits F 3 (1 : Fin 3) (2 : Fin 3)
        fin3_12_covBy.ne 1 := by
  have hPos :
      (Matrix.GeneralLinearGroup.bruhatMiddle
          ((Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3)
              (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                fin3_01_covBy.ne.symm (1 : F) *
              Matrix.SpecialLinearGroup.transvection
                fin3_12_covBy.ne.symm (-1 : F) *
              Matrix.SpecialLinearGroup.transvection
                fin3_01_covBy.ne.symm (-1 : F))) :
        MonomialBase Fˣ (Fin 3)).right.symm (1 : Fin 3) <
      (Matrix.GeneralLinearGroup.bruhatMiddle
          ((Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3)
              (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                fin3_01_covBy.ne.symm (1 : F) *
              Matrix.SpecialLinearGroup.transvection
                fin3_12_covBy.ne.symm (-1 : F) *
              Matrix.SpecialLinearGroup.transvection
                fin3_01_covBy.ne.symm (-1 : F))) :
        MonomialBase Fˣ (Fin 3)).right.symm (2 : Fin 3) :=
    bruhatMiddle_weyl12_inv_transvection10_1_transvection21_neg1_transvection10_neg1_pos
      F fin3_01_covBy fin3_12_covBy
  exact leftWeylMultiplier_of_order_pos fin3_12_covBy _ hPos

theorem leftWeylMultiplier_fin3LowerStageFour_S41
    (F : Type u) [Field F] :
    leftWeylMultiplier (F := F) (n := 3) fin3_12_covBy
        (Matrix.SpecialLinearGroup.transvection
            fin3_12_covBy.ne (-1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3)
              (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                fin3_01_covBy.ne.symm (1 : F) *
              Matrix.SpecialLinearGroup.transvection
                fin3_12_covBy.ne.symm (-1 : F) *
              Matrix.SpecialLinearGroup.transvection
                fin3_01_covBy.ne.symm (-1 : F)))) =
      weylHMTits F 3 (1 : Fin 3) (2 : Fin 3)
        fin3_12_covBy.ne 1 := by
  have hPos :
      (Matrix.GeneralLinearGroup.bruhatMiddle
          (Matrix.SpecialLinearGroup.transvection
              fin3_12_covBy.ne (-1 : F) *
            ((Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3)
                (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
              (Matrix.SpecialLinearGroup.transvection
                  fin3_01_covBy.ne.symm (1 : F) *
                Matrix.SpecialLinearGroup.transvection
                  fin3_12_covBy.ne.symm (-1 : F) *
                Matrix.SpecialLinearGroup.transvection
                  fin3_01_covBy.ne.symm (-1 : F)))) :
        MonomialBase Fˣ (Fin 3)).right.symm (1 : Fin 3) <
      (Matrix.GeneralLinearGroup.bruhatMiddle
          (Matrix.SpecialLinearGroup.transvection
              fin3_12_covBy.ne (-1 : F) *
            ((Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3)
                (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
              (Matrix.SpecialLinearGroup.transvection
                  fin3_01_covBy.ne.symm (1 : F) *
                Matrix.SpecialLinearGroup.transvection
                  fin3_12_covBy.ne.symm (-1 : F) *
                Matrix.SpecialLinearGroup.transvection
                  fin3_01_covBy.ne.symm (-1 : F)))) :
        MonomialBase Fˣ (Fin 3)).right.symm (2 : Fin 3) :=
    bruhatMiddle_T12_neg1_w12_inv_transvection10_1_transvection21_neg1_transvection10_neg1_pos
      F fin3_01_covBy fin3_12_covBy
  exact leftWeylMultiplier_of_order_pos fin3_12_covBy _ hPos

theorem leftLowerRootLift20_snd_X_one (F : Type u) [Field F] :
    X.snd ((leftLowerRootLift20 F (1 : F)).val.2 (X_one F 3)) =
      (hTits F 3 (0 : Fin 3) (1 : Fin 3) fin3_01_covBy.ne
          (1 : Fˣ))⁻¹ *
        (weylHMTits F 3 (0 : Fin 3) (1 : Fin 3)
            fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
          ((hTits F 3 (1 : Fin 3) (2 : Fin 3)
              fin3_12_covBy.ne (-1 : Fˣ))⁻¹ *
            (weylHMTits F 3 (1 : Fin 3) (2 : Fin 3)
                fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
              ((hTits F 3 (0 : Fin 3) (1 : Fin 3)
                  fin3_01_covBy.ne (-1 : Fˣ))⁻¹ *
                (weylHMTits F 3 (0 : Fin 3) (1 : Fin 3)
                    fin3_01_covBy.ne (1 : Fˣ))⁻¹)) := by
  have hComm :
      leftLowerRootLift20 F (1 : F) =
        leftLowerAdjacentRootLift F 3 fin3_12_covBy (1 : F) *
          leftLowerAdjacentRootLift F 3 fin3_01_covBy (1 : F) *
            (leftLowerAdjacentRootLift F 3 fin3_12_covBy
                (1 : F))⁻¹ *
              (leftLowerAdjacentRootLift F 3 fin3_01_covBy
                  (1 : F))⁻¹ := by
    unfold leftLowerRootLift20 leftLowerTwoStepRootLift
    simp [commutatorElement_def]
  have hNeg12 :
      leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F) =
        (leftLowerAdjacentRootLift F 3 fin3_12_covBy
            (1 : F))⁻¹ := by
    have h :=
      leftLowerAdjacentRootLift_neg (F := F) (n := 3)
        fin3_12_covBy (1 : F)
    have hNegOne : (-(1 : F)) = (-1 : F) := by simp
    rw [hNegOne] at h
    exact h
  have hNeg01 :
      leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F) =
        (leftLowerAdjacentRootLift F 3 fin3_01_covBy
            (1 : F))⁻¹ := by
    have h :=
      leftLowerAdjacentRootLift_neg (F := F) (n := 3)
        fin3_01_covBy (1 : F)
    have hNegOne : (-(1 : F)) = (-1 : F) := by simp
    rw [hNegOne] at h
    exact h
  have hEq :
      leftLowerRootLift20 F (1 : F) =
        leftLowerAdjacentRootLift F 3 fin3_12_covBy (1 : F) *
          leftLowerAdjacentRootLift F 3 fin3_01_covBy (1 : F) *
            leftLowerAdjacentRootLift F 3 fin3_12_covBy
              (-1 : F) *
              leftLowerAdjacentRootLift F 3 fin3_01_covBy
                (-1 : F) := by
    calc leftLowerRootLift20 F (1 : F)
        = leftLowerAdjacentRootLift F 3 fin3_12_covBy (1 : F) *
            leftLowerAdjacentRootLift F 3 fin3_01_covBy (1 : F) *
              (leftLowerAdjacentRootLift F 3 fin3_12_covBy
                  (1 : F))⁻¹ *
                (leftLowerAdjacentRootLift F 3 fin3_01_covBy
                    (1 : F))⁻¹ := hComm
      _ = leftLowerAdjacentRootLift F 3 fin3_12_covBy (1 : F) *
            leftLowerAdjacentRootLift F 3 fin3_01_covBy (1 : F) *
              leftLowerAdjacentRootLift F 3 fin3_12_covBy
                (-1 : F) *
                leftLowerAdjacentRootLift F 3 fin3_01_covBy
                  (-1 : F) := by
          rw [← hNeg12, ← hNeg01]
  let y1 : X F 3 :=
    (leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F)).val.2
      (X_one F 3)
  let y2 : X F 3 :=
    (leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F)).val.2 y1
  let y3 : X F 3 :=
    (leftLowerAdjacentRootLift F 3 fin3_01_covBy (1 : F)).val.2 y2
  let y4 : X F 3 :=
    (leftLowerAdjacentRootLift F 3 fin3_12_covBy (1 : F)).val.2 y3
  have hFstY1 :
      X.fst y1 =
        Matrix.SpecialLinearGroup.transvection
          fin3_01_covBy.ne.symm (-1 : F) := by
    have hFst :=
      leftLowerAdjacentRootLift_fst_apply F 3 fin3_01_covBy
        (-1 : F) (X_one F 3)
    have hOne : X.fst (X_one F 3) = 1 := X_one_fst F 3
    calc X.fst y1
        = X.fst
            ((leftLowerAdjacentRootLift F 3 fin3_01_covBy
                (-1 : F)).val.2 (X_one F 3)) := rfl
      _ = Matrix.SpecialLinearGroup.transvection
            fin3_01_covBy.ne.symm (-1 : F) * X.fst (X_one F 3) := hFst
      _ = Matrix.SpecialLinearGroup.transvection
            fin3_01_covBy.ne.symm (-1 : F) := by
        rw [hOne, mul_one]
  have hSndY1 :
      X.snd y1 =
        (hTits F 3 (0 : Fin 3) (1 : Fin 3) fin3_01_covBy.ne
            (-1 : Fˣ))⁻¹ *
          (weylHMTits F 3 (0 : Fin 3) (1 : Fin 3)
              fin3_01_covBy.ne (1 : Fˣ))⁻¹ := by
    have hr : (-1 : F) ≠ 0 := neg_ne_zero.mpr one_ne_zero
    have h :=
      leftLowerAdjacentRootLift_snd_X_one_of_ne_zero F 3
        fin3_01_covBy (-1 : F) hr
    have hUnits : Units.mk0 (-1 : F) hr = (-1 : Fˣ) := by
      apply Units.ext
      simp
    rw [hUnits] at h
    calc X.snd y1
        = X.snd
            ((leftLowerAdjacentRootLift F 3 fin3_01_covBy
                (-1 : F)).val.2 (X_one F 3)) := rfl
      _ = (hTits F 3 (0 : Fin 3) (1 : Fin 3) fin3_01_covBy.ne
              (-1 : Fˣ))⁻¹ *
            (weylHMTits F 3 (0 : Fin 3) (1 : Fin 3)
                fin3_01_covBy.ne (1 : Fˣ))⁻¹ := h
  have hFstY2 :
      X.fst y2 =
        Matrix.SpecialLinearGroup.transvection
            fin3_12_covBy.ne.symm (-1 : F) *
          Matrix.SpecialLinearGroup.transvection
            fin3_01_covBy.ne.symm (-1 : F) := by
    have hFst :=
      leftLowerAdjacentRootLift_fst_apply F 3 fin3_12_covBy
        (-1 : F) y1
    calc X.fst y2
        = X.fst
            ((leftLowerAdjacentRootLift F 3 fin3_12_covBy
                (-1 : F)).val.2 y1) := rfl
      _ = Matrix.SpecialLinearGroup.transvection
            fin3_12_covBy.ne.symm (-1 : F) * X.fst y1 := hFst
      _ = Matrix.SpecialLinearGroup.transvection
            fin3_12_covBy.ne.symm (-1 : F) *
          Matrix.SpecialLinearGroup.transvection
            fin3_01_covBy.ne.symm (-1 : F) := by
        rw [hFstY1]
  have hSndY2 :
      X.snd y2 =
        (hTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne
            (-1 : Fˣ))⁻¹ *
          (weylHMTits F 3 (1 : Fin 3) (2 : Fin 3)
              fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
            ((hTits F 3 (0 : Fin 3) (1 : Fin 3)
                fin3_01_covBy.ne (-1 : Fˣ))⁻¹ *
              (weylHMTits F 3 (0 : Fin 3) (1 : Fin 3)
                  fin3_01_covBy.ne (1 : Fˣ))⁻¹) := by
    have hSndY2' :=
      leftLowerRootLift20_inverse_prefix_snd_X_one (F := F)
    have hY2Eq :
        y2 =
          ((leftLowerAdjacentRootLift F 3 fin3_12_covBy
                (-1 : F)).val.2 *
            (leftLowerAdjacentRootLift F 3 fin3_01_covBy
                (-1 : F)).val.2) (X_one F 3) := by
      simp only [Equiv.Perm.mul_apply, y1, y2]
    calc X.snd y2
        = X.snd
            (((leftLowerAdjacentRootLift F 3 fin3_12_covBy
                  (-1 : F)).val.2 *
              (leftLowerAdjacentRootLift F 3 fin3_01_covBy
                  (-1 : F)).val.2) (X_one F 3)) := by
          rw [← hY2Eq]
      _ = (hTits F 3 (1 : Fin 3) (2 : Fin 3)
              fin3_12_covBy.ne (-1 : Fˣ))⁻¹ *
            (weylHMTits F 3 (1 : Fin 3) (2 : Fin 3)
                fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
              ((hTits F 3 (0 : Fin 3) (1 : Fin 3)
                  fin3_01_covBy.ne (-1 : Fˣ))⁻¹ *
                (weylHMTits F 3 (0 : Fin 3) (1 : Fin 3)
                    fin3_01_covBy.ne (1 : Fˣ))⁻¹) := hSndY2'
  have hFstY3 :
      X.fst y3 =
        Matrix.SpecialLinearGroup.transvection
            fin3_01_covBy.ne.symm (1 : F) *
          Matrix.SpecialLinearGroup.transvection
            fin3_12_covBy.ne.symm (-1 : F) *
          Matrix.SpecialLinearGroup.transvection
            fin3_01_covBy.ne.symm (-1 : F) := by
    have hFst :=
      leftLowerAdjacentRootLift_fst_apply F 3 fin3_01_covBy
        (1 : F) y2
    calc X.fst y3
        = X.fst
            ((leftLowerAdjacentRootLift F 3 fin3_01_covBy
                (1 : F)).val.2 y2) := rfl
      _ = Matrix.SpecialLinearGroup.transvection
            fin3_01_covBy.ne.symm (1 : F) * X.fst y2 := hFst
      _ = Matrix.SpecialLinearGroup.transvection
            fin3_01_covBy.ne.symm (1 : F) *
          (Matrix.SpecialLinearGroup.transvection
              fin3_12_covBy.ne.symm (-1 : F) *
            Matrix.SpecialLinearGroup.transvection
              fin3_01_covBy.ne.symm (-1 : F)) := by
        rw [hFstY2]
      _ = Matrix.SpecialLinearGroup.transvection
            fin3_01_covBy.ne.symm (1 : F) *
          Matrix.SpecialLinearGroup.transvection
            fin3_12_covBy.ne.symm (-1 : F) *
          Matrix.SpecialLinearGroup.transvection
            fin3_01_covBy.ne.symm (-1 : F) := by
        rw [← mul_assoc]
  have hSndY3 :
      X.snd y3 =
        (hTits F 3 (0 : Fin 3) (1 : Fin 3) fin3_01_covBy.ne
            (1 : Fˣ))⁻¹ *
          (weylHMTits F 3 (0 : Fin 3) (1 : Fin 3)
              fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
            X.snd y2 := by
    have hSndApply :=
      leftLowerAdjacentRootLift_snd_apply F 3 fin3_01_covBy
        (1 : F) y2
    have hTransNeg : (-(1 : F)) = (-1 : F) := by simp
    have hWeylFst :
        (Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3)
            (1 : Fin 3) fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
          X.fst y2 =
        (Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3)
            (1 : Fin 3) fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              fin3_12_covBy.ne.symm (-1 : F) *
            Matrix.SpecialLinearGroup.transvection
              fin3_01_covBy.ne.symm (-1 : F)) := by
      rw [hFstY2]
    have hTransFst :
        Matrix.SpecialLinearGroup.transvection
            fin3_01_covBy.ne (-(1 : F)) *
          (Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3)
              (1 : Fin 3) fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
          X.fst y2 =
        Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne
            (-1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3)
              (1 : Fin 3) fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                fin3_12_covBy.ne.symm (-1 : F) *
              Matrix.SpecialLinearGroup.transvection
                fin3_01_covBy.ne.symm (-1 : F))) := by
      rw [hTransNeg, hFstY2, mul_assoc]
    calc X.snd y3
        = X.snd
            ((leftLowerAdjacentRootLift F 3 fin3_01_covBy
                (1 : F)).val.2 y2) := rfl
      _ = leftWeylMultiplier fin3_01_covBy
              (Matrix.SpecialLinearGroup.transvection
                  fin3_01_covBy.ne (-(1 : F)) *
                (Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3)
                    (1 : Fin 3) fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
                X.fst y2) *
            (leftWeylMultiplier fin3_01_covBy
                ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3)
                    (1 : Fin 3) fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
                  X.fst y2))⁻¹ *
            X.snd y2 := hSndApply
      _ = leftWeylMultiplier fin3_01_covBy
              (Matrix.SpecialLinearGroup.transvection
                  fin3_01_covBy.ne (-1 : F) *
                ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3)
                    (1 : Fin 3) fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
                  (Matrix.SpecialLinearGroup.transvection
                      fin3_12_covBy.ne.symm (-1 : F) *
                    Matrix.SpecialLinearGroup.transvection
                      fin3_01_covBy.ne.symm (-1 : F)))) *
            (leftWeylMultiplier fin3_01_covBy
                ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3)
                    (1 : Fin 3) fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
                  (Matrix.SpecialLinearGroup.transvection
                      fin3_12_covBy.ne.symm (-1 : F) *
                    Matrix.SpecialLinearGroup.transvection
                      fin3_01_covBy.ne.symm (-1 : F))))⁻¹ *
            X.snd y2 := by
          rw [hTransFst, hWeylFst]
      _ = (hTits F 3 (0 : Fin 3) (1 : Fin 3)
              fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
            (weylHMTits F 3 (0 : Fin 3) (1 : Fin 3)
                fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
              X.snd y2 := by
          have hMul31 :=
            leftWeylMultiplier_fin3LowerStageThree_S31 (F := F)
          have hMul30 :=
            leftWeylMultiplier_fin3LowerStageThree_S30 (F := F)
          rw [hMul31, hMul30]
  have hSndY4 :
      X.snd y4 = X.snd y3 := by
    have hSndApply :=
      leftLowerAdjacentRootLift_snd_apply F 3 fin3_12_covBy
        (1 : F) y3
    have hTransNeg : (-(1 : F)) = (-1 : F) := by simp
    have hWeylFst :
        (Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3)
            (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
          X.fst y3 =
        (Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3)
            (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              fin3_01_covBy.ne.symm (1 : F) *
            Matrix.SpecialLinearGroup.transvection
              fin3_12_covBy.ne.symm (-1 : F) *
            Matrix.SpecialLinearGroup.transvection
              fin3_01_covBy.ne.symm (-1 : F)) := by
      rw [hFstY3]
    have hTransFst :
        Matrix.SpecialLinearGroup.transvection
            fin3_12_covBy.ne (-(1 : F)) *
          (Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3)
              (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
          X.fst y3 =
        Matrix.SpecialLinearGroup.transvection
            fin3_12_covBy.ne (-1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3)
              (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                fin3_01_covBy.ne.symm (1 : F) *
              Matrix.SpecialLinearGroup.transvection
                fin3_12_covBy.ne.symm (-1 : F) *
              Matrix.SpecialLinearGroup.transvection
                fin3_01_covBy.ne.symm (-1 : F))) := by
      rw [hTransNeg, hFstY3, mul_assoc]
    calc X.snd y4
        = X.snd
            ((leftLowerAdjacentRootLift F 3 fin3_12_covBy
                (1 : F)).val.2 y3) := rfl
      _ = leftWeylMultiplier fin3_12_covBy
              (Matrix.SpecialLinearGroup.transvection
                  fin3_12_covBy.ne (-(1 : F)) *
                (Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3)
                    (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
                X.fst y3) *
            (leftWeylMultiplier fin3_12_covBy
                ((Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3)
                    (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
                  X.fst y3))⁻¹ *
            X.snd y3 := hSndApply
      _ = leftWeylMultiplier fin3_12_covBy
              (Matrix.SpecialLinearGroup.transvection
                  fin3_12_covBy.ne (-1 : F) *
                ((Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3)
                    (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
                  (Matrix.SpecialLinearGroup.transvection
                      fin3_01_covBy.ne.symm (1 : F) *
                    Matrix.SpecialLinearGroup.transvection
                      fin3_12_covBy.ne.symm (-1 : F) *
                    Matrix.SpecialLinearGroup.transvection
                      fin3_01_covBy.ne.symm (-1 : F)))) *
            (leftWeylMultiplier fin3_12_covBy
                ((Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3)
                    (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
                  (Matrix.SpecialLinearGroup.transvection
                      fin3_01_covBy.ne.symm (1 : F) *
                    Matrix.SpecialLinearGroup.transvection
                      fin3_12_covBy.ne.symm (-1 : F) *
                    Matrix.SpecialLinearGroup.transvection
                      fin3_01_covBy.ne.symm (-1 : F))))⁻¹ *
            X.snd y3 := by
          rw [hTransFst, hWeylFst]
      _ = weylHMTits F 3 (1 : Fin 3) (2 : Fin 3)
              fin3_12_covBy.ne (1 : Fˣ) *
            (weylHMTits F 3 (1 : Fin 3) (2 : Fin 3)
                fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
              X.snd y3 := by
          have hMul41 :=
            leftWeylMultiplier_fin3LowerStageFour_S41 (F := F)
          have hMul40 :=
            leftWeylMultiplier_fin3LowerStageFour_S40 (F := F)
          rw [hMul41, hMul40]
      _ = X.snd y3 := by
          rw [mul_inv_cancel, one_mul]
  have hPoint :
      ((leftLowerRootLift20 F (1 : F)).val.2 (X_one F 3)) = y4 := by
    calc ((leftLowerRootLift20 F (1 : F)).val.2 (X_one F 3))
        = ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (1 : F) *
            leftLowerAdjacentRootLift F 3 fin3_01_covBy (1 : F) *
            leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F) *
            leftLowerAdjacentRootLift F 3 fin3_01_covBy
              (-1 : F)).val.2 (X_one F 3)) := by
          rw [hEq]
      _ = ((leftLowerAdjacentRootLift F 3 fin3_12_covBy
                (1 : F)).val.2 *
            (leftLowerAdjacentRootLift F 3 fin3_01_covBy
                (1 : F)).val.2 *
              (leftLowerAdjacentRootLift F 3 fin3_12_covBy
                  (-1 : F)).val.2 *
                (leftLowerAdjacentRootLift F 3 fin3_01_covBy
                    (-1 : F)).val.2) (X_one F 3) := by
          rfl
      _ = y4 := by
          simp only [Equiv.Perm.mul_apply, y1, y2, y3, y4]
  calc X.snd ((leftLowerRootLift20 F (1 : F)).val.2 (X_one F 3))
      = X.snd y4 := by
        rw [hPoint]
    _ = X.snd y3 := hSndY4
    _ = (hTits F 3 (0 : Fin 3) (1 : Fin 3) fin3_01_covBy.ne
            (1 : Fˣ))⁻¹ *
          (weylHMTits F 3 (0 : Fin 3) (1 : Fin 3)
              fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
            X.snd y2 := hSndY3
    _ = (hTits F 3 (0 : Fin 3) (1 : Fin 3) fin3_01_covBy.ne
            (1 : Fˣ))⁻¹ *
          (weylHMTits F 3 (0 : Fin 3) (1 : Fin 3)
              fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
            ((hTits F 3 (1 : Fin 3) (2 : Fin 3)
                fin3_12_covBy.ne (-1 : Fˣ))⁻¹ *
              (weylHMTits F 3 (1 : Fin 3) (2 : Fin 3)
                  fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
                ((hTits F 3 (0 : Fin 3) (1 : Fin 3)
                    fin3_01_covBy.ne (-1 : Fˣ))⁻¹ *
                  (weylHMTits F 3 (0 : Fin 3) (1 : Fin 3)
                      fin3_01_covBy.ne (1 : Fˣ))⁻¹)) := by
        rw [hSndY2, mul_assoc]

section G01Commutator

theorem leftWeylMultiplier_G01_s0
    (F : Type u) [Field F] (a : F) :
    leftWeylMultiplier (F := F) (n := 3) fin3_12_covBy
        ((Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              (show (0 : Fin 3) ≠ 2 by decide) (-a) *
            Matrix.SpecialLinearGroup.transvection
              (show (2 : Fin 3) ≠ 1 by decide) (-1 : F))) =
      (hTits F 3 (1 : Fin 3) (2 : Fin 3)
          fin3_12_covBy.ne (-1 : Fˣ))⁻¹ := by
  have hCoeff :
      leftSimpleRootCoeff F 3
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                (show (0 : Fin 3) ≠ 2 by decide) (-a) *
              Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 1 by decide) (-1 : F)))
          fin3_12_covBy = 1 :=
    leftSimpleRootCoeff_G01_s0 F a fin3_01_covBy fin3_12_covBy
  have hNotPos :
      ¬ ((Matrix.GeneralLinearGroup.bruhatMiddle
            ((Matrix.GeneralLinearGroup.weylSLUnit
                (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
              (Matrix.SpecialLinearGroup.transvection
                  (show (0 : Fin 3) ≠ 2 by decide) (-a) *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 1 by decide) (-1 : F))) :
          MonomialBase Fˣ (Fin 3)).right.symm (1 : Fin 3) <
        (Matrix.GeneralLinearGroup.bruhatMiddle
            ((Matrix.GeneralLinearGroup.weylSLUnit
                (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
              (Matrix.SpecialLinearGroup.transvection
                  (show (0 : Fin 3) ≠ 2 by decide) (-a) *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 1 by decide) (-1 : F))) :
          MonomialBase Fˣ (Fin 3)).right.symm (2 : Fin 3)) :=
    bruhatMiddle_G01_s0_not_pos F a fin3_01_covBy fin3_12_covBy
  have hNe :
      leftSimpleRootCoeff F 3
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                (show (0 : Fin 3) ≠ 2 by decide) (-a) *
              Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 1 by decide) (-1 : F)))
          fin3_12_covBy ≠ 0 := by
    rw [hCoeff]
    exact one_ne_zero
  have hMul :=
    leftWeylMultiplier_of_neg fin3_12_covBy
      ((Matrix.GeneralLinearGroup.weylSLUnit
          (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
        (Matrix.SpecialLinearGroup.transvection
            (show (0 : Fin 3) ≠ 2 by decide) (-a) *
          Matrix.SpecialLinearGroup.transvection
            (show (2 : Fin 3) ≠ 1 by decide) (-1 : F)))
      hNe hNotPos
  have hOneNe : (1 : F) ≠ 0 := one_ne_zero
  have hUnitsEq :
      torusUnitOfNegCoeff (1 : F) hOneNe = (-1 : Fˣ) := by
    apply Units.ext
    simp [torusUnitOfNegCoeff]
  have hCoeffUnits :
      torusUnitOfNegCoeff
          (leftSimpleRootCoeff F 3
            ((Matrix.GeneralLinearGroup.weylSLUnit
                (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
              (Matrix.SpecialLinearGroup.transvection
                  (show (0 : Fin 3) ≠ 2 by decide) (-a) *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 1 by decide) (-1 : F)))
            fin3_12_covBy) hNe = (-1 : Fˣ) := by
    have hEq :
        torusUnitOfNegCoeff
            (leftSimpleRootCoeff F 3
              ((Matrix.GeneralLinearGroup.weylSLUnit
                  (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
                (Matrix.SpecialLinearGroup.transvection
                    (show (0 : Fin 3) ≠ 2 by decide) (-a) *
                  Matrix.SpecialLinearGroup.transvection
                    (show (2 : Fin 3) ≠ 1 by decide) (-1 : F)))
              fin3_12_covBy) hNe =
          torusUnitOfNegCoeff (1 : F) hOneNe := by
      apply Units.ext
      simp [torusUnitOfNegCoeff, hCoeff]
    rw [hEq, hUnitsEq]
  rw [hCoeffUnits] at hMul
  exact hMul

theorem leftWeylMultiplier_G01_s1
    (F : Type u) [Field F] (a : F) :
    leftWeylMultiplier (F := F) (n := 3) fin3_12_covBy
        (Matrix.SpecialLinearGroup.transvection
            (show (1 : Fin 3) ≠ 2 by decide) (-1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                (show (0 : Fin 3) ≠ 2 by decide) (-a) *
              Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 1 by decide) (-1 : F)))) =
      weylHMTits F 3 (1 : Fin 3) (2 : Fin 3)
        fin3_12_covBy.ne (1 : Fˣ) := by
  have hZero :
      leftSimpleRootCoeff F 3
          (Matrix.SpecialLinearGroup.transvection
              (show (1 : Fin 3) ≠ 2 by decide) (-1 : F) *
            ((Matrix.GeneralLinearGroup.weylSLUnit
                (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
              (Matrix.SpecialLinearGroup.transvection
                  (show (0 : Fin 3) ≠ 2 by decide) (-a) *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 1 by decide) (-1 : F))))
          fin3_12_covBy = 0 :=
    leftSimpleRootCoeff_G01_s1 F a fin3_01_covBy fin3_12_covBy
  exact leftWeylMultiplier_of_zero fin3_12_covBy _ hZero

theorem G01_commutator_proj
    (F : Type u) [Field F] (a : F) :
    leftExtensionProjHom F 3
        ⁅leftUpperRootLift F 3 0 2 (by decide) a,
          leftLowerAdjacentRootLift F 3 fin3_12_covBy (1 : F)⁆ =
      Matrix.SpecialLinearGroup.transvection
        (show (0 : Fin 3) ≠ 1 by decide) a := by
  rw [map_commutatorElement]
  simp only [leftExtensionProjHom_leftUpperRootLift,
    leftExtensionProjHom_leftLowerAdjacentRootLift]
  apply Matrix.SpecialLinearGroup.toGL_injective
  calc Matrix.SpecialLinearGroup.toGL
          ⁅Matrix.SpecialLinearGroup.transvection
              (show (0 : Fin 3) ≠ 2 by decide) a,
            Matrix.SpecialLinearGroup.transvection
              (show (2 : Fin 3) ≠ 1 by decide) (1 : F)⁆
      = ⁅Matrix.SpecialLinearGroup.toGL
            (Matrix.SpecialLinearGroup.transvection
              (show (0 : Fin 3) ≠ 2 by decide) a),
          Matrix.SpecialLinearGroup.toGL
            (Matrix.SpecialLinearGroup.transvection
              (show (2 : Fin 3) ≠ 1 by decide) (1 : F))⁆ := by
        rw [map_commutatorElement]
    _ = ⁅Matrix.GeneralLinearGroup.elementary
            (0 : Fin 3) (2 : Fin 3) (by decide) a,
          Matrix.GeneralLinearGroup.elementary
            (2 : Fin 3) (1 : Fin 3) (by decide) (1 : F)⁆ := by
        have h02 :
            Matrix.SpecialLinearGroup.toGL
                (Matrix.SpecialLinearGroup.transvection
                  (show (0 : Fin 3) ≠ 2 by decide) a) =
              Matrix.GeneralLinearGroup.elementary
                (0 : Fin 3) (2 : Fin 3) (by decide) a := by
          apply Units.ext
          simp [Matrix.SpecialLinearGroup.transvection_coe,
            Matrix.GeneralLinearGroup.coe_elementary]
        have h21 :
            Matrix.SpecialLinearGroup.toGL
                (Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 1 by decide) (1 : F)) =
              Matrix.GeneralLinearGroup.elementary
                (2 : Fin 3) (1 : Fin 3) (by decide) (1 : F) := by
          apply Units.ext
          simp [Matrix.SpecialLinearGroup.transvection_coe,
            Matrix.GeneralLinearGroup.coe_elementary]
        rw [h02, h21]
    _ = Matrix.GeneralLinearGroup.elementary
            (0 : Fin 3) (1 : Fin 3) (by decide) a := by
        have hElem :=
          Matrix.GeneralLinearGroup.commutatorElement_elementary
            (0 : Fin 3) (1 : Fin 3) (2 : Fin 3)
            (by decide) (by decide) (by decide) a (1 : F)
        simpa [mul_one] using hElem
    _ = Matrix.SpecialLinearGroup.toGL
            (Matrix.SpecialLinearGroup.transvection
              (show (0 : Fin 3) ≠ 1 by decide) a) := by
        apply Units.ext
        simp [Matrix.SpecialLinearGroup.transvection_coe,
          Matrix.GeneralLinearGroup.coe_elementary]

theorem G01_commutator_snd_X_one
    (F : Type u) [Field F] (a : F) :
    X.snd
        (⁅leftUpperRootLift F 3 0 2 (by decide) a,
          leftLowerAdjacentRootLift F 3 fin3_12_covBy (1 : F)⁆.val.2
          (X_one F 3)) = 1 := by
  have hCommDef :
      ⁅leftUpperRootLift F 3 0 2 (by decide) a,
        leftLowerAdjacentRootLift F 3 fin3_12_covBy (1 : F)⁆ =
        leftUpperRootLift F 3 0 2 (by decide) a *
          leftLowerAdjacentRootLift F 3 fin3_12_covBy (1 : F) *
            (leftUpperRootLift F 3 0 2 (by decide) a)⁻¹ *
              (leftLowerAdjacentRootLift F 3
                fin3_12_covBy (1 : F))⁻¹ := by
    rw [commutatorElement_def]
  have hUpperInv :
      (leftUpperRootLift F 3 0 2 (by decide) a)⁻¹ =
        leftUpperRootLift F 3 0 2 (by decide) (-a) := by
    have h := leftUpperRootLift_neg (F := F) (n := 3)
      0 2 (by decide) a
    exact h.symm
  have hLowerInv :
      (leftLowerAdjacentRootLift F 3 fin3_12_covBy (1 : F))⁻¹ =
        leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F) := by
    have h :=
      leftLowerAdjacentRootLift_neg (F := F) (n := 3)
        fin3_12_covBy (1 : F)
    have hNegOne : (-(1 : F)) = (-1 : F) := by simp
    rw [hNegOne] at h
    exact h.symm
  have hCommEq :
      ⁅leftUpperRootLift F 3 0 2 (by decide) a,
        leftLowerAdjacentRootLift F 3 fin3_12_covBy (1 : F)⁆ =
        leftUpperRootLift F 3 0 2 (by decide) a *
          leftLowerAdjacentRootLift F 3 fin3_12_covBy (1 : F) *
            leftUpperRootLift F 3 0 2 (by decide) (-a) *
              leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F) := by
    calc ⁅leftUpperRootLift F 3 0 2 (by decide) a,
            leftLowerAdjacentRootLift F 3 fin3_12_covBy (1 : F)⁆
        = leftUpperRootLift F 3 0 2 (by decide) a *
            leftLowerAdjacentRootLift F 3 fin3_12_covBy (1 : F) *
              (leftUpperRootLift F 3 0 2 (by decide) a)⁻¹ *
                (leftLowerAdjacentRootLift F 3
                  fin3_12_covBy (1 : F))⁻¹ := hCommDef
      _ = leftUpperRootLift F 3 0 2 (by decide) a *
            leftLowerAdjacentRootLift F 3 fin3_12_covBy (1 : F) *
              leftUpperRootLift F 3 0 2 (by decide) (-a) *
                leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F) := by
          rw [hUpperInv, hLowerInv]
  let y1 : X F 3 :=
    (leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F)).val.2
      (X_one F 3)
  let y2 : X F 3 :=
    (leftUpperRootLift F 3 0 2 (by decide) (-a)).val.2 y1
  let y3 : X F 3 :=
    (leftLowerAdjacentRootLift F 3 fin3_12_covBy (1 : F)).val.2 y2
  let y4 : X F 3 :=
    (leftUpperRootLift F 3 0 2 (by decide) a).val.2 y3
  have hFstY1 :
      X.fst y1 =
        Matrix.SpecialLinearGroup.transvection
          (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) := by
    have hFst :=
      leftLowerAdjacentRootLift_fst_apply F 3 fin3_12_covBy
        (-1 : F) (X_one F 3)
    have hOne : X.fst (X_one F 3) = 1 := X_one_fst F 3
    calc X.fst y1
        = X.fst
            ((leftLowerAdjacentRootLift F 3 fin3_12_covBy
                (-1 : F)).val.2 (X_one F 3)) := rfl
      _ = Matrix.SpecialLinearGroup.transvection
            (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
            X.fst (X_one F 3) := hFst
      _ = Matrix.SpecialLinearGroup.transvection
            (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) := by
          rw [hOne, mul_one]
  have hSndY1 :
      X.snd y1 =
        (hTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne
            (-1 : Fˣ))⁻¹ *
          (weylHMTits F 3 (1 : Fin 3) (2 : Fin 3)
              fin3_12_covBy.ne (1 : Fˣ))⁻¹ := by
    have hr : (-1 : F) ≠ 0 := neg_ne_zero.mpr one_ne_zero
    have h :=
      leftLowerAdjacentRootLift_snd_X_one_of_ne_zero F 3
        fin3_12_covBy (-1 : F) hr
    have hUnits : Units.mk0 (-1 : F) hr = (-1 : Fˣ) := by
      apply Units.ext
      simp
    rw [hUnits] at h
    calc X.snd y1
        = X.snd
            ((leftLowerAdjacentRootLift F 3 fin3_12_covBy
                (-1 : F)).val.2 (X_one F 3)) := rfl
      _ = (hTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne
              (-1 : Fˣ))⁻¹ *
            (weylHMTits F 3 (1 : Fin 3) (2 : Fin 3)
                fin3_12_covBy.ne (1 : Fˣ))⁻¹ := h
  have hFstY2 :
      X.fst y2 =
        Matrix.SpecialLinearGroup.transvection
            (show (0 : Fin 3) ≠ 2 by decide) (-a) *
          Matrix.SpecialLinearGroup.transvection
            (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) := by
    calc X.fst y2
        = X.fst
            ((leftUpperRootLift F 3 0 2 (by decide) (-a)).val.2 y1) := rfl
      _ = Matrix.SpecialLinearGroup.transvection
            (show (0 : Fin 3) ≠ 2 by decide) (-a) * X.fst y1 := by
          have hProj := leftExtensionProjHom_coe
            (F := F) (n := 3)
            (leftUpperRootLift F 3 0 2 (by decide) (-a)) y1
          have hHom :
              leftExtensionProjHom F 3
                  (leftUpperRootLift F 3 0 2 (by decide) (-a)) =
                Matrix.SpecialLinearGroup.transvection
                  (show (0 : Fin 3) ≠ 2 by decide) (-a) := by
            calc leftExtensionProjHom F 3
                    (leftUpperRootLift F 3 0 2 (by decide) (-a))
                = Matrix.SpecialLinearGroup.transvection
                    (ne_of_lt (show (0 : Fin 3) < 2 by decide)) (-a) :=
                  leftExtensionProjHom_leftUpperRootLift F 3 0 2
                    (by decide) (-a)
              _ = Matrix.SpecialLinearGroup.transvection
                    (show (0 : Fin 3) ≠ 2 by decide) (-a) := by
                  apply Subtype.ext
                  rfl
          rw [hHom] at hProj
          exact hProj
      _ = Matrix.SpecialLinearGroup.transvection
            (show (0 : Fin 3) ≠ 2 by decide) (-a) *
            Matrix.SpecialLinearGroup.transvection
              (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) := by
          rw [hFstY1]
  have hSndY2 : X.snd y2 = X.snd y1 := by
    have hUpperSnd :
        X.snd
            ((leftUpperRootLift F 3 0 2 (by decide) (-a)).val.2 y1) =
          X.snd y1 := by
      have hVal :
          (leftUpperRootLift F 3 0 2 (by decide) (-a)).val.2 =
            leftUpperPerm (F := F)
              (UpperElementary.elementary 0 2 (by decide) (-a)) := by
        simp [leftUpperRootLift_val]
      calc X.snd
              ((leftUpperRootLift F 3 0 2 (by decide) (-a)).val.2 y1)
          = X.snd
              (leftUpperPerm (F := F)
                (UpperElementary.elementary 0 2 (by decide) (-a)) y1) := by
            rw [hVal]
        _ = X.snd
              (leftUpper (F := F)
                (UpperElementary.elementary 0 2 (by decide) (-a)) y1) := by
            rw [leftUpperPerm_apply]
        _ = X.snd y1 := by rw [leftUpper_snd]
    calc X.snd y2
        = X.snd
            ((leftUpperRootLift F 3 0 2 (by decide) (-a)).val.2 y1) := rfl
      _ = X.snd y1 := hUpperSnd
  have hSndY3 : X.snd y3 = 1 := by
    have hSndApply :=
      leftLowerAdjacentRootLift_snd_apply F 3 fin3_12_covBy
        (1 : F) y2
    have hWeylFst :
        (Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
          X.fst y2 =
        (Matrix.GeneralLinearGroup.weylSLUnit
            (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              (show (0 : Fin 3) ≠ 2 by decide) (-a) *
            Matrix.SpecialLinearGroup.transvection
              (show (2 : Fin 3) ≠ 1 by decide) (-1 : F)) := by
      rw [hFstY2]
    have hTransFst :
        Matrix.SpecialLinearGroup.transvection
            (show (1 : Fin 3) ≠ 2 by decide) (-1 : F) *
          (Matrix.GeneralLinearGroup.weylSLUnit
              (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
            X.fst y2 =
        Matrix.SpecialLinearGroup.transvection
            (show (1 : Fin 3) ≠ 2 by decide) (-1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit
              (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                (show (0 : Fin 3) ≠ 2 by decide) (-a) *
              Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 1 by decide) (-1 : F))) := by
      rw [hFstY2, mul_assoc]
    calc X.snd y3
        = X.snd
            ((leftLowerAdjacentRootLift F 3 fin3_12_covBy
                (1 : F)).val.2 y2) := rfl
      _ = leftWeylMultiplier (F := F) fin3_12_covBy
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 2 by decide) (-1 : F) *
                (Matrix.GeneralLinearGroup.weylSLUnit
                    (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne
                      (1 : Fˣ))⁻¹ * X.fst y2) *
            (leftWeylMultiplier (F := F) fin3_12_covBy
                ((Matrix.GeneralLinearGroup.weylSLUnit
                    (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne
                      (1 : Fˣ))⁻¹ * X.fst y2))⁻¹ *
              X.snd y2 := hSndApply
      _ = leftWeylMultiplier (F := F) fin3_12_covBy
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 2 by decide) (-1 : F) *
                ((Matrix.GeneralLinearGroup.weylSLUnit
                    (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne
                      (1 : Fˣ))⁻¹ *
                  (Matrix.SpecialLinearGroup.transvection
                      (show (0 : Fin 3) ≠ 2 by decide) (-a) *
                    Matrix.SpecialLinearGroup.transvection
                      (show (2 : Fin 3) ≠ 1 by decide) (-1 : F)))) *
            (leftWeylMultiplier (F := F) fin3_12_covBy
                ((Matrix.GeneralLinearGroup.weylSLUnit
                    (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne
                      (1 : Fˣ))⁻¹ *
                  (Matrix.SpecialLinearGroup.transvection
                      (show (0 : Fin 3) ≠ 2 by decide) (-a) *
                    Matrix.SpecialLinearGroup.transvection
                      (show (2 : Fin 3) ≠ 1 by decide) (-1 : F))))⁻¹ *
              X.snd y2 := by
          rw [hTransFst, hWeylFst]
      _ = weylHMTits F 3 (1 : Fin 3) (2 : Fin 3)
              fin3_12_covBy.ne (1 : Fˣ) *
            ((hTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne
                (-1 : Fˣ))⁻¹)⁻¹ *
              X.snd y2 := by
          have hMulS1 := leftWeylMultiplier_G01_s1 (F := F) a
          have hMulS0 := leftWeylMultiplier_G01_s0 (F := F) a
          rw [hMulS1, hMulS0]
      _ = weylHMTits F 3 (1 : Fin 3) (2 : Fin 3)
              fin3_12_covBy.ne (1 : Fˣ) *
            (hTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne
                (-1 : Fˣ)) *
              X.snd y2 := by
          rw [inv_inv]
      _ = weylHMTits F 3 (1 : Fin 3) (2 : Fin 3)
              fin3_12_covBy.ne (1 : Fˣ) *
            (hTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne
                (-1 : Fˣ)) *
              X.snd y1 := by
          rw [hSndY2]
      _ = weylHMTits F 3 (1 : Fin 3) (2 : Fin 3)
              fin3_12_covBy.ne (1 : Fˣ) *
            (hTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne
                (-1 : Fˣ)) *
              ((hTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne
                  (-1 : Fˣ))⁻¹ *
                (weylHMTits F 3 (1 : Fin 3) (2 : Fin 3)
                    fin3_12_covBy.ne (1 : Fˣ))⁻¹) := by
          rw [hSndY1]
      _ = 1 := by
          calc weylHMTits F 3 (1 : Fin 3) (2 : Fin 3)
                    fin3_12_covBy.ne (1 : Fˣ) *
                  (hTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne
                      (-1 : Fˣ)) *
                    ((hTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne
                        (-1 : Fˣ))⁻¹ *
                      (weylHMTits F 3 (1 : Fin 3) (2 : Fin 3)
                          fin3_12_covBy.ne (1 : Fˣ))⁻¹)
              = weylHMTits F 3 (1 : Fin 3) (2 : Fin 3)
                    fin3_12_covBy.ne (1 : Fˣ) *
                  ((hTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne
                      (-1 : Fˣ)) *
                    (hTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne
                        (-1 : Fˣ))⁻¹) *
                  (weylHMTits F 3 (1 : Fin 3) (2 : Fin 3)
                      fin3_12_covBy.ne (1 : Fˣ))⁻¹ := by
                simp only [mul_assoc]
            _ = weylHMTits F 3 (1 : Fin 3) (2 : Fin 3)
                    fin3_12_covBy.ne (1 : Fˣ) *
                  (weylHMTits F 3 (1 : Fin 3) (2 : Fin 3)
                      fin3_12_covBy.ne (1 : Fˣ))⁻¹ := by
                simp [mul_inv_cancel]
            _ = 1 := by simp
  have hSndY4 : X.snd y4 = X.snd y3 := by
    calc X.snd y4
        = X.snd
            ((leftUpperRootLift F 3 0 2 (by decide) a).val.2 y3) := rfl
      _ = X.snd y3 := by
          have hVal :
              (leftUpperRootLift F 3 0 2 (by decide) a).val.2 =
                leftUpperPerm (F := F)
                  (UpperElementary.elementary 0 2 (by decide) a) := by
            simp [leftUpperRootLift_val]
          rw [hVal, leftUpperPerm_apply, leftUpper_snd]
  have hPoint :
      (⁅leftUpperRootLift F 3 0 2 (by decide) a,
        leftLowerAdjacentRootLift F 3 fin3_12_covBy (1 : F)⁆).val.2
        (X_one F 3) = y4 := by
    calc (⁅leftUpperRootLift F 3 0 2 (by decide) a,
            leftLowerAdjacentRootLift F 3 fin3_12_covBy (1 : F)⁆).val.2
            (X_one F 3)
        = ((leftUpperRootLift F 3 0 2 (by decide) a *
            leftLowerAdjacentRootLift F 3 fin3_12_covBy (1 : F) *
              leftUpperRootLift F 3 0 2 (by decide) (-a) *
                leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F)).val.2
            (X_one F 3)) := by
          rw [hCommEq]
        _ = y4 := by
          simp only [y1, y2, y3, y4]
          rfl
  calc X.snd
        (⁅leftUpperRootLift F 3 0 2 (by decide) a,
          leftLowerAdjacentRootLift F 3 fin3_12_covBy (1 : F)⁆.val.2
          (X_one F 3))
      = X.snd y4 := by rw [hPoint]
    _ = X.snd y3 := hSndY4
    _ = 1 := hSndY3

theorem G01_commutator_eq
    (F : Type u) [Field F] (a : F) :
    ⁅leftUpperRootLift F 3 0 2 (by decide) a,
      leftLowerAdjacentRootLift F 3 fin3_12_covBy (1 : F)⁆ =
      leftUpperRootLift F 3 0 1 (by decide) a := by
  apply leftExtension_eq_of_proj_eq_of_snd_X_one_eq
    (F := F) (n := 3) (by decide)
  · have hProjComm := G01_commutator_proj (F := F) a
    have hProjUpper :
        leftExtensionProjHom F 3
            (leftUpperRootLift F 3 0 1 (by decide) a) =
          Matrix.SpecialLinearGroup.transvection
            (ne_of_lt (show (0 : Fin 3) < 1 by decide)) a :=
      leftExtensionProjHom_leftUpperRootLift F 3 0 1 (by decide) a
    rw [hProjComm, hProjUpper]
  · have hSndComm := G01_commutator_snd_X_one (F := F) a
    have hSndUpper :
        X.snd
            ((leftUpperRootLift F 3 0 1 (by decide) a).val.2
              (X_one F 3)) = 1 := by
      have hVal :
          (leftUpperRootLift F 3 0 1 (by decide) a).val.2 =
            leftUpperPerm (F := F)
              (UpperElementary.elementary 0 1 (by decide) a) := by
        simp [leftUpperRootLift_val]
      calc X.snd
              ((leftUpperRootLift F 3 0 1 (by decide) a).val.2
                (X_one F 3))
          = X.snd
              (leftUpperPerm (F := F)
                (UpperElementary.elementary 0 1 (by decide) a)
                (X_one F 3)) := by rw [hVal]
        _ = X.snd
              (leftUpper (F := F)
                (UpperElementary.elementary 0 1 (by decide) a)
                (X_one F 3)) := by rw [leftUpperPerm_apply]
        _ = X.snd (X_one F 3) := by rw [leftUpper_snd]
        _ = 1 := by rw [X_one_snd]
    rw [hSndComm, hSndUpper]

end G01Commutator

section G10InversePrefix

theorem leftWeylMultiplier_G10InversePrefix_s0
    (F : Type u) [Field F] :
    leftWeylMultiplier (F := F) (n := 3) fin3_01_covBy
        ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3)
            (1 : Fin 3) fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
          Matrix.SpecialLinearGroup.transvection
            (show (2 : Fin 3) ≠ 1 by decide) (-1 : F)) =
      weylHMTits F 3 (0 : Fin 3) (1 : Fin 3) fin3_01_covBy.ne 1 := by
  have hZero :
      leftSimpleRootCoeff F 3
          ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3)
              (1 : Fin 3) fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
            Matrix.SpecialLinearGroup.transvection
              (show (2 : Fin 3) ≠ 1 by decide) (-1 : F)) fin3_01_covBy =
        0 :=
    leftSimpleRootCoeff_G10_inversePrefix_s0 F fin3_01_covBy fin3_12_covBy
  exact leftWeylMultiplier_of_zero fin3_01_covBy _ hZero

theorem leftWeylMultiplier_G10InversePrefix_s1
    (F : Type u) [Field F] :
    leftWeylMultiplier (F := F) (n := 3) fin3_01_covBy
        (Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne (1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3)
              (1 : Fin 3) fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
            Matrix.SpecialLinearGroup.transvection
              (show (2 : Fin 3) ≠ 1 by decide) (-1 : F))) =
      (hTits F 3 (0 : Fin 3) (1 : Fin 3) fin3_01_covBy.ne (-1 : Fˣ))⁻¹ := by
  have hCoeff :
      leftSimpleRootCoeff F 3
          (Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne (1 : F) *
            ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3)
                (1 : Fin 3) fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
              Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 1 by decide) (-1 : F))) fin3_01_covBy =
        1 :=
    leftSimpleRootCoeff_G10_inversePrefix_s1 F fin3_01_covBy fin3_12_covBy
  have hNotPos :
      ¬ ((Matrix.GeneralLinearGroup.bruhatMiddle
            (Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne (1 : F) *
              ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3)
                  (1 : Fin 3) fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 1 by decide) (-1 : F))) :
          MonomialBase Fˣ (Fin 3)).right.symm (0 : Fin 3) <
        (Matrix.GeneralLinearGroup.bruhatMiddle
            (Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne (1 : F) *
              ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3)
                  (1 : Fin 3) fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 1 by decide) (-1 : F))) :
          MonomialBase Fˣ (Fin 3)).right.symm (1 : Fin 3)) :=
    bruhatMiddle_G10_inversePrefix_s1_not_pos F fin3_01_covBy fin3_12_covBy
  have hNe :
      leftSimpleRootCoeff F 3
          (Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne (1 : F) *
            ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3)
                (1 : Fin 3) fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
              Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 1 by decide) (-1 : F))) fin3_01_covBy ≠
        0 := by
    rw [hCoeff]
    exact one_ne_zero
  have hMul :=
    leftWeylMultiplier_of_neg fin3_01_covBy _ hNe hNotPos
  have hOneNe : (1 : F) ≠ 0 := one_ne_zero
  have hUnitsEq :
      torusUnitOfNegCoeff (1 : F) hOneNe = (-1 : Fˣ) := by
    apply Units.ext
    simp [torusUnitOfNegCoeff]
  have hCoeffUnits :
      torusUnitOfNegCoeff
          (leftSimpleRootCoeff F 3
            (Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne (1 : F) *
              ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3)
                  (1 : Fin 3) fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 1 by decide) (-1 : F))) fin3_01_covBy)
          hNe =
        (-1 : Fˣ) := by
    have hEq :
        torusUnitOfNegCoeff
            (leftSimpleRootCoeff F 3
              (Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne (1 : F) *
                ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3)
                    (1 : Fin 3) fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
                  Matrix.SpecialLinearGroup.transvection
                    (show (2 : Fin 3) ≠ 1 by decide) (-1 : F))) fin3_01_covBy)
            hNe =
          torusUnitOfNegCoeff (1 : F) hOneNe := by
      apply Units.ext
      simp [torusUnitOfNegCoeff, hCoeff]
    rw [hEq, hUnitsEq]
  rw [hCoeffUnits] at hMul
  exact hMul

theorem G10InversePrefix_fst
    (F : Type u) [Field F] :
    X.fst
        ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F)).val.2
          ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F)).val.2
            (X_one F 3))) =
      Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne.symm (-1 : F) *
        Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne.symm
          (-1 : F) := by
  have hFst01 :=
    leftLowerAdjacentRootLift_fst_apply F 3 fin3_01_covBy (-1 : F)
      ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F)).val.2 (X_one F 3))
  have hFst12 :=
    leftLowerAdjacentRootLift_fst_apply F 3 fin3_12_covBy (-1 : F) (X_one F 3)
  have hOne : X.fst (X_one F 3) = 1 := X_one_fst F 3
  calc X.fst
          ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F)).val.2
            ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F)).val.2
              (X_one F 3)))
      = Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne.symm (-1 : F) *
          X.fst
            ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F)).val.2
              (X_one F 3)) := hFst01
    _ = Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne.symm (-1 : F) *
          (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne.symm (-1 : F) *
            X.fst (X_one F 3)) := by
        rw [hFst12]
    _ = Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne.symm (-1 : F) *
          Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne.symm (-1 : F) := by
        rw [hOne, mul_one]

theorem G10InversePrefix_snd
    (F : Type u) [Field F] :
    X.snd
        ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F)).val.2
          ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F)).val.2
            (X_one F 3))) =
      (hTits F 3 (0 : Fin 3) (1 : Fin 3) fin3_01_covBy.ne (-1 : Fˣ))⁻¹ *
        (weylHMTits F 3 (0 : Fin 3) (1 : Fin 3) fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
          ((hTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne (-1 : Fˣ))⁻¹ *
            (weylHMTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne
                (1 : Fˣ))⁻¹) := by
  let x1 : X F 3 :=
    (leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F)).val.2 (X_one F 3)
  have hFstX1 :
      X.fst x1 =
        Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne.symm (-1 : F) := by
    have hFst :=
      leftLowerAdjacentRootLift_fst_apply F 3 fin3_12_covBy (-1 : F) (X_one F 3)
    have hOne : X.fst (X_one F 3) = 1 := X_one_fst F 3
    calc X.fst x1
        = X.fst
            ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F)).val.2
              (X_one F 3)) := rfl
      _ = Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne.symm (-1 : F) *
            X.fst (X_one F 3) := hFst
      _ = Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne.symm (-1 : F) := by
          rw [hOne, mul_one]
  have hSndX1 :
      X.snd x1 =
        (hTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne (-1 : Fˣ))⁻¹ *
          (weylHMTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne
              (1 : Fˣ))⁻¹ := by
    have hr : (-1 : F) ≠ 0 := neg_ne_zero.mpr one_ne_zero
    have h :=
      leftLowerAdjacentRootLift_snd_X_one_of_ne_zero F 3 fin3_12_covBy (-1 : F) hr
    have hUnits : Units.mk0 (-1 : F) hr = (-1 : Fˣ) := by
      apply Units.ext
      simp
    rw [hUnits] at h
    calc X.snd x1
        = X.snd
            ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F)).val.2
              (X_one F 3)) := rfl
      _ = (hTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne (-1 : Fˣ))⁻¹ *
            (weylHMTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne
                (1 : Fˣ))⁻¹ := h
  have hTrans21Decide :
      Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne.symm (-1 : F) =
        Matrix.SpecialLinearGroup.transvection
          (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) := by
    apply Subtype.ext
    rfl
  have hWeylX1 :
      (Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3)
          fin3_01_covBy.ne (1 : Fˣ))⁻¹ * X.fst x1 =
        (Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3)
            fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
          Matrix.SpecialLinearGroup.transvection
            (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) := by
    rw [hFstX1, hTrans21Decide]
  have hTransX1 :
      Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne (-(-1 : F)) *
          (Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3)
              fin3_01_covBy.ne (1 : Fˣ))⁻¹ * X.fst x1 =
        Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne (1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3)
              fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
            Matrix.SpecialLinearGroup.transvection
              (show (2 : Fin 3) ≠ 1 by decide) (-1 : F)) := by
    rw [show (-(-1 : F)) = (1 : F) from by simp, hFstX1, hTrans21Decide,
      mul_assoc]
  have hSndApply :=
    leftLowerAdjacentRootLift_snd_apply F 3 fin3_01_covBy (-1 : F) x1
  calc X.snd
          ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F)).val.2
            ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F)).val.2
              (X_one F 3)))
      = X.snd ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F)).val.2 x1) := rfl
    _ = leftWeylMultiplier fin3_01_covBy
            (Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne
                (-(-1 : F)) *
              (Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3)
                  fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
              X.fst x1) *
          (leftWeylMultiplier fin3_01_covBy
              ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3)
                  fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
                X.fst x1))⁻¹ *
          X.snd x1 := hSndApply
    _ = leftWeylMultiplier fin3_01_covBy
            (Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne (1 : F) *
              ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3)
                  fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 1 by decide) (-1 : F))) *
          (leftWeylMultiplier fin3_01_covBy
              ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3)
                  fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 1 by decide) (-1 : F)))⁻¹ *
          X.snd x1 := by
        rw [hTransX1, hWeylX1]
    _ = (hTits F 3 (0 : Fin 3) (1 : Fin 3) fin3_01_covBy.ne (-1 : Fˣ))⁻¹ *
          (weylHMTits F 3 (0 : Fin 3) (1 : Fin 3) fin3_01_covBy.ne
              (1 : Fˣ))⁻¹ *
            X.snd x1 := by
        have hMul1 := leftWeylMultiplier_G10InversePrefix_s1 (F := F)
        have hMul0 := leftWeylMultiplier_G10InversePrefix_s0 (F := F)
        rw [hMul1, hMul0]
    _ = (hTits F 3 (0 : Fin 3) (1 : Fin 3) fin3_01_covBy.ne (-1 : Fˣ))⁻¹ *
          (weylHMTits F 3 (0 : Fin 3) (1 : Fin 3) fin3_01_covBy.ne
              (1 : Fˣ))⁻¹ *
            ((hTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne (-1 : Fˣ))⁻¹ *
              (weylHMTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne
                  (1 : Fˣ))⁻¹) := by
        rw [hSndX1]

end G10InversePrefix

section G10InverseStageThree

theorem leftWeylMultiplier_G10InverseStageThree_C0
    (F : Type u) [Field F] :
    leftWeylMultiplier (F := F) (n := 3) fin3_12_covBy
        ((Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3)
            (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              fin3_01_covBy.ne.symm (-1 : F) *
            Matrix.SpecialLinearGroup.transvection
              fin3_12_covBy.ne.symm (-1 : F))) =
      weylHMTits F 3 (1 : Fin 3) (2 : Fin 3)
        fin3_12_covBy.ne 1 := by
  have hZero :
      leftSimpleRootCoeff F 3
          ((Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3)
              (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                fin3_01_covBy.ne.symm (-1 : F) *
              Matrix.SpecialLinearGroup.transvection
                fin3_12_covBy.ne.symm (-1 : F))) fin3_12_covBy = 0 :=
    leftSimpleRootCoeff_G10InverseStageThree_weyl12_inv_T10_T21
      F fin3_01_covBy fin3_12_covBy
  exact leftWeylMultiplier_of_zero fin3_12_covBy _ hZero

theorem leftWeylMultiplier_G10InverseStageThree_C1
    (F : Type u) [Field F] :
    leftWeylMultiplier (F := F) (n := 3) fin3_12_covBy
        (Matrix.SpecialLinearGroup.transvection
            fin3_12_covBy.ne (-1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3)
              (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                fin3_01_covBy.ne.symm (-1 : F) *
              Matrix.SpecialLinearGroup.transvection
                fin3_12_covBy.ne.symm (-1 : F)))) =
      (hTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne
          (1 : Fˣ))⁻¹ := by
  have hCoeff :
      leftSimpleRootCoeff F 3
          (Matrix.SpecialLinearGroup.transvection
              fin3_12_covBy.ne (-1 : F) *
            ((Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3)
                (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
              (Matrix.SpecialLinearGroup.transvection
                  fin3_01_covBy.ne.symm (-1 : F) *
                Matrix.SpecialLinearGroup.transvection
                  fin3_12_covBy.ne.symm (-1 : F)))) fin3_12_covBy =
        -1 :=
    leftSimpleRootCoeff_G10InverseStageThree_T12_weyl12_T10_T21
      F fin3_01_covBy fin3_12_covBy
  have hNotPos :
      ¬ ((Matrix.GeneralLinearGroup.bruhatMiddle
            (Matrix.SpecialLinearGroup.transvection
                fin3_12_covBy.ne (-1 : F) *
              ((Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3)
                  (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
                (Matrix.SpecialLinearGroup.transvection
                    fin3_01_covBy.ne.symm (-1 : F) *
                  Matrix.SpecialLinearGroup.transvection
                    fin3_12_covBy.ne.symm (-1 : F)))) :
          MonomialBase Fˣ (Fin 3)).right.symm (1 : Fin 3) <
        (Matrix.GeneralLinearGroup.bruhatMiddle
            (Matrix.SpecialLinearGroup.transvection
                fin3_12_covBy.ne (-1 : F) *
              ((Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3)
                  (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
                (Matrix.SpecialLinearGroup.transvection
                    fin3_01_covBy.ne.symm (-1 : F) *
                  Matrix.SpecialLinearGroup.transvection
                    fin3_12_covBy.ne.symm (-1 : F)))) :
          MonomialBase Fˣ (Fin 3)).right.symm (2 : Fin 3)) :=
    bruhatMiddle_G10InverseStageThree_T12_weyl12_T10_T21_not_pos
      F fin3_01_covBy fin3_12_covBy
  have hNe :
      leftSimpleRootCoeff F 3
          (Matrix.SpecialLinearGroup.transvection
              fin3_12_covBy.ne (-1 : F) *
            ((Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3)
                (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
              (Matrix.SpecialLinearGroup.transvection
                  fin3_01_covBy.ne.symm (-1 : F) *
                Matrix.SpecialLinearGroup.transvection
                  fin3_12_covBy.ne.symm (-1 : F)))) fin3_12_covBy ≠
        0 := by
    rw [hCoeff]
    exact neg_ne_zero.mpr one_ne_zero
  have hMul :=
    leftWeylMultiplier_of_neg fin3_12_covBy _ hNe hNotPos
  have hOneNe : (-1 : F) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have hUnitsEq :
      torusUnitOfNegCoeff (-1 : F) hOneNe = (1 : Fˣ) := by
    apply Units.ext
    simp [torusUnitOfNegCoeff]
  have hCoeffUnits :
      torusUnitOfNegCoeff
          (leftSimpleRootCoeff F 3
            (Matrix.SpecialLinearGroup.transvection
                fin3_12_covBy.ne (-1 : F) *
              ((Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3)
                  (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
                (Matrix.SpecialLinearGroup.transvection
                    fin3_01_covBy.ne.symm (-1 : F) *
                  Matrix.SpecialLinearGroup.transvection
                    fin3_12_covBy.ne.symm (-1 : F)))) fin3_12_covBy)
          hNe = (1 : Fˣ) := by
    have hEq :
        torusUnitOfNegCoeff
            (leftSimpleRootCoeff F 3
              (Matrix.SpecialLinearGroup.transvection
                  fin3_12_covBy.ne (-1 : F) *
                ((Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3)
                    (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
                  (Matrix.SpecialLinearGroup.transvection
                      fin3_01_covBy.ne.symm (-1 : F) *
                    Matrix.SpecialLinearGroup.transvection
                      fin3_12_covBy.ne.symm (-1 : F)))) fin3_12_covBy)
            hNe =
          torusUnitOfNegCoeff (-1 : F) hOneNe := by
      apply Units.ext
      simp [torusUnitOfNegCoeff, hCoeff]
    rw [hEq, hUnitsEq]
  rw [hCoeffUnits] at hMul
  exact hMul

end G10InverseStageThree

section G10InverseStageFour

theorem leftWeylMultiplier_G10InverseStageFour_D0
    (F : Type u) [Field F] :
    leftWeylMultiplier (F := F) (n := 3) fin3_01_covBy
        ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3)
            (1 : Fin 3) fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              fin3_12_covBy.ne.symm (1 : F) *
            Matrix.SpecialLinearGroup.transvection
              fin3_01_covBy.ne.symm (-1 : F) *
            Matrix.SpecialLinearGroup.transvection
              fin3_12_covBy.ne.symm (-1 : F))) =
      weylHMTits F 3 (0 : Fin 3) (1 : Fin 3)
        fin3_01_covBy.ne 1 := by
  have hPos :
      (Matrix.GeneralLinearGroup.bruhatMiddle
          ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3)
              (1 : Fin 3) fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                fin3_12_covBy.ne.symm (1 : F) *
              Matrix.SpecialLinearGroup.transvection
                fin3_01_covBy.ne.symm (-1 : F) *
              Matrix.SpecialLinearGroup.transvection
                fin3_12_covBy.ne.symm (-1 : F))) :
        MonomialBase Fˣ (Fin 3)).right.symm (0 : Fin 3) <
      (Matrix.GeneralLinearGroup.bruhatMiddle
          ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3)
              (1 : Fin 3) fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                fin3_12_covBy.ne.symm (1 : F) *
              Matrix.SpecialLinearGroup.transvection
                fin3_01_covBy.ne.symm (-1 : F) *
              Matrix.SpecialLinearGroup.transvection
                fin3_12_covBy.ne.symm (-1 : F))) :
        MonomialBase Fˣ (Fin 3)).right.symm (1 : Fin 3) :=
    bruhatMiddle_G10InverseStageFour_D0_pos
      fin3_01_covBy fin3_12_covBy
  exact leftWeylMultiplier_of_order_pos fin3_01_covBy _ hPos

theorem leftWeylMultiplier_G10InverseStageFour_D1
    (F : Type u) [Field F] :
    leftWeylMultiplier (F := F) (n := 3) fin3_01_covBy
        (Matrix.SpecialLinearGroup.transvection
            fin3_01_covBy.ne (-1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3)
              (1 : Fin 3) fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                fin3_12_covBy.ne.symm (1 : F) *
              Matrix.SpecialLinearGroup.transvection
                fin3_01_covBy.ne.symm (-1 : F) *
              Matrix.SpecialLinearGroup.transvection
                fin3_12_covBy.ne.symm (-1 : F)))) =
      weylHMTits F 3 (0 : Fin 3) (1 : Fin 3)
        fin3_01_covBy.ne 1 := by
  have hPos :
      (Matrix.GeneralLinearGroup.bruhatMiddle
          (Matrix.SpecialLinearGroup.transvection
              fin3_01_covBy.ne (-1 : F) *
            ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3)
                (1 : Fin 3) fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
              (Matrix.SpecialLinearGroup.transvection
                  fin3_12_covBy.ne.symm (1 : F) *
                Matrix.SpecialLinearGroup.transvection
                  fin3_01_covBy.ne.symm (-1 : F) *
                Matrix.SpecialLinearGroup.transvection
                  fin3_12_covBy.ne.symm (-1 : F)))) :
        MonomialBase Fˣ (Fin 3)).right.symm (0 : Fin 3) <
      (Matrix.GeneralLinearGroup.bruhatMiddle
          (Matrix.SpecialLinearGroup.transvection
              fin3_01_covBy.ne (-1 : F) *
            ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3)
                (1 : Fin 3) fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
              (Matrix.SpecialLinearGroup.transvection
                  fin3_12_covBy.ne.symm (1 : F) *
                Matrix.SpecialLinearGroup.transvection
                  fin3_01_covBy.ne.symm (-1 : F) *
                Matrix.SpecialLinearGroup.transvection
                  fin3_12_covBy.ne.symm (-1 : F)))) :
        MonomialBase Fˣ (Fin 3)).right.symm (1 : Fin 3) :=
    bruhatMiddle_G10InverseStageFour_D1_pos
      fin3_01_covBy fin3_12_covBy
  exact leftWeylMultiplier_of_order_pos fin3_01_covBy _ hPos

end G10InverseStageFour

section G10InverseStageThreeAction

theorem G10InverseStageThree_fst
    (F : Type u) [Field F] :
    X.fst
        ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (1 : F)).val.2
          ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F)).val.2
            ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F)).val.2
              (X_one F 3)))) =
      Matrix.SpecialLinearGroup.transvection
          fin3_12_covBy.ne.symm (1 : F) *
        Matrix.SpecialLinearGroup.transvection
          fin3_01_covBy.ne.symm (-1 : F) *
        Matrix.SpecialLinearGroup.transvection
          fin3_12_covBy.ne.symm (-1 : F) := by
  have hFstPref := G10InversePrefix_fst (F := F)
  have hFst12 :=
    leftLowerAdjacentRootLift_fst_apply F 3 fin3_12_covBy (1 : F)
      ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F)).val.2
        ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F)).val.2
          (X_one F 3)))
  calc X.fst
          ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (1 : F)).val.2
            ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F)).val.2
              ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F)).val.2
                (X_one F 3))))
      = Matrix.SpecialLinearGroup.transvection
          fin3_12_covBy.ne.symm (1 : F) *
          X.fst
            ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F)).val.2
              ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F)).val.2
                (X_one F 3))) := hFst12
    _ = Matrix.SpecialLinearGroup.transvection
          fin3_12_covBy.ne.symm (1 : F) *
          (Matrix.SpecialLinearGroup.transvection
              fin3_01_covBy.ne.symm (-1 : F) *
            Matrix.SpecialLinearGroup.transvection
              fin3_12_covBy.ne.symm (-1 : F)) := by
        rw [hFstPref]
    _ = Matrix.SpecialLinearGroup.transvection
          fin3_12_covBy.ne.symm (1 : F) *
          Matrix.SpecialLinearGroup.transvection
            fin3_01_covBy.ne.symm (-1 : F) *
          Matrix.SpecialLinearGroup.transvection
            fin3_12_covBy.ne.symm (-1 : F) := by
        rw [← mul_assoc]

theorem G10InverseStageThree_snd
    (F : Type u) [Field F] :
    X.snd
        ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (1 : F)).val.2
          ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F)).val.2
            ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F)).val.2
              (X_one F 3)))) =
      (hTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne
          (1 : Fˣ))⁻¹ *
        (weylHMTits F 3 (1 : Fin 3) (2 : Fin 3)
            fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
          X.snd
            ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F)).val.2
              ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F)).val.2
                (X_one F 3))) := by
  let x2 : X F 3 :=
    (leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F)).val.2
      ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F)).val.2
        (X_one F 3))
  have hFstX2 : X.fst x2 =
      Matrix.SpecialLinearGroup.transvection
          fin3_01_covBy.ne.symm (-1 : F) *
        Matrix.SpecialLinearGroup.transvection
          fin3_12_covBy.ne.symm (-1 : F) :=
    G10InversePrefix_fst F
  have hWeylFst :
      (Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3)
          (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ * X.fst x2 =
        (Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3)
            (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              fin3_01_covBy.ne.symm (-1 : F) *
            Matrix.SpecialLinearGroup.transvection
              fin3_12_covBy.ne.symm (-1 : F)) := by
    rw [hFstX2]
  have hTransFst :
      Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne (-1 : F) *
        (Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3)
            (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ * X.fst x2 =
        Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne (-1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3)
              (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                fin3_01_covBy.ne.symm (-1 : F) *
              Matrix.SpecialLinearGroup.transvection
                fin3_12_covBy.ne.symm (-1 : F))) := by
    rw [hFstX2, mul_assoc]
  have hSndApply :=
    leftLowerAdjacentRootLift_snd_apply F 3 fin3_12_covBy (1 : F) x2
  calc X.snd
          ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (1 : F)).val.2
            ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F)).val.2
              ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F)).val.2
                (X_one F 3))))
      = X.snd ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (1 : F)).val.2 x2) :=
        rfl
    _ = leftWeylMultiplier fin3_12_covBy
            (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne
                (-1 : F) *
              (Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3)
                  (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ * X.fst x2) *
          (leftWeylMultiplier fin3_12_covBy
              ((Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3)
                  (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ * X.fst x2))⁻¹ *
          X.snd x2 := hSndApply
    _ = leftWeylMultiplier fin3_12_covBy
            (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne
                (-1 : F) *
              ((Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3)
                  (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
                (Matrix.SpecialLinearGroup.transvection
                    fin3_01_covBy.ne.symm (-1 : F) *
                  Matrix.SpecialLinearGroup.transvection
                    fin3_12_covBy.ne.symm (-1 : F)))) *
          (leftWeylMultiplier fin3_12_covBy
              ((Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3)
                  (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
                (Matrix.SpecialLinearGroup.transvection
                    fin3_01_covBy.ne.symm (-1 : F) *
                  Matrix.SpecialLinearGroup.transvection
                    fin3_12_covBy.ne.symm (-1 : F))))⁻¹ *
          X.snd x2 := by
        rw [hTransFst, hWeylFst]
    _ = (hTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne
            (1 : Fˣ))⁻¹ *
          (weylHMTits F 3 (1 : Fin 3) (2 : Fin 3)
              fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
            X.snd x2 := by
        have hMulC1 := leftWeylMultiplier_G10InverseStageThree_C1 (F := F)
        have hMulC0 := leftWeylMultiplier_G10InverseStageThree_C0 (F := F)
        rw [hMulC1, hMulC0]

theorem G10InverseStageThree_fst_snd_combined
    (F : Type u) [Field F] :
    X.snd
        ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (1 : F)).val.2
          ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F)).val.2
            ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F)).val.2
              (X_one F 3)))) =
      (hTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
        (weylHMTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne
            (1 : Fˣ))⁻¹ *
          ((hTits F 3 (0 : Fin 3) (1 : Fin 3) fin3_01_covBy.ne
              (-1 : Fˣ))⁻¹ *
            (weylHMTits F 3 (0 : Fin 3) (1 : Fin 3) fin3_01_covBy.ne
                (1 : Fˣ))⁻¹ *
              ((hTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne
                  (-1 : Fˣ))⁻¹ *
                (weylHMTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne
                    (1 : Fˣ))⁻¹)) := by
  have h3 := G10InverseStageThree_snd (F := F)
  have hPre := G10InversePrefix_snd (F := F)
  calc X.snd
          ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (1 : F)).val.2
            ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F)).val.2
              ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F)).val.2
                (X_one F 3))))
      = (hTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne
            (1 : Fˣ))⁻¹ *
          (weylHMTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne
              (1 : Fˣ))⁻¹ *
            X.snd
              ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F)).val.2
                ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F)).val.2
                  (X_one F 3))) := h3
    _ = (hTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne
            (1 : Fˣ))⁻¹ *
          (weylHMTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne
              (1 : Fˣ))⁻¹ *
            ((hTits F 3 (0 : Fin 3) (1 : Fin 3) fin3_01_covBy.ne
                (-1 : Fˣ))⁻¹ *
              (weylHMTits F 3 (0 : Fin 3) (1 : Fin 3) fin3_01_covBy.ne
                  (1 : Fˣ))⁻¹ *
                ((hTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne
                    (-1 : Fˣ))⁻¹ *
                  (weylHMTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne
                      (1 : Fˣ))⁻¹)) := by
        rw [hPre]

end G10InverseStageThreeAction

section G10InverseFull

theorem leftLowerRootLift20_inv_eq
    (F : Type u) [Field F] :
    (leftLowerRootLift20 F (1 : F))⁻¹ =
      leftLowerAdjacentRootLift F 3 fin3_01_covBy (1 : F) *
        leftLowerAdjacentRootLift F 3 fin3_12_covBy (1 : F) *
        leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F) *
        leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F) := by
  unfold leftLowerRootLift20 leftLowerTwoStepRootLift
  simp only [commutatorElement_def]
  have hNeg01 :
      leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F) =
        (leftLowerAdjacentRootLift F 3 fin3_01_covBy (1 : F))⁻¹ := by
    have h := leftLowerAdjacentRootLift_neg (F := F) (n := 3)
      fin3_01_covBy (1 : F)
    have h1 : (-(1 : F)) = (-1 : F) := by simp
    rw [h1] at h
    exact h
  have hNeg12 :
      leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F) =
        (leftLowerAdjacentRootLift F 3 fin3_12_covBy (1 : F))⁻¹ := by
    have h := leftLowerAdjacentRootLift_neg (F := F) (n := 3)
      fin3_12_covBy (1 : F)
    have h1 : (-(1 : F)) = (-1 : F) := by simp
    rw [h1] at h
    exact h
  calc (leftLowerAdjacentRootLift F 3 fin3_12_covBy (1 : F) *
            leftLowerAdjacentRootLift F 3 fin3_01_covBy (1 : F) *
              (leftLowerAdjacentRootLift F 3 fin3_12_covBy (1 : F))⁻¹ *
                (leftLowerAdjacentRootLift F 3 fin3_01_covBy (1 : F))⁻¹)⁻¹
      = leftLowerAdjacentRootLift F 3 fin3_01_covBy (1 : F) *
          leftLowerAdjacentRootLift F 3 fin3_12_covBy (1 : F) *
          (leftLowerAdjacentRootLift F 3 fin3_01_covBy (1 : F))⁻¹ *
          (leftLowerAdjacentRootLift F 3 fin3_12_covBy (1 : F))⁻¹ := by
        simp only [_root_.mul_inv_rev, inv_inv, mul_assoc]
    _ = leftLowerAdjacentRootLift F 3 fin3_01_covBy (1 : F) *
          leftLowerAdjacentRootLift F 3 fin3_12_covBy (1 : F) *
          leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F) *
          leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F) := by
        rw [← hNeg01, ← hNeg12]

theorem G10Inverse_full_fst_aux
    (F : Type u) [Field F] :
    Matrix.SpecialLinearGroup.transvection
        fin3_01_covBy.ne.symm (1 : F) *
      Matrix.SpecialLinearGroup.transvection
        fin3_12_covBy.ne.symm (1 : F) *
      Matrix.SpecialLinearGroup.transvection
        fin3_01_covBy.ne.symm (-1 : F) *
      Matrix.SpecialLinearGroup.transvection
        fin3_12_covBy.ne.symm (-1 : F) =
    Matrix.SpecialLinearGroup.transvection
        (show (2 : Fin 3) ≠ 0 by decide) (-1 : F) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.SpecialLinearGroup.coe_mul,
      Matrix.add_apply, Matrix.one_apply,
      Matrix.single_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Fin.isValue]

theorem G10Inverse_fst
    (F : Type u) [Field F] :
    X.fst (((leftLowerRootLift20 F (1 : F))⁻¹).val.2 (X_one F 3)) =
      Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) (-1 : F) := by
  have hInv := leftLowerRootLift20_inv_eq (F := F)
  have hFstPref := G10InversePrefix_fst F
  have hFst3 := G10InverseStageThree_fst F
  have hFst01 :=
    leftLowerAdjacentRootLift_fst_apply F 3 fin3_01_covBy (1 : F)
      ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (1 : F)).val.2
        ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F)).val.2
          ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F)).val.2 (X_one F 3))))
  have hPoint :
      (((leftLowerRootLift20 F (1 : F))⁻¹).val.2 (X_one F 3)) =
      (leftLowerAdjacentRootLift F 3 fin3_01_covBy (1 : F)).val.2
        ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (1 : F)).val.2
          ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F)).val.2
            ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F)).val.2 (X_one F 3)))) := by
    calc (((leftLowerRootLift20 F (1 : F))⁻¹).val.2 (X_one F 3))
        = ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (1 : F) *
            leftLowerAdjacentRootLift F 3 fin3_12_covBy (1 : F) *
            leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F) *
            leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F)).val.2 (X_one F 3)) := by
          rw [hInv]
      _ = (leftLowerAdjacentRootLift F 3 fin3_01_covBy (1 : F)).val.2
            ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (1 : F)).val.2
              ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F)).val.2
                ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F)).val.2 (X_one F 3)))) := by
          rfl
  calc X.fst (((leftLowerRootLift20 F (1 : F))⁻¹).val.2 (X_one F 3))
      = X.fst
          ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (1 : F)).val.2
            ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (1 : F)).val.2
              ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F)).val.2
                ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F)).val.2
                  (X_one F 3))))) := by
        rw [hPoint]
    _ = Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne.symm (1 : F) *
          X.fst
            ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (1 : F)).val.2
              ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F)).val.2
                ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F)).val.2
                  (X_one F 3)))) := hFst01
    _ = Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne.symm (1 : F) *
          (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne.symm (1 : F) *
            Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne.symm (-1 : F) *
            Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne.symm (-1 : F)) := by
        rw [hFst3]
    _ = Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne.symm (1 : F) *
          Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne.symm (1 : F) *
          Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne.symm (-1 : F) *
          Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne.symm (-1 : F) := by
        simp only [mul_assoc]
    _ = Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) (-1 : F) :=
      G10Inverse_full_fst_aux F

theorem G10Inverse_snd
    (F : Type u) [Field F] :
    X.snd (((leftLowerRootLift20 F (1 : F))⁻¹).val.2 (X_one F 3)) =
      (hTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
        (weylHMTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
          ((hTits F 3 (0 : Fin 3) (1 : Fin 3) fin3_01_covBy.ne
              (-1 : Fˣ))⁻¹ *
            (weylHMTits F 3 (0 : Fin 3) (1 : Fin 3) fin3_01_covBy.ne
                (1 : Fˣ))⁻¹ *
              ((hTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne
                  (-1 : Fˣ))⁻¹ *
                (weylHMTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne
                    (1 : Fˣ))⁻¹)) := by
  have hInv := leftLowerRootLift20_inv_eq (F := F)
  have hCombined := G10InverseStageThree_fst_snd_combined F
  let x3 : X F 3 :=
    (leftLowerAdjacentRootLift F 3 fin3_12_covBy (1 : F)).val.2
      ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F)).val.2
        ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F)).val.2 (X_one F 3)))
  have hSndX3 : X.snd x3 =
      (hTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
        (weylHMTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
          ((hTits F 3 (0 : Fin 3) (1 : Fin 3) fin3_01_covBy.ne
              (-1 : Fˣ))⁻¹ *
            (weylHMTits F 3 (0 : Fin 3) (1 : Fin 3) fin3_01_covBy.ne
                (1 : Fˣ))⁻¹ *
              ((hTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne
                  (-1 : Fˣ))⁻¹ *
                (weylHMTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne
                    (1 : Fˣ))⁻¹)) :=
    hCombined
  have hFstX3 := G10InverseStageThree_fst F
  have hSndApply :=
    leftLowerAdjacentRootLift_snd_apply F 3 fin3_01_covBy (1 : F) x3
  have hTransNeg : (-(1 : F)) = (-1 : F) := by simp
  have hWeylFst :
      (Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3)
          fin3_01_covBy.ne (1 : Fˣ))⁻¹ * X.fst x3 =
        (Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3)
            fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne.symm (1 : F) *
            Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne.symm (-1 : F) *
            Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne.symm (-1 : F)) := by
    rw [hFstX3]
  have hTransFst :
      Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne (-(1 : F)) *
        (Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3)
            fin3_01_covBy.ne (1 : Fˣ))⁻¹ * X.fst x3 =
        Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne (-1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3)
              fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne.symm (1 : F) *
              Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne.symm (-1 : F) *
              Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne.symm (-1 : F))) := by
    rw [hTransNeg, hFstX3, mul_assoc]
  have hPoint :
      (((leftLowerRootLift20 F (1 : F))⁻¹).val.2 (X_one F 3)) =
        (leftLowerAdjacentRootLift F 3 fin3_01_covBy (1 : F)).val.2 x3 := by
    calc (((leftLowerRootLift20 F (1 : F))⁻¹).val.2 (X_one F 3))
        = ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (1 : F) *
            leftLowerAdjacentRootLift F 3 fin3_12_covBy (1 : F) *
            leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F) *
            leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F)).val.2 (X_one F 3)) := by
          rw [hInv]
      _ = (leftLowerAdjacentRootLift F 3 fin3_01_covBy (1 : F)).val.2
            ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (1 : F)).val.2
              ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F)).val.2
                ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F)).val.2 (X_one F 3)))) := by
          rfl
      _ = (leftLowerAdjacentRootLift F 3 fin3_01_covBy (1 : F)).val.2 x3 := rfl
  calc X.snd (((leftLowerRootLift20 F (1 : F))⁻¹).val.2 (X_one F 3))
      = X.snd ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (1 : F)).val.2 x3) := by
        rw [hPoint]
    _ = leftWeylMultiplier fin3_01_covBy
            (Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne
                (-(1 : F)) *
              (Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3)
                  fin3_01_covBy.ne (1 : Fˣ))⁻¹ * X.fst x3) *
          (leftWeylMultiplier fin3_01_covBy
              ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3)
                  fin3_01_covBy.ne (1 : Fˣ))⁻¹ * X.fst x3))⁻¹ *
          X.snd x3 := hSndApply
    _ = leftWeylMultiplier fin3_01_covBy
            (Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne (-1 : F) *
              ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3)
                  fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
                (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne.symm (1 : F) *
                  Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne.symm (-1 : F) *
                  Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne.symm (-1 : F)))) *
          (leftWeylMultiplier fin3_01_covBy
              ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3)
                  fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
                (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne.symm (1 : F) *
                  Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne.symm (-1 : F) *
                  Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne.symm (-1 : F))))⁻¹ *
          X.snd x3 := by
        rw [hTransFst, hWeylFst]
    _ = weylHMTits F 3 (0 : Fin 3) (1 : Fin 3) fin3_01_covBy.ne (1 : Fˣ) *
          (weylHMTits F 3 (0 : Fin 3) (1 : Fin 3) fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
          X.snd x3 := by
        have hMulD1 := leftWeylMultiplier_G10InverseStageFour_D1 (F := F)
        have hMulD0 := leftWeylMultiplier_G10InverseStageFour_D0 (F := F)
        rw [hMulD1, hMulD0]
    _ = X.snd x3 := by
        rw [mul_inv_cancel, one_mul]
    _ = (hTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
          (weylHMTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
            ((hTits F 3 (0 : Fin 3) (1 : Fin 3) fin3_01_covBy.ne
                (-1 : Fˣ))⁻¹ *
              (weylHMTits F 3 (0 : Fin 3) (1 : Fin 3) fin3_01_covBy.ne
                  (1 : Fˣ))⁻¹ *
                ((hTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne
                    (-1 : Fˣ))⁻¹ *
                  (weylHMTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne
                      (1 : Fˣ))⁻¹)) := hSndX3

end G10InverseFull

section G10TranslatedHelpers

private theorem torusUnitOfNegCoeff_neg_one
    {F : Type u} [Field F] (h : (-1 : F) ≠ 0) :
    torusUnitOfNegCoeff (-1 : F) h = (1 : Fˣ) := by
  apply Units.ext
  simp [torusUnitOfNegCoeff]

private theorem torusUnitOfNegCoeff_inv_one_sub
    (F : Type u) [Field F] (a : F) (_ha : a ≠ 1)
    (hInv : (a - 1)⁻¹ ≠ 0) (hOneSub : (1 - a) ≠ 0) :
    torusUnitOfNegCoeff ((a - 1)⁻¹) hInv =
      (Units.mk0 (1 - a) hOneSub)⁻¹ := by
  apply Units.ext
  simp only [torusUnitOfNegCoeff, Units.val_mk0,
    Units.val_inv_eq_inv_val]
  have hOne : (1 : F) - a = -(a - 1) := by ring
  calc (-(a - 1)⁻¹ : F)
      = (-(a - 1))⁻¹ := by
        rw [neg_inv]
    _ = (1 - a)⁻¹ := by
        rw [← hOne]

private theorem torusUnitOfNegCoeff_div_ratio
    (F : Type u) [Field F] (a : F) (_ha0 : a ≠ 0) (_ha1 : a ≠ 1)
    (hDiv : a / (a - 1) ≠ 0) (hRatio : a / (1 - a) ≠ 0) :
    torusUnitOfNegCoeff (a / (a - 1)) hDiv =
      Units.mk0 (a / (1 - a)) hRatio := by
  apply Units.ext
  change -(a / (a - 1)) = a / (1 - a)
  have hOne : (1 : F) - a = -(a - 1) := by ring
  have hDivEq : a / (1 - a) = -(a / (a - 1)) := by
    calc a / (1 - a)
        = a / (-(a - 1)) := by
          rw [hOne]
      _ = -(a / (a - 1)) := by
          rw [div_neg]
  rw [hDivEq]

private theorem leftWeylMultiplier_G10TranslatedStageOne_C0_aux
    (F : Type u) [Field F] (a : F) :
    leftWeylMultiplier (F := F) (n := 3) fin3_01_covBy
        ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3)
            fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne (-a) *
            Matrix.SpecialLinearGroup.transvection
              (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))) =
      weylHMTits F 3 0 1 fin3_01_covBy.ne 1 := by
  have hPos :=
    bruhatMiddle_G10TranslatedStageOne_C0_pos F a
      fin3_01_covBy fin3_12_covBy
  exact leftWeylMultiplier_of_order_pos fin3_01_covBy _ hPos

private theorem leftWeylMultiplier_G10TranslatedStageOne_C1_aux
    (F : Type u) [Field F] (a : F) :
    leftWeylMultiplier (F := F) (n := 3) fin3_01_covBy
        (Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne (1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3)
              fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne (-a) *
              Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))) =
      weylHMTits F 3 0 1 fin3_01_covBy.ne 1 := by
  have hPos :=
    bruhatMiddle_G10TranslatedStageOne_C1_pos F a
      fin3_01_covBy fin3_12_covBy
  exact leftWeylMultiplier_of_order_pos fin3_01_covBy _ hPos

private theorem leftWeylMultiplier_G10TranslatedStageTwo_exc_C0
    (F : Type u) [Field F] :
    leftWeylMultiplier (F := F) (n := 3) fin3_12_covBy
        ((Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3)
            fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 2 by decide) (-1 : F) *
              Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))) =
      weylHMTits F 3 1 2 fin3_12_covBy.ne 1 := by
  have hPos :=
    bruhatMiddle_G10TranslatedStageTwo_exceptional_C0_pos F
      fin3_01_covBy fin3_12_covBy
  exact leftWeylMultiplier_of_order_pos fin3_12_covBy _ hPos

private theorem leftWeylMultiplier_G10TranslatedStageTwo_exc_C1
    (F : Type u) [Field F] :
    leftWeylMultiplier (F := F) (n := 3) fin3_12_covBy
        (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne (1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3)
              fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 2 by decide) (-1 : F) *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))))) =
      weylHMTits F 3 1 2 fin3_12_covBy.ne 1 := by
  have hPos :=
    bruhatMiddle_G10TranslatedStageTwo_exceptional_C1_pos F
      fin3_01_covBy fin3_12_covBy
  exact leftWeylMultiplier_of_order_pos fin3_12_covBy _ hPos

private theorem leftWeylMultiplier_G10TranslatedStageTwo_zero_C0
    (F : Type u) [Field F] :
    leftWeylMultiplier (F := F) (n := 3) fin3_12_covBy
        ((Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3)
            fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 2 by decide) (-(0 : F)) *
              Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))) =
      (hTits F 3 1 2 fin3_12_covBy.ne (1 : Fˣ))⁻¹ := by
  have ha : (0 : F) ≠ 1 := by simp
  have hCoeff :=
    leftSimpleRootCoeff_G10TranslatedStageTwo_C0 F 0 ha fin3_12_covBy
  have hCoeffEq : ((0 : F) - 1)⁻¹ = (-1 : F) := by simp
  rw [hCoeffEq] at hCoeff
  have hNe : leftSimpleRootCoeff F 3
      ((Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3)
          fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
        (Matrix.SpecialLinearGroup.transvection
            (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
          (Matrix.SpecialLinearGroup.transvection
              (show (1 : Fin 3) ≠ 2 by decide) (-(0 : F)) *
            Matrix.SpecialLinearGroup.transvection
              (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))) fin3_12_covBy ≠
      0 := by
    rw [hCoeff]
    exact neg_ne_zero.mpr one_ne_zero
  have hNotPos :=
    bruhatMiddle_G10TranslatedStageTwo_C0_not_pos F 0 ha fin3_12_covBy
  have hMul :=
    leftWeylMultiplier_of_neg fin3_12_covBy _ hNe hNotPos
  have hOneNe : (-1 : F) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have hUnits : torusUnitOfNegCoeff (-1 : F) hOneNe = (1 : Fˣ) := by
    exact torusUnitOfNegCoeff_neg_one hOneNe
  have hUnitsEq :
      torusUnitOfNegCoeff
          (leftSimpleRootCoeff F 3
            ((Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3)
                fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                (Matrix.SpecialLinearGroup.transvection
                    (show (1 : Fin 3) ≠ 2 by decide) (-(0 : F)) *
                  Matrix.SpecialLinearGroup.transvection
                    (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))) fin3_12_covBy)
          hNe = (1 : Fˣ) := by
    have hEqT : torusUnitOfNegCoeff
        (leftSimpleRootCoeff F 3
          ((Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3)
              fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 2 by decide) (-(0 : F)) *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))) fin3_12_covBy)
        hNe = torusUnitOfNegCoeff (-1 : F) hOneNe := by
      apply Units.ext
      simp only [torusUnitOfNegCoeff, Units.val_mk0]
      rw [hCoeff]
    rw [hEqT, hUnits]
  rw [hUnitsEq] at hMul
  exact hMul

private theorem leftWeylMultiplier_G10TranslatedStageTwo_zero_C1
    (F : Type u) [Field F] :
    leftWeylMultiplier (F := F) (n := 3) fin3_12_covBy
        (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne (1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3)
              fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 2 by decide) (-(0 : F)) *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))))) =
      weylHMTits F 3 1 2 fin3_12_covBy.ne 1 := by
  have ha : (0 : F) ≠ 1 := by simp
  have hCoeff :=
    leftSimpleRootCoeff_G10TranslatedStageTwo_C1 F 0 ha fin3_12_covBy
  have hZero : (0 : F) / ((0 : F) - 1) = 0 := by simp
  rw [hZero] at hCoeff
  exact leftWeylMultiplier_of_zero fin3_12_covBy _ hCoeff

private theorem leftWeylMultiplier_G10TranslatedStageTwo_gen_C0
    (F : Type u) [Field F] (a : F) (ha1 : a ≠ 1) :
    leftWeylMultiplier (F := F) (n := 3) fin3_12_covBy
        ((Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3)
            fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                fin3_12_covBy.ne (-a) *
              Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))) =
      (hTits F 3 1 2 fin3_12_covBy.ne
          (torusUnitOfNegCoeff ((a - 1)⁻¹)
            (inv_ne_zero (sub_ne_zero.mpr ha1))))⁻¹ := by
  have hCoeff :=
    leftSimpleRootCoeff_G10TranslatedStageTwo_C0 F a ha1 fin3_12_covBy
  have hSub : a - 1 ≠ 0 := sub_ne_zero.mpr ha1
  have hInvNe : (a - 1)⁻¹ ≠ 0 := inv_ne_zero hSub
  have hNe : leftSimpleRootCoeff F 3
      ((Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3)
          fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
        (Matrix.SpecialLinearGroup.transvection
            (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
          (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne (-a) *
            Matrix.SpecialLinearGroup.transvection
              (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))) fin3_12_covBy ≠
      0 := by
    rw [hCoeff]
    exact hInvNe
  have hNotPos :=
    bruhatMiddle_G10TranslatedStageTwo_C0_not_pos F a ha1 fin3_12_covBy
  have hMul :=
    leftWeylMultiplier_of_neg fin3_12_covBy _ hNe hNotPos
  have hUnitsEq : torusUnitOfNegCoeff
      (leftSimpleRootCoeff F 3
        ((Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3)
            fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
            (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne (-a) *
              Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))) fin3_12_covBy)
      hNe =
      torusUnitOfNegCoeff ((a - 1)⁻¹) hInvNe := by
    apply Units.ext
    simp [torusUnitOfNegCoeff, hCoeff]
  rw [hUnitsEq] at hMul
  exact hMul

private theorem leftWeylMultiplier_G10TranslatedStageTwo_gen_C1
    (F : Type u) [Field F] (a : F) (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    leftWeylMultiplier (F := F) (n := 3) fin3_12_covBy
        (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne (1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3)
              fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne (-a) *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))))) =
      (hTits F 3 1 2 fin3_12_covBy.ne
          (torusUnitOfNegCoeff (a / (a - 1))
            (div_ne_zero ha0 (sub_ne_zero.mpr ha1))))⁻¹ := by
  have hCoeff :=
    leftSimpleRootCoeff_G10TranslatedStageTwo_C1 F a ha1 fin3_12_covBy
  have hSub : a - 1 ≠ 0 := sub_ne_zero.mpr ha1
  have hDivNe : a / (a - 1) ≠ 0 := div_ne_zero ha0 hSub
  have hNe : leftSimpleRootCoeff F 3
      (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne (1 : F) *
        ((Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3)
            fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
            (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne (-a) *
              Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))))) fin3_12_covBy ≠
      0 := by
    rw [hCoeff]
    exact hDivNe
  have hNotPos :=
    bruhatMiddle_G10TranslatedStageTwo_C1_not_pos F a ha1 fin3_12_covBy
  have hMul :=
    leftWeylMultiplier_of_neg fin3_12_covBy _ hNe hNotPos
  have hUnitsEq : torusUnitOfNegCoeff
      (leftSimpleRootCoeff F 3
        (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne (1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3)
              fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne (-a) *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))))) fin3_12_covBy)
      hNe =
      torusUnitOfNegCoeff (a / (a - 1)) hDivNe := by
    apply Units.ext
    simp [torusUnitOfNegCoeff, hCoeff]
  rw [hUnitsEq] at hMul
  exact hMul

end G10TranslatedHelpers

section G10TranslatedUpper

theorem G10TranslatedUpper_fst
    (F : Type u) [Field F] (a : F) :
    X.fst
        ((leftUpperRootLift F 3 1 2 (by decide) (-a)).val.2
          (((leftLowerRootLift20 F (1 : F))⁻¹).val.2 (X_one F 3))) =
      Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne (-a) *
        Matrix.SpecialLinearGroup.transvection
          (show (2 : Fin 3) ≠ 0 by decide) (-1 : F) := by
  let y0 : X F 3 :=
    ((leftLowerRootLift20 F (1 : F))⁻¹).val.2 (X_one F 3)
  have hFst0 : X.fst y0 =
      Matrix.SpecialLinearGroup.transvection
        (show (2 : Fin 3) ≠ 0 by decide) (-1 : F) :=
    G10Inverse_fst F
  have hProj :
      leftExtensionProjHom F 3
          (leftUpperRootLift F 3 1 2 (by decide) (-a)) =
        Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne (-a) := by
    have h0 :=
      leftExtensionProjHom_leftUpperRootLift F 3 1 2 (by decide) (-a)
    have hEq :
        Matrix.SpecialLinearGroup.transvection
            (ne_of_lt (show (1 : Fin 3) < 2 by decide)) (-a) =
          Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne (-a) := by
      apply Subtype.ext
      rfl
    calc leftExtensionProjHom F 3
            (leftUpperRootLift F 3 1 2 (by decide) (-a))
        = Matrix.SpecialLinearGroup.transvection
            (ne_of_lt (show (1 : Fin 3) < 2 by decide)) (-a) := h0
      _ = Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne (-a) :=
          hEq
  have hFst :=
    leftExtensionProjHom_coe (F := F) (n := 3)
      (leftUpperRootLift F 3 1 2 (by decide) (-a)) y0
  calc X.fst
          ((leftUpperRootLift F 3 1 2 (by decide) (-a)).val.2
            (((leftLowerRootLift20 F (1 : F))⁻¹).val.2 (X_one F 3)))
      = X.fst ((leftUpperRootLift F 3 1 2 (by decide) (-a)).val.2 y0) := rfl
    _ = leftExtensionProjHom F 3
            (leftUpperRootLift F 3 1 2 (by decide) (-a)) *
          X.fst y0 := hFst
    _ = Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne (-a) *
          X.fst y0 := by
        rw [hProj]
    _ = Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne (-a) *
          Matrix.SpecialLinearGroup.transvection
            (show (2 : Fin 3) ≠ 0 by decide) (-1 : F) := by
        rw [hFst0]

theorem G10TranslatedUpper_snd
    (F : Type u) [Field F] (a : F) :
    X.snd
        ((leftUpperRootLift F 3 1 2 (by decide) (-a)).val.2
          (((leftLowerRootLift20 F (1 : F))⁻¹).val.2 (X_one F 3))) =
      X.snd (((leftLowerRootLift20 F (1 : F))⁻¹).val.2 (X_one F 3)) := by
  let y0 : X F 3 :=
    ((leftLowerRootLift20 F (1 : F))⁻¹).val.2 (X_one F 3)
  have hVal :
      (leftUpperRootLift F 3 1 2 (by decide) (-a)).val.2 =
        leftUpperPerm
          (UpperElementary.elementary (1 : Fin 3) 2 (by decide) (-a)) := by
    simp [leftUpperRootLift_val]
  calc X.snd
          ((leftUpperRootLift F 3 1 2 (by decide) (-a)).val.2
            (((leftLowerRootLift20 F (1 : F))⁻¹).val.2 (X_one F 3)))
      = X.snd ((leftUpperRootLift F 3 1 2 (by decide) (-a)).val.2 y0) := rfl
    _ = X.snd (leftUpperPerm
          (UpperElementary.elementary (1 : Fin 3) 2 (by decide) (-a)) y0) := by
        rw [hVal]
    _ = X.snd (leftUpper
          (UpperElementary.elementary (1 : Fin 3) 2 (by decide) (-a)) y0) := by
        rw [leftUpperPerm_apply]
    _ = X.snd y0 := by
        rw [leftUpper_snd]

end G10TranslatedUpper

section G10TranslatedStageOne

theorem G10TranslatedStageOne_fst
    (F : Type u) [Field F] (a : F) :
    X.fst
        ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F)).val.2
          ((leftUpperRootLift F 3 1 2 (by decide) (-a)).val.2
            (((leftLowerRootLift20 F (1 : F))⁻¹).val.2 (X_one F 3)))) =
      Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne.symm (-1 : F) *
        (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne (-a) *
          Matrix.SpecialLinearGroup.transvection
            (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)) := by
  let yU : X F 3 :=
    (leftUpperRootLift F 3 1 2 (by decide) (-a)).val.2
      (((leftLowerRootLift20 F (1 : F))⁻¹).val.2 (X_one F 3))
  have hFstU : X.fst yU =
      Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne (-a) *
        Matrix.SpecialLinearGroup.transvection
          (show (2 : Fin 3) ≠ 0 by decide) (-1 : F) :=
    G10TranslatedUpper_fst F a
  have hFst01 :=
    leftLowerAdjacentRootLift_fst_apply F 3 fin3_01_covBy (-1 : F) yU
  calc X.fst
          ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F)).val.2
            ((leftUpperRootLift F 3 1 2 (by decide) (-a)).val.2
              (((leftLowerRootLift20 F (1 : F))⁻¹).val.2 (X_one F 3))))
      = X.fst ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F)).val.2 yU) :=
        rfl
    _ = Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne.symm (-1 : F) *
          X.fst yU := hFst01
    _ = Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne.symm (-1 : F) *
          (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne (-a) *
            Matrix.SpecialLinearGroup.transvection
              (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)) := by
        rw [hFstU]

theorem G10TranslatedStageOne_snd
    (F : Type u) [Field F] (a : F) :
    X.snd
        ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F)).val.2
          ((leftUpperRootLift F 3 1 2 (by decide) (-a)).val.2
            (((leftLowerRootLift20 F (1 : F))⁻¹).val.2 (X_one F 3)))) =
      X.snd (((leftLowerRootLift20 F (1 : F))⁻¹).val.2 (X_one F 3)) := by
  let y0 : X F 3 :=
    ((leftLowerRootLift20 F (1 : F))⁻¹).val.2 (X_one F 3)
  let yU : X F 3 :=
    (leftUpperRootLift F 3 1 2 (by decide) (-a)).val.2 y0
  have hSndU : X.snd yU = X.snd y0 :=
    G10TranslatedUpper_snd F a
  have hFstU : X.fst yU =
      Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne (-a) *
        Matrix.SpecialLinearGroup.transvection
          (show (2 : Fin 3) ≠ 0 by decide) (-1 : F) :=
    G10TranslatedUpper_fst F a
  have hSndApply :=
    leftLowerAdjacentRootLift_snd_apply F 3 fin3_01_covBy (-1 : F) yU
  have hTransNeg : (-(-1 : F)) = (1 : F) := by simp
  have hWeylFst :
      (Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3)
          fin3_01_covBy.ne (1 : Fˣ))⁻¹ * X.fst yU =
        (Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3)
            fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne (-a) *
            Matrix.SpecialLinearGroup.transvection
              (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)) := by
    rw [hFstU]
  have hTransFst :
      Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne (-(-1 : F)) *
        (Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3)
            fin3_01_covBy.ne (1 : Fˣ))⁻¹ * X.fst yU =
        Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne (1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3)
              fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne (-a) *
              Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))) := by
    rw [hTransNeg, hFstU, mul_assoc]
  have hEq : X.snd
      ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F)).val.2
        ((leftUpperRootLift F 3 1 2 (by decide) (-a)).val.2
          (((leftLowerRootLift20 F (1 : F))⁻¹).val.2 (X_one F 3)))) =
      X.snd ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F)).val.2 yU) := rfl
  calc X.snd
          ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F)).val.2
            ((leftUpperRootLift F 3 1 2 (by decide) (-a)).val.2
              (((leftLowerRootLift20 F (1 : F))⁻¹).val.2 (X_one F 3))))
      = X.snd ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F)).val.2 yU) :=
        hEq
    _ = leftWeylMultiplier fin3_01_covBy
            (Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne
                (-(-1 : F)) *
              (Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3)
                  fin3_01_covBy.ne (1 : Fˣ))⁻¹ * X.fst yU) *
          (leftWeylMultiplier fin3_01_covBy
              ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3)
                  fin3_01_covBy.ne (1 : Fˣ))⁻¹ * X.fst yU))⁻¹ *
          X.snd yU := hSndApply
    _ = leftWeylMultiplier fin3_01_covBy
            (Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne (1 : F) *
              ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3)
                  fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
                (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne (-a) *
                  Matrix.SpecialLinearGroup.transvection
                    (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))) *
          (leftWeylMultiplier fin3_01_covBy
              ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3)
                  fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
                (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne (-a) *
                  Matrix.SpecialLinearGroup.transvection
                    (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))))⁻¹ *
          X.snd yU := by
        rw [hTransFst, hWeylFst]
    _ = weylHMTits F 3 0 1 fin3_01_covBy.ne 1 *
          (weylHMTits F 3 0 1 fin3_01_covBy.ne 1)⁻¹ *
          X.snd yU := by
        have hM1 := leftWeylMultiplier_G10TranslatedStageOne_C1_aux F a
        have hM0 := leftWeylMultiplier_G10TranslatedStageOne_C0_aux F a
        rw [hM1, hM0]
    _ = X.snd yU := by
        rw [mul_inv_cancel, one_mul]
    _ = X.snd y0 := hSndU

end G10TranslatedStageOne

section G10TranslatedStageTwo

theorem G10TranslatedStageTwo_fst
    (F : Type u) [Field F] (a : F) :
    X.fst
        ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F)).val.2
          ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F)).val.2
            ((leftUpperRootLift F 3 1 2 (by decide) (-a)).val.2
              (((leftLowerRootLift20 F (1 : F))⁻¹).val.2 (X_one F 3))))) =
      Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne.symm (-1 : F) *
        (Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne.symm (-1 : F) *
          (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne (-a) *
            Matrix.SpecialLinearGroup.transvection
              (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))) := by
  let yU : X F 3 :=
    (leftUpperRootLift F 3 1 2 (by decide) (-a)).val.2
      (((leftLowerRootLift20 F (1 : F))⁻¹).val.2 (X_one F 3))
  let y1 : X F 3 :=
    (leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F)).val.2 yU
  have hFstU := G10TranslatedUpper_fst F a
  have hFst1 := G10TranslatedStageOne_fst F a
  have hFstU_eq : X.fst yU =
      Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne (-a) *
        Matrix.SpecialLinearGroup.transvection
          (show (2 : Fin 3) ≠ 0 by decide) (-1 : F) := hFstU
  have hFst1_eq : X.fst y1 =
      Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne.symm (-1 : F) *
        (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne (-a) *
          Matrix.SpecialLinearGroup.transvection
            (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)) := hFst1
  have hFst12 :=
    leftLowerAdjacentRootLift_fst_apply F 3 fin3_12_covBy (-1 : F) y1
  calc X.fst
          ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F)).val.2
            ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F)).val.2
              ((leftUpperRootLift F 3 1 2 (by decide) (-a)).val.2
                (((leftLowerRootLift20 F (1 : F))⁻¹).val.2 (X_one F 3)))))
      = X.fst ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F)).val.2 y1) :=
        rfl
    _ = Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne.symm (-1 : F) *
          X.fst y1 := hFst12
    _ = Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne.symm (-1 : F) *
          (Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne.symm (-1 : F) *
            (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne (-a) *
              Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))) := by
        rw [hFst1_eq]
theorem G10TranslatedStageTwo_snd_one
    (F : Type u) [Field F] :
    X.snd
        ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F)).val.2
          ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F)).val.2
            ((leftUpperRootLift F 3 1 2 (by decide)
                (-(1 : F))).val.2
              (((leftLowerRootLift20 F (1 : F))⁻¹).val.2 (X_one F 3))))) =
      X.snd (((leftLowerRootLift20 F (1 : F))⁻¹).val.2 (X_one F 3)) := by
  let y0 : X F 3 :=
    ((leftLowerRootLift20 F (1 : F))⁻¹).val.2 (X_one F 3)
  let yU : X F 3 :=
    (leftUpperRootLift F 3 1 2 (by decide) (-(1 : F))).val.2 y0
  let y1 : X F 3 :=
    (leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F)).val.2 yU
  have hSndU : X.snd yU = X.snd y0 :=
    G10TranslatedUpper_snd F 1
  have hFstU : X.fst yU =
      Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne (-(1 : F)) *
        Matrix.SpecialLinearGroup.transvection
          (show (2 : Fin 3) ≠ 0 by decide) (-1 : F) :=
    G10TranslatedUpper_fst F 1
  have hSnd1 : X.snd y1 = X.snd y0 := by
    have h := G10TranslatedStageOne_snd F 1
    calc X.snd y1
        = X.snd
            ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F)).val.2
              ((leftUpperRootLift F 3 1 2 (by decide) (-(1 : F))).val.2
                (((leftLowerRootLift20 F (1 : F))⁻¹).val.2 (X_one F 3)))) := rfl
      _ = X.snd y0 := h
  have hFst1 : X.fst y1 =
      Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne.symm (-1 : F) *
        (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne (-(1 : F)) *
          Matrix.SpecialLinearGroup.transvection
            (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)) :=
    G10TranslatedStageOne_fst F 1
  have hNegOne : (-(1 : F)) = (-1 : F) := by simp
  have hFst1Rewrite : X.fst y1 =
      Matrix.SpecialLinearGroup.transvection
          (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
        (Matrix.SpecialLinearGroup.transvection
            (show (1 : Fin 3) ≠ 2 by decide) (-1 : F) *
          Matrix.SpecialLinearGroup.transvection
            (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)) := by
    calc X.fst y1
        = Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne.symm (-1 : F) *
            (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne (-(1 : F)) *
              Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)) := hFst1
      _ = Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne.symm (-1 : F) *
            (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne (-1 : F) *
              Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)) := by
          rw [hNegOne]
      _ = _ := by
          have hEq10 : Matrix.SpecialLinearGroup.transvection
              fin3_01_covBy.ne.symm (-1 : F) =
              Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) := by
            apply Subtype.ext; rfl
          have hEq12 : Matrix.SpecialLinearGroup.transvection
              fin3_12_covBy.ne (-1 : F) =
              Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 2 by decide) (-1 : F) := by
            apply Subtype.ext; rfl
          rw [hEq10, hEq12]
  have hSndApply :=
    leftLowerAdjacentRootLift_snd_apply F 3 fin3_12_covBy (-1 : F) y1
  have hTransNeg : (-(-1 : F)) = (1 : F) := by simp
  have hWeylFst :
      (Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3)
          fin3_12_covBy.ne (1 : Fˣ))⁻¹ * X.fst y1 =
        (Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3)
            fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 2 by decide) (-1 : F) *
              Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))) := by
    rw [hFst1Rewrite]
  have hTransFst :
      Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne (-(-1 : F)) *
        (Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3)
            fin3_12_covBy.ne (1 : Fˣ))⁻¹ * X.fst y1 =
        Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne (1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3)
              fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 2 by decide) (-1 : F) *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))) := by
    rw [hTransNeg, hFst1Rewrite, mul_assoc]
  calc X.snd
          ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F)).val.2
            ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F)).val.2
              ((leftUpperRootLift F 3 1 2 (by decide) (-(1 : F))).val.2
                (((leftLowerRootLift20 F (1 : F))⁻¹).val.2 (X_one F 3)))))
      = X.snd ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F)).val.2 y1) := rfl
    _ = leftWeylMultiplier fin3_12_covBy
            (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne
                (-(-1 : F)) *
              (Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3)
                  fin3_12_covBy.ne (1 : Fˣ))⁻¹ * X.fst y1) *
          (leftWeylMultiplier fin3_12_covBy
              ((Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3)
                  fin3_12_covBy.ne (1 : Fˣ))⁻¹ * X.fst y1))⁻¹ *
          X.snd y1 := hSndApply
    _ = leftWeylMultiplier fin3_12_covBy
            (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne (1 : F) *
              ((Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3)
                  fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
                (Matrix.SpecialLinearGroup.transvection
                    (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                  (Matrix.SpecialLinearGroup.transvection
                      (show (1 : Fin 3) ≠ 2 by decide) (-1 : F) *
                    Matrix.SpecialLinearGroup.transvection
                      (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))))) *
          (leftWeylMultiplier fin3_12_covBy
              ((Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3)
                  fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
                (Matrix.SpecialLinearGroup.transvection
                    (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                  (Matrix.SpecialLinearGroup.transvection
                      (show (1 : Fin 3) ≠ 2 by decide) (-1 : F) *
                    Matrix.SpecialLinearGroup.transvection
                      (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))))⁻¹ *
          X.snd y1 := by
        rw [hTransFst, hWeylFst]
    _ = weylHMTits F 3 1 2 fin3_12_covBy.ne 1 *
          (weylHMTits F 3 1 2 fin3_12_covBy.ne 1)⁻¹ *
          X.snd y1 := by
        have hM1 := leftWeylMultiplier_G10TranslatedStageTwo_exc_C1 F
        have hM0 := leftWeylMultiplier_G10TranslatedStageTwo_exc_C0 F
        rw [hM1, hM0]
    _ = X.snd y1 := by
        rw [mul_inv_cancel, one_mul]
    _ = X.snd y0 := hSnd1

theorem G10TranslatedStageTwo_snd_zero
    (F : Type u) [Field F] :
    X.snd
        ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F)).val.2
          ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F)).val.2
            ((leftUpperRootLift F 3 1 2 (by decide) (-(0 : F))).val.2
              (((leftLowerRootLift20 F (1 : F))⁻¹).val.2 (X_one F 3))))) =
      (weylHMTits F 3 1 2 fin3_12_covBy.ne 1 *
        hTits F 3 1 2 fin3_12_covBy.ne 1) *
        X.snd (((leftLowerRootLift20 F (1 : F))⁻¹).val.2 (X_one F 3)) := by
  let y0 : X F 3 :=
    ((leftLowerRootLift20 F (1 : F))⁻¹).val.2 (X_one F 3)
  let yU : X F 3 :=
    (leftUpperRootLift F 3 1 2 (by decide) (-(0 : F))).val.2 y0
  let y1 : X F 3 :=
    (leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F)).val.2 yU
  have hFstU : X.fst yU =
      Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne (-(0 : F)) *
        Matrix.SpecialLinearGroup.transvection
          (show (2 : Fin 3) ≠ 0 by decide) (-1 : F) :=
    G10TranslatedUpper_fst F 0
  have hFst1 : X.fst y1 =
      Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne.symm (-1 : F) *
        (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne (-(0 : F)) *
          Matrix.SpecialLinearGroup.transvection
            (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)) := by
    have hFst01 :=
      leftLowerAdjacentRootLift_fst_apply F 3 fin3_01_covBy (-1 : F) yU
    calc X.fst y1
        = X.fst ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F)).val.2 yU) := rfl
      _ = Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne.symm (-1 : F) *
            X.fst yU := hFst01
      _ = _ := by rw [hFstU]
  have hSnd1 : X.snd y1 = X.snd y0 :=
    G10TranslatedStageOne_snd F 0
  have hFst1Rewrite : X.fst y1 =
      Matrix.SpecialLinearGroup.transvection
          (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
        (Matrix.SpecialLinearGroup.transvection
            (show (1 : Fin 3) ≠ 2 by decide) (-(0 : F)) *
          Matrix.SpecialLinearGroup.transvection
            (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)) := by
    calc X.fst y1
        = Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne.symm (-1 : F) *
            (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne (-(0 : F)) *
              Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)) := hFst1
      _ = _ := by
          have hEq10 : Matrix.SpecialLinearGroup.transvection
              fin3_01_covBy.ne.symm (-1 : F) =
              Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) := by
            apply Subtype.ext; rfl
          have hEq12 : Matrix.SpecialLinearGroup.transvection
              fin3_12_covBy.ne (-(0 : F)) =
              Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 2 by decide) (-(0 : F)) := by
            apply Subtype.ext; rfl
          rw [hEq10, hEq12]
  have hSndApply :=
    leftLowerAdjacentRootLift_snd_apply F 3 fin3_12_covBy (-1 : F) y1
  have hTransNeg : (-(-1 : F)) = (1 : F) := by simp
  have hWeylFst :
      (Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3)
          fin3_12_covBy.ne (1 : Fˣ))⁻¹ * X.fst y1 =
        (Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3)
            fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 2 by decide) (-(0 : F)) *
              Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))) := by
    rw [hFst1Rewrite]
  have hTransFst :
      Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne (-(-1 : F)) *
        (Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3)
            fin3_12_covBy.ne (1 : Fˣ))⁻¹ * X.fst y1 =
        Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne (1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3)
              fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 2 by decide) (-(0 : F)) *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))) := by
    rw [hTransNeg, hFst1Rewrite, mul_assoc]
  calc X.snd
          ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F)).val.2
            ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F)).val.2
              ((leftUpperRootLift F 3 1 2 (by decide) (-(0 : F))).val.2
                (((leftLowerRootLift20 F (1 : F))⁻¹).val.2 (X_one F 3)))))
      = X.snd ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F)).val.2 y1) := rfl
    _ = leftWeylMultiplier fin3_12_covBy
            (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne
                (-(-1 : F)) *
              (Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3)
                  fin3_12_covBy.ne (1 : Fˣ))⁻¹ * X.fst y1) *
          (leftWeylMultiplier fin3_12_covBy
              ((Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3)
                  fin3_12_covBy.ne (1 : Fˣ))⁻¹ * X.fst y1))⁻¹ *
          X.snd y1 := hSndApply
    _ = leftWeylMultiplier fin3_12_covBy
            (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne (1 : F) *
              ((Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3)
                  fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
                (Matrix.SpecialLinearGroup.transvection
                    (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                  (Matrix.SpecialLinearGroup.transvection
                      (show (1 : Fin 3) ≠ 2 by decide) (-(0 : F)) *
                    Matrix.SpecialLinearGroup.transvection
                      (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))))) *
          (leftWeylMultiplier fin3_12_covBy
              ((Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3)
                  fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
                (Matrix.SpecialLinearGroup.transvection
                    (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                  (Matrix.SpecialLinearGroup.transvection
                      (show (1 : Fin 3) ≠ 2 by decide) (-(0 : F)) *
                    Matrix.SpecialLinearGroup.transvection
                      (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))))⁻¹ *
          X.snd y1 := by
        rw [hTransFst, hWeylFst]
    _ = weylHMTits F 3 1 2 fin3_12_covBy.ne 1 *
          ((hTits F 3 1 2 fin3_12_covBy.ne 1)⁻¹)⁻¹ *
          X.snd y1 := by
        have hM1 := leftWeylMultiplier_G10TranslatedStageTwo_zero_C1 F
        have hM0 := leftWeylMultiplier_G10TranslatedStageTwo_zero_C0 F
        rw [hM1, hM0]
    _ = (weylHMTits F 3 1 2 fin3_12_covBy.ne 1 *
          hTits F 3 1 2 fin3_12_covBy.ne 1) *
          X.snd y1 := by
        rw [inv_inv, mul_assoc]
    _ = (weylHMTits F 3 1 2 fin3_12_covBy.ne 1 *
          hTits F 3 1 2 fin3_12_covBy.ne 1) *
          X.snd y0 := by
        rw [hSnd1]

theorem G10TranslatedStageTwo_snd_generic
    (F : Type u) [Field F] (a : F) (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    let hOneSub : (1 - a) ≠ 0 := sub_ne_zero.mpr (Ne.symm ha1);
    let hRatio : a / (1 - a) ≠ 0 :=
      div_ne_zero ha0 hOneSub;
    X.snd
        ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F)).val.2
          ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F)).val.2
            ((leftUpperRootLift F 3 1 2 (by decide) (-a)).val.2
              (((leftLowerRootLift20 F (1 : F))⁻¹).val.2 (X_one F 3))))) =
      ((hTits F 3 1 2 fin3_12_covBy.ne
          (Units.mk0 (a / (1 - a)) hRatio))⁻¹ *
        hTits F 3 1 2 fin3_12_covBy.ne
          ((Units.mk0 (1 - a) hOneSub)⁻¹)) *
        X.snd (((leftLowerRootLift20 F (1 : F))⁻¹).val.2 (X_one F 3)) := by
  intro hOneSub hRatio
  let y0 : X F 3 :=
    ((leftLowerRootLift20 F (1 : F))⁻¹).val.2 (X_one F 3)
  let yU : X F 3 :=
    (leftUpperRootLift F 3 1 2 (by decide) (-a)).val.2 y0
  let y1 : X F 3 :=
    (leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F)).val.2 yU
  have hFst1 : X.fst y1 =
      Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne.symm (-1 : F) *
        (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne (-a) *
          Matrix.SpecialLinearGroup.transvection
            (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)) :=
    G10TranslatedStageOne_fst F a
  have hSnd1 : X.snd y1 = X.snd y0 :=
    G10TranslatedStageOne_snd F a
  have hFst1Rewrite : X.fst y1 =
      Matrix.SpecialLinearGroup.transvection
          (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
        (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne (-a) *
          Matrix.SpecialLinearGroup.transvection
            (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)) := by
    calc X.fst y1
        = Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne.symm (-1 : F) *
            (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne (-a) *
              Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)) := hFst1
      _ = _ := by
          have hEq : Matrix.SpecialLinearGroup.transvection
              fin3_01_covBy.ne.symm (-1 : F) =
              Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) := by
            apply Subtype.ext; rfl
          rw [hEq]
  have hSub : a - 1 ≠ 0 := sub_ne_zero.mpr ha1
  have hInvNe : (a - 1)⁻¹ ≠ 0 := inv_ne_zero hSub
  have hDivNe : a / (a - 1) ≠ 0 := div_ne_zero ha0 hSub
  have hSndApply :=
    leftLowerAdjacentRootLift_snd_apply F 3 fin3_12_covBy (-1 : F) y1
  have hTransNeg : (-(-1 : F)) = (1 : F) := by simp
  have hWeylFst :
      (Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3)
          fin3_12_covBy.ne (1 : Fˣ))⁻¹ * X.fst y1 =
        (Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3)
            fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
            (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne (-a) *
              Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))) := by
    rw [hFst1Rewrite]
  have hTransFst :
      Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne (-(-1 : F)) *
        (Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3)
            fin3_12_covBy.ne (1 : Fˣ))⁻¹ * X.fst y1 =
        Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne (1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3)
              fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne (-a) *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))) := by
    rw [hTransNeg, hFst1Rewrite, mul_assoc]
  have hUnitInv :
      torusUnitOfNegCoeff ((a - 1)⁻¹) hInvNe =
        (Units.mk0 (1 - a) hOneSub)⁻¹ :=
    torusUnitOfNegCoeff_inv_one_sub F a ha1 hInvNe hOneSub
  have hUnitDiv :
      torusUnitOfNegCoeff (a / (a - 1)) hDivNe =
        Units.mk0 (a / (1 - a)) hRatio :=
    torusUnitOfNegCoeff_div_ratio F a ha0 ha1 hDivNe hRatio
  have hM1 :=
    leftWeylMultiplier_G10TranslatedStageTwo_gen_C1 F a ha0 ha1
  have hM0 :=
    leftWeylMultiplier_G10TranslatedStageTwo_gen_C0 F a ha1
  calc X.snd
          ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F)).val.2
            ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F)).val.2
              ((leftUpperRootLift F 3 1 2 (by decide) (-a)).val.2
                (((leftLowerRootLift20 F (1 : F))⁻¹).val.2 (X_one F 3)))))
      = X.snd ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F)).val.2 y1) := rfl
    _ = leftWeylMultiplier fin3_12_covBy
            (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne
                (-(-1 : F)) *
              (Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3)
                  fin3_12_covBy.ne (1 : Fˣ))⁻¹ * X.fst y1) *
          (leftWeylMultiplier fin3_12_covBy
              ((Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3)
                  fin3_12_covBy.ne (1 : Fˣ))⁻¹ * X.fst y1))⁻¹ *
          X.snd y1 := hSndApply
    _ = leftWeylMultiplier fin3_12_covBy
            (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne (1 : F) *
              ((Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3)
                  fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
                (Matrix.SpecialLinearGroup.transvection
                    (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                  (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne (-a) *
                    Matrix.SpecialLinearGroup.transvection
                      (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))))) *
          (leftWeylMultiplier fin3_12_covBy
              ((Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3)
                  fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
                (Matrix.SpecialLinearGroup.transvection
                    (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                  (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne (-a) *
                    Matrix.SpecialLinearGroup.transvection
                      (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))))⁻¹ *
          X.snd y1 := by
        rw [hTransFst, hWeylFst]
    _ = (hTits F 3 1 2 fin3_12_covBy.ne
            (torusUnitOfNegCoeff (a / (a - 1)) hDivNe))⁻¹ *
          hTits F 3 1 2 fin3_12_covBy.ne
            (torusUnitOfNegCoeff ((a - 1)⁻¹) hInvNe) *
          X.snd y1 := by
        rw [hM1, hM0, inv_inv, mul_assoc]
    _ = ((hTits F 3 1 2 fin3_12_covBy.ne
            (Units.mk0 (a / (1 - a)) hRatio))⁻¹ *
          hTits F 3 1 2 fin3_12_covBy.ne
            ((Units.mk0 (1 - a) hOneSub)⁻¹)) *
          X.snd y1 := by
        rw [hUnitDiv, hUnitInv]
    _ = ((hTits F 3 1 2 fin3_12_covBy.ne
            (Units.mk0 (a / (1 - a)) hRatio))⁻¹ *
          hTits F 3 1 2 fin3_12_covBy.ne
            ((Units.mk0 (1 - a) hOneSub)⁻¹)) *
          X.snd y0 := by
        rw [hSnd1]

end G10TranslatedStageTwo

section G10TranslatedStageThreeHelpers

private theorem torusUnitOfNegCoeff_one
    {F : Type u} [Field F] (h : (1 : F) ≠ 0) :
    torusUnitOfNegCoeff (1 : F) h = (-1 : Fˣ) := by
  apply Units.ext
  simp [torusUnitOfNegCoeff]

private theorem leftWeylMultiplier_G10TranslatedStageThree_gen_C0
    (F : Type u) [Field F] (a : F) (ha0 : a ≠ 0) :
    leftWeylMultiplier (F := F) (n := 3) fin3_01_covBy
        ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3)
            fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 2 by decide) (-a) *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))))) =
      (hTits F 3 (0 : Fin 3) (1 : Fin 3) fin3_01_covBy.ne
          (-1 : Fˣ))⁻¹ := by
  have hCoeff :=
    leftSimpleRootCoeff_G10TranslatedStageThree_C0 F a ha0
      fin3_01_covBy
  have hNotPos :=
    bruhatMiddle_G10TranslatedStageThree_C0_not_pos F a ha0
      fin3_01_covBy
  have hNe :
      leftSimpleRootCoeff F 3
          ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3)
              fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                (Matrix.SpecialLinearGroup.transvection
                    (show (1 : Fin 3) ≠ 2 by decide) (-a) *
                  Matrix.SpecialLinearGroup.transvection
                    (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))))
          fin3_01_covBy ≠ 0 := by
    rw [hCoeff]
    exact one_ne_zero
  have hMul :=
    leftWeylMultiplier_of_neg fin3_01_covBy _ hNe hNotPos
  have hOneNe : (1 : F) ≠ 0 := one_ne_zero
  have hUnits : torusUnitOfNegCoeff (1 : F) hOneNe = (-1 : Fˣ) :=
    torusUnitOfNegCoeff_one hOneNe
  have hUnitsEq :
      torusUnitOfNegCoeff
          (leftSimpleRootCoeff F 3
            ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3)
                (1 : Fin 3) fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
              (Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
                (Matrix.SpecialLinearGroup.transvection
                    (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                  (Matrix.SpecialLinearGroup.transvection
                      (show (1 : Fin 3) ≠ 2 by decide) (-a) *
                    Matrix.SpecialLinearGroup.transvection
                      (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))))
            fin3_01_covBy) hNe = (-1 : Fˣ) := by
    have hEq :
        torusUnitOfNegCoeff
            (leftSimpleRootCoeff F 3
              ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3)
                  (1 : Fin 3) fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
                (Matrix.SpecialLinearGroup.transvection
                    (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
                  (Matrix.SpecialLinearGroup.transvection
                      (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                    (Matrix.SpecialLinearGroup.transvection
                        (show (1 : Fin 3) ≠ 2 by decide) (-a) *
                      Matrix.SpecialLinearGroup.transvection
                        (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))))
              fin3_01_covBy) hNe =
          torusUnitOfNegCoeff (1 : F) hOneNe := by
      apply Units.ext
      simp [torusUnitOfNegCoeff, hCoeff]
    rw [hEq, hUnits]
  rw [hUnitsEq] at hMul
  exact hMul

private theorem leftWeylMultiplier_G10TranslatedStageThree_gen_C1
    (F : Type u) [Field F] (a : F) (ha0 : a ≠ 0) :
    leftWeylMultiplier (F := F) (n := 3) fin3_01_covBy
        (Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne
            (-1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3)
              fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                (Matrix.SpecialLinearGroup.transvection
                    (show (1 : Fin 3) ≠ 2 by decide) (-a) *
                  Matrix.SpecialLinearGroup.transvection
                    (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))))) =
      weylHMTits F 3 (0 : Fin 3) (1 : Fin 3) fin3_01_covBy.ne 1 := by
  have hCoeff :=
    leftSimpleRootCoeff_G10TranslatedStageThree_C1 F a ha0
      fin3_01_covBy
  exact leftWeylMultiplier_of_zero fin3_01_covBy _ hCoeff

private theorem leftWeylMultiplier_G10TranslatedStageThree_zero_C0
    (F : Type u) [Field F] :
    leftWeylMultiplier (F := F) (n := 3) fin3_01_covBy
        ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3)
            fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
              Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))) =
      (hTits F 3 (0 : Fin 3) (1 : Fin 3) fin3_01_covBy.ne
          (-1 : Fˣ))⁻¹ := by
  have hCoeff :=
    leftSimpleRootCoeff_G10TranslatedStageThree_zero_C0 F
      fin3_01_covBy
  have hNotPos :=
    bruhatMiddle_G10TranslatedStageThree_zero_C0_not_pos F
      fin3_01_covBy
  have hNe :
      leftSimpleRootCoeff F 3
          ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3)
              fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))))
          fin3_01_covBy ≠ 0 := by
    rw [hCoeff]
    exact one_ne_zero
  have hMul :=
    leftWeylMultiplier_of_neg fin3_01_covBy _ hNe hNotPos
  have hOneNe : (1 : F) ≠ 0 := one_ne_zero
  have hUnits : torusUnitOfNegCoeff (1 : F) hOneNe = (-1 : Fˣ) :=
    torusUnitOfNegCoeff_one hOneNe
  have hUnitsEq :
      torusUnitOfNegCoeff
          (leftSimpleRootCoeff F 3
            ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3)
                (1 : Fin 3) fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
              (Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
                (Matrix.SpecialLinearGroup.transvection
                    (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                  Matrix.SpecialLinearGroup.transvection
                    (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))))
            fin3_01_covBy) hNe = (-1 : Fˣ) := by
    have hEq :
        torusUnitOfNegCoeff
            (leftSimpleRootCoeff F 3
              ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3)
                  (1 : Fin 3) fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
                (Matrix.SpecialLinearGroup.transvection
                    (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
                  (Matrix.SpecialLinearGroup.transvection
                      (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                    Matrix.SpecialLinearGroup.transvection
                      (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))))
              fin3_01_covBy) hNe =
          torusUnitOfNegCoeff (1 : F) hOneNe := by
      apply Units.ext
      simp [torusUnitOfNegCoeff, hCoeff]
    rw [hEq, hUnits]
  rw [hUnitsEq] at hMul
  exact hMul

private theorem leftWeylMultiplier_G10TranslatedStageThree_zero_C1
    (F : Type u) [Field F] :
    leftWeylMultiplier (F := F) (n := 3) fin3_01_covBy
        (Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne
            (-1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3)
              fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))))) =
      weylHMTits F 3 (0 : Fin 3) (1 : Fin 3) fin3_01_covBy.ne 1 := by
  have hCoeff :=
    leftSimpleRootCoeff_G10TranslatedStageThree_zero_C1 F
      fin3_01_covBy
  exact leftWeylMultiplier_of_zero fin3_01_covBy _ hCoeff

end G10TranslatedStageThreeHelpers

section G10TranslatedStageThree

theorem G10TranslatedStageThree_fst
    (F : Type u) [Field F] (a : F) :
    X.fst
        ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (1 : F)).val.2
          ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F)).val.2
            ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F)).val.2
              ((leftUpperRootLift F 3 1 2 (by decide) (-a)).val.2
                (((leftLowerRootLift20 F (1 : F))⁻¹).val.2
                  (X_one F 3)))))) =
      Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne.symm
          (1 : F) *
        (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne.symm
            (-1 : F) *
          (Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne.symm
              (-1 : F) *
            (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne (-a) *
              Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))) := by
  let y2 : X F 3 :=
    (leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F)).val.2
      ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F)).val.2
        ((leftUpperRootLift F 3 1 2 (by decide) (-a)).val.2
          (((leftLowerRootLift20 F (1 : F))⁻¹).val.2 (X_one F 3))))
  have hFstY2 :=
    G10TranslatedStageTwo_fst (F := F) a
  have hFstLift :=
    leftLowerAdjacentRootLift_fst_apply F 3 fin3_01_covBy (1 : F) y2
  calc X.fst
          ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (1 : F)).val.2
            ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F)).val.2
              ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F)).val.2
                ((leftUpperRootLift F 3 1 2 (by decide) (-a)).val.2
                  (((leftLowerRootLift20 F (1 : F))⁻¹).val.2
                    (X_one F 3))))))
      = Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne.symm
            (1 : F) * X.fst y2 := hFstLift
    _ = Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne.symm
            (1 : F) *
          (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne.symm
              (-1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                fin3_01_covBy.ne.symm (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne
                  (-a) *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))) := by
          rw [hFstY2]

theorem G10TranslatedStageThree_snd
    (F : Type u) [Field F] (a : F) :
    X.snd
        ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (1 : F)).val.2
          ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F)).val.2
            ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F)).val.2
              ((leftUpperRootLift F 3 1 2 (by decide) (-a)).val.2
                (((leftLowerRootLift20 F (1 : F))⁻¹).val.2
                  (X_one F 3)))))) =
      (weylHMTits F 3 (0 : Fin 3) (1 : Fin 3) fin3_01_covBy.ne
          (1 : Fˣ) *
        hTits F 3 (0 : Fin 3) (1 : Fin 3) fin3_01_covBy.ne
          (-1 : Fˣ)) *
        X.snd
          ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F)).val.2
            ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F)).val.2
              ((leftUpperRootLift F 3 1 2 (by decide) (-a)).val.2
                (((leftLowerRootLift20 F (1 : F))⁻¹).val.2
                  (X_one F 3))))) := by
  let y2 : X F 3 :=
    (leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F)).val.2
      ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F)).val.2
        ((leftUpperRootLift F 3 1 2 (by decide) (-a)).val.2
          (((leftLowerRootLift20 F (1 : F))⁻¹).val.2 (X_one F 3))))
  have hFstY2 :=
    G10TranslatedStageTwo_fst (F := F) a
  have hSndApply :=
    leftLowerAdjacentRootLift_snd_apply F 3 fin3_01_covBy (1 : F) y2
  have hTransNeg : (-(1 : F)) = (-1 : F) := by simp
  have hWeylFst :
      (Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3)
          fin3_01_covBy.ne (1 : Fˣ))⁻¹ * X.fst y2 =
        (Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3)
            fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne.symm
              (-1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                fin3_01_covBy.ne.symm (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne
                  (-a) *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))) := by
    rw [hFstY2]
  have hTransFst :
      Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne
          (-(1 : F)) *
        (Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3)
            fin3_01_covBy.ne (1 : Fˣ))⁻¹ * X.fst y2 =
        Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne
            (-1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3)
              fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                fin3_12_covBy.ne.symm (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  fin3_01_covBy.ne.symm (-1 : F) *
                (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne
                    (-a) *
                  Matrix.SpecialLinearGroup.transvection
                    (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))))) := by
    rw [hTransNeg, hFstY2, mul_assoc]
  have hResult :
      X.snd ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (1 : F)).val.2 y2) =
        leftWeylMultiplier (F := F) fin3_01_covBy
            (Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne
                (-(1 : F)) *
              (Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3)
                  fin3_01_covBy.ne (1 : Fˣ))⁻¹ * X.fst y2) *
          (leftWeylMultiplier (F := F) fin3_01_covBy
              ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3)
                  (1 : Fin 3) fin3_01_covBy.ne (1 : Fˣ))⁻¹ * X.fst y2))⁻¹ *
          X.snd y2 := hSndApply
  by_cases ha0 : a = 0
  · have hT12Zero :
        Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne
            (-(0 : F)) = 1 := by
      have hZero : (-(0 : F)) = (0 : F) := by simp
      rw [hZero]
      exact Matrix.SpecialLinearGroup.transvection_coeff_zero
        fin3_12_covBy.ne
    have hT12ShowZero :
        Matrix.SpecialLinearGroup.transvection
            (show (1 : Fin 3) ≠ 2 by decide) (-(0 : F)) = 1 := by
      have hZero : (-(0 : F)) = (0 : F) := by simp
      rw [hZero]
      exact Matrix.SpecialLinearGroup.transvection_coeff_zero
        (show (1 : Fin 3) ≠ 2 by decide)
    have hP3ZeroSimpl :
        Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne.symm
            (-1 : F) *
          (Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne.symm
              (-1 : F) *
            (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne
                (-(0 : F)) *
              Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))) =
        Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne.symm
            (-1 : F) *
          (Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne.symm
              (-1 : F) *
            Matrix.SpecialLinearGroup.transvection
              (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)) := by
      calc Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne.symm
              (-1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                fin3_01_covBy.ne.symm (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne
                  (-(0 : F)) *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))
          = Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne.symm
                (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  fin3_01_covBy.ne.symm (-1 : F) *
                (1 *
                  Matrix.SpecialLinearGroup.transvection
                    (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))) := by
            rw [hT12Zero]
        _ = _ := by
            rw [one_mul]
    have hP3GenericZeroEq :
        Matrix.SpecialLinearGroup.transvection
            (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
          (Matrix.SpecialLinearGroup.transvection
              (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 2 by decide) (-(0 : F)) *
              Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))) =
        Matrix.SpecialLinearGroup.transvection
            (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
          (Matrix.SpecialLinearGroup.transvection
              (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
            Matrix.SpecialLinearGroup.transvection
              (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)) := by
      calc Matrix.SpecialLinearGroup.transvection
              (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 2 by decide) (-(0 : F)) *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))
          = Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                (1 *
                  Matrix.SpecialLinearGroup.transvection
                    (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))) := by
            rw [hT12ShowZero]
        _ = _ := by
            rw [one_mul]
    have hFstY2Zero : X.fst y2 =
        Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne.symm
            (-1 : F) *
          (Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne.symm
              (-1 : F) *
            Matrix.SpecialLinearGroup.transvection
              (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)) := by
      have h1 : X.fst y2 =
          Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne.symm
              (-1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                fin3_01_covBy.ne.symm (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne
                  (-a) *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))) :=
        hFstY2
      rw [ha0] at h1
      have h2 := hP3ZeroSimpl
      rw [h2] at h1
      exact h1
    have hWeylFstZero :
        (Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3)
            fin3_01_covBy.ne (1 : Fˣ))⁻¹ * X.fst y2 =
        (Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3)
            fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne.symm
              (-1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                fin3_01_covBy.ne.symm (-1 : F) *
              Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))) := by
      rw [hFstY2Zero]
    have hTransWeylFstZeroEq :
        (Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3)
            fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne.symm
              (-1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                fin3_01_covBy.ne.symm (-1 : F) *
              Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))) =
        (Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3)
            fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
              Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))) := by
      have h21 :
          Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne.symm
              (-1 : F) =
          Matrix.SpecialLinearGroup.transvection
              (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) := by
        apply Subtype.ext
        rfl
      have h10 :
          Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne.symm
              (-1 : F) =
          Matrix.SpecialLinearGroup.transvection
              (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) := by
        apply Subtype.ext
        rfl
      rw [h21, h10]
    have hTransFstZero :
        Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne
            (-(1 : F)) *
          (Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3)
              fin3_01_covBy.ne (1 : Fˣ))⁻¹ * X.fst y2 =
        Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne
            (-1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3)
              fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))) := by
      rw [hTransNeg, hFstY2Zero, hTransWeylFstZeroEq, mul_assoc]
    have hWeylFstZero' :
        (Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3)
            fin3_01_covBy.ne (1 : Fˣ))⁻¹ * X.fst y2 =
        (Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3)
            fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
              Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))) := by
      rw [hWeylFstZero, hTransWeylFstZeroEq]
    calc X.snd
            ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (1 : F)).val.2
              ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F)).val.2
                ((leftLowerAdjacentRootLift F 3 fin3_01_covBy
                    (-1 : F)).val.2
                  ((leftUpperRootLift F 3 1 2 (by decide) (-a)).val.2
                    (((leftLowerRootLift20 F (1 : F))⁻¹).val.2
                      (X_one F 3))))))
        = X.snd ((leftLowerAdjacentRootLift F 3 fin3_01_covBy
              (1 : F)).val.2 y2) := rfl
      _ = leftWeylMultiplier (F := F) fin3_01_covBy
              (Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne
                  (-(1 : F)) *
                (Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3)
                    (1 : Fin 3) fin3_01_covBy.ne (1 : Fˣ))⁻¹ * X.fst y2) *
            (leftWeylMultiplier (F := F) fin3_01_covBy
                ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3)
                    (1 : Fin 3) fin3_01_covBy.ne (1 : Fˣ))⁻¹ * X.fst y2))⁻¹ *
            X.snd y2 := hResult
      _ = leftWeylMultiplier (F := F) fin3_01_covBy
              (Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne
                  (-1 : F) *
                ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3)
                    (1 : Fin 3) fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
                  (Matrix.SpecialLinearGroup.transvection
                      (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
                    (Matrix.SpecialLinearGroup.transvection
                        (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                      Matrix.SpecialLinearGroup.transvection
                        (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))))) *
            (leftWeylMultiplier (F := F) fin3_01_covBy
                ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3)
                    (1 : Fin 3) fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
                  (Matrix.SpecialLinearGroup.transvection
                      (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
                    (Matrix.SpecialLinearGroup.transvection
                        (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                      Matrix.SpecialLinearGroup.transvection
                        (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))))⁻¹ *
            X.snd y2 := by
          rw [hTransFstZero, hWeylFstZero']
      _ = weylHMTits F 3 (0 : Fin 3) (1 : Fin 3) fin3_01_covBy.ne
              (1 : Fˣ) *
            ((hTits F 3 (0 : Fin 3) (1 : Fin 3) fin3_01_covBy.ne
                (-1 : Fˣ))⁻¹)⁻¹ *
            X.snd y2 := by
          have hMulC1 :=
            leftWeylMultiplier_G10TranslatedStageThree_zero_C1
              (F := F)
          have hMulC0 :=
            leftWeylMultiplier_G10TranslatedStageThree_zero_C0
              (F := F)
          rw [hMulC1, hMulC0]
      _ = (weylHMTits F 3 (0 : Fin 3) (1 : Fin 3) fin3_01_covBy.ne
              (1 : Fˣ) *
            hTits F 3 (0 : Fin 3) (1 : Fin 3) fin3_01_covBy.ne
              (-1 : Fˣ)) *
            X.snd y2 := by
          rw [inv_inv, mul_assoc]
  · have ha0Ne : a ≠ 0 := ha0
    have hWeylFstGen :
        (Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3)
            fin3_01_covBy.ne (1 : Fˣ))⁻¹ * X.fst y2 =
        (Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3)
            fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 2 by decide) (-a) *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))) := by
      have h21 :
          Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne.symm
              (-1 : F) =
          Matrix.SpecialLinearGroup.transvection
              (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) := by
        apply Subtype.ext
        rfl
      have h10 :
          Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne.symm
              (-1 : F) =
          Matrix.SpecialLinearGroup.transvection
              (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) := by
        apply Subtype.ext
        rfl
      have h12 :
          Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne
              (-a) =
          Matrix.SpecialLinearGroup.transvection
              (show (1 : Fin 3) ≠ 2 by decide) (-a) := by
        apply Subtype.ext
        rfl
      calc (Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3)
                (1 : Fin 3) fin3_01_covBy.ne (1 : Fˣ))⁻¹ * X.fst y2
          = (Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3)
                (1 : Fin 3) fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
              (Matrix.SpecialLinearGroup.transvection
                  fin3_12_covBy.ne.symm (-1 : F) *
                (Matrix.SpecialLinearGroup.transvection
                    fin3_01_covBy.ne.symm (-1 : F) *
                  (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne
                      (-a) *
                    Matrix.SpecialLinearGroup.transvection
                      (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))) := by
            rw [hFstY2]
        _ = (Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3)
                (1 : Fin 3) fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
              (Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
                (Matrix.SpecialLinearGroup.transvection
                    (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                  (Matrix.SpecialLinearGroup.transvection
                      (show (1 : Fin 3) ≠ 2 by decide) (-a) *
                    Matrix.SpecialLinearGroup.transvection
                      (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))) := by
            rw [h21, h10, h12]
    have hTransFstGen :
        Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne
            (-(1 : F)) *
          (Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3)
              fin3_01_covBy.ne (1 : Fˣ))⁻¹ * X.fst y2 =
        Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne
            (-1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3)
              fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                (Matrix.SpecialLinearGroup.transvection
                    (show (1 : Fin 3) ≠ 2 by decide) (-a) *
                  Matrix.SpecialLinearGroup.transvection
                    (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))))) := by
      calc Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne
              (-(1 : F)) *
            (Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3)
                fin3_01_covBy.ne (1 : Fˣ))⁻¹ * X.fst y2
          = Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne
                (-1 : F) *
              (Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3)
                  (1 : Fin 3) fin3_01_covBy.ne (1 : Fˣ))⁻¹ * X.fst y2 := by
            rw [hTransNeg]
        _ = Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne
                (-1 : F) *
              ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3)
                  (1 : Fin 3) fin3_01_covBy.ne (1 : Fˣ))⁻¹ * X.fst y2) := by
            rw [mul_assoc]
        _ = Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne
                (-1 : F) *
              ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3)
                  (1 : Fin 3) fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
                (Matrix.SpecialLinearGroup.transvection
                    (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
                  (Matrix.SpecialLinearGroup.transvection
                      (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                    (Matrix.SpecialLinearGroup.transvection
                        (show (1 : Fin 3) ≠ 2 by decide) (-a) *
                      Matrix.SpecialLinearGroup.transvection
                        (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))))) := by
            rw [hWeylFstGen]
    calc X.snd
            ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (1 : F)).val.2
              ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F)).val.2
                ((leftLowerAdjacentRootLift F 3 fin3_01_covBy
                    (-1 : F)).val.2
                  ((leftUpperRootLift F 3 1 2 (by decide) (-a)).val.2
                    (((leftLowerRootLift20 F (1 : F))⁻¹).val.2
                      (X_one F 3))))))
        = X.snd ((leftLowerAdjacentRootLift F 3 fin3_01_covBy
              (1 : F)).val.2 y2) := rfl
      _ = leftWeylMultiplier (F := F) fin3_01_covBy
              (Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne
                  (-(1 : F)) *
                (Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3)
                    (1 : Fin 3) fin3_01_covBy.ne (1 : Fˣ))⁻¹ * X.fst y2) *
            (leftWeylMultiplier (F := F) fin3_01_covBy
                ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3)
                    (1 : Fin 3) fin3_01_covBy.ne (1 : Fˣ))⁻¹ * X.fst y2))⁻¹ *
            X.snd y2 := hResult
      _ = leftWeylMultiplier (F := F) fin3_01_covBy
              (Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne
                  (-1 : F) *
                ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3)
                    (1 : Fin 3) fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
                  (Matrix.SpecialLinearGroup.transvection
                      (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
                    (Matrix.SpecialLinearGroup.transvection
                        (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                      (Matrix.SpecialLinearGroup.transvection
                          (show (1 : Fin 3) ≠ 2 by decide) (-a) *
                        Matrix.SpecialLinearGroup.transvection
                          (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))))) *
            (leftWeylMultiplier (F := F) fin3_01_covBy
                ((Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3)
                    (1 : Fin 3) fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
                  (Matrix.SpecialLinearGroup.transvection
                      (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
                    (Matrix.SpecialLinearGroup.transvection
                        (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                      (Matrix.SpecialLinearGroup.transvection
                          (show (1 : Fin 3) ≠ 2 by decide) (-a) *
                        Matrix.SpecialLinearGroup.transvection
                          (show (2 : Fin 3) ≠ 0 by decide)
                            (-1 : F))))))⁻¹ *
            X.snd y2 := by
          rw [hTransFstGen, hWeylFstGen]
      _ = weylHMTits F 3 (0 : Fin 3) (1 : Fin 3) fin3_01_covBy.ne
              (1 : Fˣ) *
            ((hTits F 3 (0 : Fin 3) (1 : Fin 3) fin3_01_covBy.ne
                (-1 : Fˣ))⁻¹)⁻¹ *
            X.snd y2 := by
          have hMulC1 :=
            leftWeylMultiplier_G10TranslatedStageThree_gen_C1 F a ha0Ne
          have hMulC0 :=
            leftWeylMultiplier_G10TranslatedStageThree_gen_C0 F a ha0Ne
          rw [hMulC1, hMulC0]
      _ = (weylHMTits F 3 (0 : Fin 3) (1 : Fin 3) fin3_01_covBy.ne
              (1 : Fˣ) *
            hTits F 3 (0 : Fin 3) (1 : Fin 3) fin3_01_covBy.ne
              (-1 : Fˣ)) *
            X.snd y2 := by
          rw [inv_inv, mul_assoc]

end G10TranslatedStageThree
section G10TranslatedStageFourHelpers

private theorem G10TranslatedStageFour_fst_matrix_aux
    (F : Type u) [Field F] (a : F) :
    Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne.symm
        (1 : F) *
      (Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne.symm
          (1 : F) *
        (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne.symm
            (-1 : F) *
          (Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne.symm
              (-1 : F) *
            (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne
                (-a) *
              Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))))) =
    Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne.symm a *
      Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne
        (-a) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three]

private def G10TranslatedStageFour_P4
    (F : Type u) [Field F] (a : F) :
    Matrix.SpecialLinearGroup (Fin 3) F :=
  Matrix.SpecialLinearGroup.transvection
      (show (1 : Fin 3) ≠ 0 by decide) (1 : F) *
    (Matrix.SpecialLinearGroup.transvection
        (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
      (Matrix.SpecialLinearGroup.transvection
          (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
        (Matrix.SpecialLinearGroup.transvection
            (show (1 : Fin 3) ≠ 2 by decide) (-a) *
          Matrix.SpecialLinearGroup.transvection
            (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))))

private def G10TranslatedStageFour_D0
    (F : Type u) [Field F] (a : F) :
    Matrix.SpecialLinearGroup (Fin 3) F :=
  (Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3)
      fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
    G10TranslatedStageFour_P4 (F := F) a

private def G10TranslatedStageFour_D1
    (F : Type u) [Field F] (a : F) :
    Matrix.SpecialLinearGroup (Fin 3) F :=
  Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne (-1 : F) *
    G10TranslatedStageFour_D0 (F := F) a

private theorem leftWeylMultiplier_G10TranslatedStageFour_gen_D0
    (F : Type u) [Field F] (a : F) (ha0 : a ≠ 0) :
    leftWeylMultiplier (F := F) (n := 3) fin3_12_covBy
        (G10TranslatedStageFour_D0 (F := F) a) =
      (hTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne
          (-1 : Fˣ))⁻¹ := by
  have hCoeff : leftSimpleRootCoeff F 3
      (G10TranslatedStageFour_D0 (F := F) a) fin3_12_covBy = 1 := by
    simpa [G10TranslatedStageFour_P4, G10TranslatedStageFour_D0] using
      leftSimpleRootCoeff_G10TranslatedStageFour_D0 F a ha0 fin3_12_covBy
  have hNotPos : ¬ ((Matrix.GeneralLinearGroup.bruhatMiddle
      (G10TranslatedStageFour_D0 (F := F) a) :
        MonomialBase Fˣ (Fin 3)).right.symm (1 : Fin 3) <
      (Matrix.GeneralLinearGroup.bruhatMiddle
        (G10TranslatedStageFour_D0 (F := F) a) :
        MonomialBase Fˣ (Fin 3)).right.symm (2 : Fin 3)) := by
    simpa [G10TranslatedStageFour_P4, G10TranslatedStageFour_D0] using
      bruhatMiddle_G10TranslatedStageFour_D0_not_pos F a ha0 fin3_12_covBy
  have hNe : leftSimpleRootCoeff F 3
      (G10TranslatedStageFour_D0 (F := F) a) fin3_12_covBy ≠ 0 := by
    rw [hCoeff]
    exact one_ne_zero
  have hMul :=
    leftWeylMultiplier_of_neg fin3_12_covBy
      (G10TranslatedStageFour_D0 (F := F) a) hNe hNotPos
  have hOneNe : (1 : F) ≠ 0 := one_ne_zero
  have hUnits : torusUnitOfNegCoeff (1 : F) hOneNe = (-1 : Fˣ) := by
    apply Units.ext
    simp [torusUnitOfNegCoeff]
  have hCoeffUnits :
      torusUnitOfNegCoeff
          (leftSimpleRootCoeff F 3
            (G10TranslatedStageFour_D0 (F := F) a) fin3_12_covBy) hNe =
        (-1 : Fˣ) := by
    have hEq :
        torusUnitOfNegCoeff
            (leftSimpleRootCoeff F 3
              (G10TranslatedStageFour_D0 (F := F) a) fin3_12_covBy) hNe =
          torusUnitOfNegCoeff (1 : F) hOneNe := by
      apply Units.ext
      simp [torusUnitOfNegCoeff, hCoeff]
    rw [hEq, hUnits]
  rw [hCoeffUnits] at hMul
  exact hMul

private theorem leftWeylMultiplier_G10TranslatedStageFour_gen_D1
    (F : Type u) [Field F] (a : F) (ha0 : a ≠ 0) :
    leftWeylMultiplier (F := F) (n := 3) fin3_12_covBy
        (G10TranslatedStageFour_D1 (F := F) a) =
      weylHMTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne 1 := by
  have hCoeff : leftSimpleRootCoeff F 3
      (G10TranslatedStageFour_D1 (F := F) a) fin3_12_covBy = 0 := by
    simpa [G10TranslatedStageFour_P4, G10TranslatedStageFour_D0,
      G10TranslatedStageFour_D1] using
      leftSimpleRootCoeff_G10TranslatedStageFour_D1 F a ha0 fin3_12_covBy
  exact leftWeylMultiplier_of_zero fin3_12_covBy _ hCoeff

private theorem leftWeylMultiplier_G10TranslatedStageFour_zero_D0
    (F : Type u) [Field F] :
    leftWeylMultiplier (F := F) (n := 3) fin3_12_covBy
        (G10TranslatedStageFour_D0 (F := F) (0 : F)) =
      (hTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne
          (-1 : Fˣ))⁻¹ := by
  have hT12Zero :
      Matrix.SpecialLinearGroup.transvection
          (show (1 : Fin 3) ≠ 2 by decide) (-(0 : F)) = 1 := by
    have hZero : (-(0 : F)) = (0 : F) := by simp
    rw [hZero]
    exact Matrix.SpecialLinearGroup.transvection_coeff_zero
      (show (1 : Fin 3) ≠ 2 by decide)
  have hP4Zero :
      G10TranslatedStageFour_P4 (F := F) (0 : F) =
        Matrix.SpecialLinearGroup.transvection
            (show (1 : Fin 3) ≠ 0 by decide) (1 : F) *
          (Matrix.SpecialLinearGroup.transvection
              (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
              Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))) := by
    calc G10TranslatedStageFour_P4 (F := F) (0 : F)
        = Matrix.SpecialLinearGroup.transvection
              (show (1 : Fin 3) ≠ 0 by decide) (1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                (Matrix.SpecialLinearGroup.transvection
                    (show (1 : Fin 3) ≠ 2 by decide) (-(0 : F)) *
                  Matrix.SpecialLinearGroup.transvection
                    (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))) := rfl
      _ = _ := by rw [hT12Zero, one_mul]
  have hD0Eq :
      G10TranslatedStageFour_D0 (F := F) (0 : F) =
        (Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3)
            fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              (show (1 : Fin 3) ≠ 0 by decide) (1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))) := by
    calc G10TranslatedStageFour_D0 (F := F) (0 : F)
        = (Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3)
              fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
            G10TranslatedStageFour_P4 (F := F) (0 : F) := rfl
      _ = _ := by rw [hP4Zero]
  have hCoeff : leftSimpleRootCoeff F 3
      (G10TranslatedStageFour_D0 (F := F) (0 : F)) fin3_12_covBy = 1 := by
    have hBase :=
      leftSimpleRootCoeff_G10TranslatedStageFour_zero_D0 F fin3_12_covBy
    have hBaseEq : leftSimpleRootCoeff F 3
        ((Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3)
            fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              (show (1 : Fin 3) ≠ 0 by decide) (1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))))) fin3_12_covBy = 1 :=
      hBase
    calc leftSimpleRootCoeff F 3
          (G10TranslatedStageFour_D0 (F := F) (0 : F)) fin3_12_covBy
        = leftSimpleRootCoeff F 3
            ((Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3)
                fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 0 by decide) (1 : F) *
                (Matrix.SpecialLinearGroup.transvection
                    (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
                  (Matrix.SpecialLinearGroup.transvection
                      (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                    Matrix.SpecialLinearGroup.transvection
                      (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))))) fin3_12_covBy := by
          rw [hD0Eq]
      _ = 1 := hBaseEq
  have hNotPos : ¬ ((Matrix.GeneralLinearGroup.bruhatMiddle
      (G10TranslatedStageFour_D0 (F := F) (0 : F)) :
        MonomialBase Fˣ (Fin 3)).right.symm (1 : Fin 3) <
      (Matrix.GeneralLinearGroup.bruhatMiddle
        (G10TranslatedStageFour_D0 (F := F) (0 : F)) :
        MonomialBase Fˣ (Fin 3)).right.symm (2 : Fin 3)) := by
    have hBase :=
      bruhatMiddle_G10TranslatedStageFour_zero_D0_not_pos F fin3_12_covBy
    have hMidEq : Matrix.GeneralLinearGroup.bruhatMiddle
        (G10TranslatedStageFour_D0 (F := F) (0 : F)) =
        Matrix.GeneralLinearGroup.bruhatMiddle
        ((Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3)
            fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              (show (1 : Fin 3) ≠ 0 by decide) (1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))) ) := by
      rw [hD0Eq]
    rw [hMidEq]
    exact hBase
  have hNe : leftSimpleRootCoeff F 3
      (G10TranslatedStageFour_D0 (F := F) (0 : F)) fin3_12_covBy ≠ 0 := by
    rw [hCoeff]
    exact one_ne_zero
  have hMul :=
    leftWeylMultiplier_of_neg fin3_12_covBy
      (G10TranslatedStageFour_D0 (F := F) (0 : F)) hNe hNotPos
  have hOneNe : (1 : F) ≠ 0 := one_ne_zero
  have hUnits : torusUnitOfNegCoeff (1 : F) hOneNe = (-1 : Fˣ) := by
    apply Units.ext
    simp [torusUnitOfNegCoeff]
  have hCoeffUnits :
      torusUnitOfNegCoeff
          (leftSimpleRootCoeff F 3
            (G10TranslatedStageFour_D0 (F := F) (0 : F)) fin3_12_covBy) hNe =
        (-1 : Fˣ) := by
    have hEq :
        torusUnitOfNegCoeff
            (leftSimpleRootCoeff F 3
              (G10TranslatedStageFour_D0 (F := F) (0 : F)) fin3_12_covBy) hNe =
          torusUnitOfNegCoeff (1 : F) hOneNe := by
      apply Units.ext
      simp [torusUnitOfNegCoeff, hCoeff]
    rw [hEq, hUnits]
  rw [hCoeffUnits] at hMul
  exact hMul

private theorem leftWeylMultiplier_G10TranslatedStageFour_zero_D1
    (F : Type u) [Field F] :
    leftWeylMultiplier (F := F) (n := 3) fin3_12_covBy
        (G10TranslatedStageFour_D1 (F := F) (0 : F)) =
      weylHMTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne 1 := by
  have hT12Zero :
      Matrix.SpecialLinearGroup.transvection
          (show (1 : Fin 3) ≠ 2 by decide) (-(0 : F)) = 1 := by
    have hZero : (-(0 : F)) = (0 : F) := by simp
    rw [hZero]
    exact Matrix.SpecialLinearGroup.transvection_coeff_zero
      (show (1 : Fin 3) ≠ 2 by decide)
  have hP4Zero :
      G10TranslatedStageFour_P4 (F := F) (0 : F) =
        Matrix.SpecialLinearGroup.transvection
            (show (1 : Fin 3) ≠ 0 by decide) (1 : F) *
          (Matrix.SpecialLinearGroup.transvection
              (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
              Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))) := by
    calc G10TranslatedStageFour_P4 (F := F) (0 : F)
        = Matrix.SpecialLinearGroup.transvection
              (show (1 : Fin 3) ≠ 0 by decide) (1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                (Matrix.SpecialLinearGroup.transvection
                    (show (1 : Fin 3) ≠ 2 by decide) (-(0 : F)) *
                  Matrix.SpecialLinearGroup.transvection
                    (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))) := rfl
      _ = _ := by rw [hT12Zero, one_mul]
  have hD0Eq :
      G10TranslatedStageFour_D0 (F := F) (0 : F) =
        (Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3)
            fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
          (Matrix.SpecialLinearGroup.transvection
              (show (1 : Fin 3) ≠ 0 by decide) (1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))) := by
    calc G10TranslatedStageFour_D0 (F := F) (0 : F)
        = (Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3)
              fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
            G10TranslatedStageFour_P4 (F := F) (0 : F) := rfl
      _ = _ := by rw [hP4Zero]
  have hD1Eq :
      G10TranslatedStageFour_D1 (F := F) (0 : F) =
        Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne (-1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3)
              fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
            (Matrix.SpecialLinearGroup.transvection
                (show (1 : Fin 3) ≠ 0 by decide) (1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
                (Matrix.SpecialLinearGroup.transvection
                    (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                  Matrix.SpecialLinearGroup.transvection
                    (show (2 : Fin 3) ≠ 0 by decide) (-1 : F))))) := by
    calc G10TranslatedStageFour_D1 (F := F) (0 : F)
        = Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne (-1 : F) *
            G10TranslatedStageFour_D0 (F := F) (0 : F) := rfl
      _ = _ := by rw [hD0Eq]
  have hCoeff : leftSimpleRootCoeff F 3
      (G10TranslatedStageFour_D1 (F := F) (0 : F)) fin3_12_covBy = 0 := by
    have hBase :=
      leftSimpleRootCoeff_G10TranslatedStageFour_zero_D1 F fin3_12_covBy
    calc leftSimpleRootCoeff F 3
            (G10TranslatedStageFour_D1 (F := F) (0 : F)) fin3_12_covBy
        = leftSimpleRootCoeff F 3
            (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne (-1 : F) *
              ((Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3)
                  fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
                (Matrix.SpecialLinearGroup.transvection
                    (show (1 : Fin 3) ≠ 0 by decide) (1 : F) *
                  (Matrix.SpecialLinearGroup.transvection
                      (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) *
                    (Matrix.SpecialLinearGroup.transvection
                        (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) *
                      Matrix.SpecialLinearGroup.transvection
                        (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))))) fin3_12_covBy := by
          rw [hD1Eq]
      _ = 0 := hBase
  exact leftWeylMultiplier_of_zero fin3_12_covBy _ hCoeff

end G10TranslatedStageFourHelpers

section G10TranslatedStageFour

theorem G10TranslatedStageFour_fst
    (F : Type u) [Field F] (a : F) :
    X.fst
        ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (1 : F)).val.2
          ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (1 : F)).val.2
            ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F)).val.2
              ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F)).val.2
                ((leftUpperRootLift F 3 1 2 (by decide) (-a)).val.2
                  (((leftLowerRootLift20 F (1 : F))⁻¹).val.2
                    (X_one F 3))))))) =
      Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne.symm a *
        Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne
          (-a) := by
  let y3 : X F 3 :=
    (leftLowerAdjacentRootLift F 3 fin3_01_covBy (1 : F)).val.2
      ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F)).val.2
        ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F)).val.2
          ((leftUpperRootLift F 3 1 2 (by decide) (-a)).val.2
            (((leftLowerRootLift20 F (1 : F))⁻¹).val.2 (X_one F 3)))))
  have hFstY3 : X.fst y3 =
      Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne.symm
          (1 : F) *
        (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne.symm
            (-1 : F) *
          (Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne.symm
              (-1 : F) *
            (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne
                (-a) *
              Matrix.SpecialLinearGroup.transvection
                (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))) :=
    G10TranslatedStageThree_fst F a
  have hFstLift :=
    leftLowerAdjacentRootLift_fst_apply F 3 fin3_12_covBy (1 : F) y3
  calc X.fst
        ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (1 : F)).val.2
          ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (1 : F)).val.2
            ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F)).val.2
              ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F)).val.2
                ((leftUpperRootLift F 3 1 2 (by decide) (-a)).val.2
                  (((leftLowerRootLift20 F (1 : F))⁻¹).val.2
                    (X_one F 3)))))))
      = X.fst ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (1 : F)).val.2 y3) := rfl
    _ = Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne.symm
            (1 : F) *
          X.fst y3 := hFstLift
    _ = _ := by
          rw [hFstY3]
          exact G10TranslatedStageFour_fst_matrix_aux F a

theorem G10TranslatedStageFour_snd
    (F : Type u) [Field F] (a : F) :
    X.snd
        ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (1 : F)).val.2
          ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (1 : F)).val.2
            ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F)).val.2
              ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F)).val.2
                ((leftUpperRootLift F 3 1 2 (by decide) (-a)).val.2
                  (((leftLowerRootLift20 F (1 : F))⁻¹).val.2
                    (X_one F 3))))))) =
      (weylHMTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne
          (1 : Fˣ) *
        hTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne
          (-1 : Fˣ)) *
        X.snd
          ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (1 : F)).val.2
            ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F)).val.2
              ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F)).val.2
                ((leftUpperRootLift F 3 1 2 (by decide) (-a)).val.2
                  (((leftLowerRootLift20 F (1 : F))⁻¹).val.2
                    (X_one F 3)))))) := by
  let y3 : X F 3 :=
    (leftLowerAdjacentRootLift F 3 fin3_01_covBy (1 : F)).val.2
      ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F)).val.2
        ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F)).val.2
          ((leftUpperRootLift F 3 1 2 (by decide) (-a)).val.2
            (((leftLowerRootLift20 F (1 : F))⁻¹).val.2 (X_one F 3)))))
  have hFstY3 : X.fst y3 =
      G10TranslatedStageFour_P4 (F := F) a := by
    have h := G10TranslatedStageThree_fst (F := F) a
    have h10 :
        Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne.symm
            (1 : F) =
          Matrix.SpecialLinearGroup.transvection
            (show (1 : Fin 3) ≠ 0 by decide) (1 : F) := by
      apply Subtype.ext; rfl
    have h21 :
        Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne.symm
            (-1 : F) =
          Matrix.SpecialLinearGroup.transvection
            (show (2 : Fin 3) ≠ 1 by decide) (-1 : F) := by
      apply Subtype.ext; rfl
    have h10' :
        Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne.symm
            (-1 : F) =
          Matrix.SpecialLinearGroup.transvection
            (show (1 : Fin 3) ≠ 0 by decide) (-1 : F) := by
      apply Subtype.ext; rfl
    have h12 :
        Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne
            (-a) =
          Matrix.SpecialLinearGroup.transvection
            (show (1 : Fin 3) ≠ 2 by decide) (-a) := by
      apply Subtype.ext; rfl
    calc X.fst y3
        = Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne.symm
              (1 : F) *
            (Matrix.SpecialLinearGroup.transvection
                fin3_12_covBy.ne.symm (-1 : F) *
              (Matrix.SpecialLinearGroup.transvection
                  fin3_01_covBy.ne.symm (-1 : F) *
                (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne
                    (-a) *
                  Matrix.SpecialLinearGroup.transvection
                    (show (2 : Fin 3) ≠ 0 by decide) (-1 : F)))) := h
      _ = _ := by
          rw [h10, h21, h10', h12]
          rfl
  have hSndApply :=
    leftLowerAdjacentRootLift_snd_apply F 3 fin3_12_covBy (1 : F) y3
  have hTransNeg : (-(1 : F)) = (-1 : F) := by simp
  have hD0 :
      (Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3)
          fin3_12_covBy.ne (1 : Fˣ))⁻¹ * X.fst y3 =
        G10TranslatedStageFour_D0 (F := F) a := by
    rw [hFstY3]
    rfl
  have hTransWeylFst :
      Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne
            (-(1 : F)) *
          (Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3)
              fin3_12_covBy.ne (1 : Fˣ))⁻¹ * X.fst y3 =
        Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne
            (-1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3)
              fin3_12_covBy.ne (1 : Fˣ))⁻¹ * X.fst y3) := by
    calc Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne
              (-(1 : F)) *
            (Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3)
                fin3_12_covBy.ne (1 : Fˣ))⁻¹ * X.fst y3
        = Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne
              (-1 : F) *
            (Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3)
                fin3_12_covBy.ne (1 : Fˣ))⁻¹ * X.fst y3 := by
          rw [hTransNeg]
      _ = Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne
              (-1 : F) *
            ((Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3)
                fin3_12_covBy.ne (1 : Fˣ))⁻¹ * X.fst y3) := by
          rw [mul_assoc]
  have hD1raw :
      Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne (-1 : F) *
          ((Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3)
              fin3_12_covBy.ne (1 : Fˣ))⁻¹ * X.fst y3) =
        G10TranslatedStageFour_D1 (F := F) a := by
    rw [hD0]
    rfl
  have hD1Trans :
      Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne
            (-(1 : F)) *
          (Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3)
              fin3_12_covBy.ne (1 : Fˣ))⁻¹ * X.fst y3 =
        G10TranslatedStageFour_D1 (F := F) a := by
    rw [hTransWeylFst, hD1raw]
  have hSndEq :
      X.snd ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (1 : F)).val.2 y3) =
        leftWeylMultiplier (F := F) fin3_12_covBy
            (G10TranslatedStageFour_D1 (F := F) a) *
          (leftWeylMultiplier (F := F) fin3_12_covBy
              (G10TranslatedStageFour_D0 (F := F) a))⁻¹ *
          X.snd y3 := by
    calc X.snd ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (1 : F)).val.2 y3)
        = leftWeylMultiplier fin3_12_covBy
              (Matrix.SpecialLinearGroup.transvection fin3_12_covBy.ne
                  (-(1 : F)) *
                (Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3) (2 : Fin 3)
                    fin3_12_covBy.ne (1 : Fˣ))⁻¹ * X.fst y3) *
            (leftWeylMultiplier fin3_12_covBy
                ((Matrix.GeneralLinearGroup.weylSLUnit (1 : Fin 3)
                    (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ * X.fst y3))⁻¹ *
            X.snd y3 := hSndApply
      _ = leftWeylMultiplier fin3_12_covBy
              (G10TranslatedStageFour_D1 (F := F) a) *
            (leftWeylMultiplier fin3_12_covBy
                (G10TranslatedStageFour_D0 (F := F) a))⁻¹ *
            X.snd y3 := by
          rw [hD1Trans, hD0]
  by_cases ha0 : a = 0
  · have hD0Zero :
        G10TranslatedStageFour_D0 (F := F) a =
          G10TranslatedStageFour_D0 (F := F) (0 : F) := by
      rw [ha0]
    have hD1Zero :
        G10TranslatedStageFour_D1 (F := F) a =
          G10TranslatedStageFour_D1 (F := F) (0 : F) := by
      rw [ha0]
    calc X.snd
          ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (1 : F)).val.2
            ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (1 : F)).val.2
              ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F)).val.2
                ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F)).val.2
                  ((leftUpperRootLift F 3 1 2 (by decide) (-a)).val.2
                    (((leftLowerRootLift20 F (1 : F))⁻¹).val.2
                      (X_one F 3)))))))
        = X.snd ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (1 : F)).val.2 y3) := rfl
      _ = leftWeylMultiplier (F := F) fin3_12_covBy
              (G10TranslatedStageFour_D1 (F := F) a) *
            (leftWeylMultiplier (F := F) fin3_12_covBy
                (G10TranslatedStageFour_D0 (F := F) a))⁻¹ *
            X.snd y3 := hSndEq
      _ = leftWeylMultiplier (F := F) fin3_12_covBy
              (G10TranslatedStageFour_D1 (F := F) (0 : F)) *
            (leftWeylMultiplier (F := F) fin3_12_covBy
                (G10TranslatedStageFour_D0 (F := F) (0 : F)))⁻¹ *
            X.snd y3 := by
          rw [hD0Zero, hD1Zero]
      _ = weylHMTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne 1 *
            ((hTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne
                (-1 : Fˣ))⁻¹)⁻¹ *
            X.snd y3 := by
          rw [leftWeylMultiplier_G10TranslatedStageFour_zero_D1 (F := F),
            leftWeylMultiplier_G10TranslatedStageFour_zero_D0 (F := F)]
      _ = (weylHMTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne
              (1 : Fˣ) *
            hTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne
              (-1 : Fˣ)) *
            X.snd y3 := by
          rw [inv_inv, mul_assoc]
  · have ha0Ne : a ≠ 0 := ha0
    calc X.snd
          ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (1 : F)).val.2
            ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (1 : F)).val.2
              ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F)).val.2
                ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F)).val.2
                  ((leftUpperRootLift F 3 1 2 (by decide) (-a)).val.2
                    (((leftLowerRootLift20 F (1 : F))⁻¹).val.2
                      (X_one F 3)))))))
        = X.snd ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (1 : F)).val.2 y3) := rfl
      _ = leftWeylMultiplier (F := F) fin3_12_covBy
              (G10TranslatedStageFour_D1 (F := F) a) *
            (leftWeylMultiplier (F := F) fin3_12_covBy
                (G10TranslatedStageFour_D0 (F := F) a))⁻¹ *
            X.snd y3 := hSndEq
      _ = weylHMTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne 1 *
            ((hTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne
                (-1 : Fˣ))⁻¹)⁻¹ *
            X.snd y3 := by
          rw [leftWeylMultiplier_G10TranslatedStageFour_gen_D1 F a ha0Ne,
            leftWeylMultiplier_G10TranslatedStageFour_gen_D0 F a ha0Ne]
      _ = (weylHMTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne
              (1 : Fˣ) *
            hTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne
              (-1 : Fˣ)) *
            X.snd y3 := by
          rw [inv_inv, mul_assoc]

end G10TranslatedStageFour

theorem G10_commutator_proj (F : Type u) [Field F] (a : F) :
    leftExtensionProjHom F 3
        ⁅leftUpperRootLift F 3 1 2 (by decide) a,
          leftLowerRootLift20 F (1 : F)⁆ =
      Matrix.SpecialLinearGroup.transvection
        (show (1 : Fin 3) ≠ 0 by decide) a := by
  rw [map_commutatorElement]
  simp only [leftExtensionProjHom_leftUpperRootLift,
    leftExtensionProjHom_leftLowerRootLift20]
  apply Matrix.SpecialLinearGroup.toGL_injective
  calc Matrix.SpecialLinearGroup.toGL
          ⁅Matrix.SpecialLinearGroup.transvection
              (show (1 : Fin 3) ≠ 2 by decide) a,
            Matrix.SpecialLinearGroup.transvection
              (show (2 : Fin 3) ≠ 0 by decide) (1 : F)⁆
      = ⁅Matrix.SpecialLinearGroup.toGL
            (Matrix.SpecialLinearGroup.transvection
              (show (1 : Fin 3) ≠ 2 by decide) a),
          Matrix.SpecialLinearGroup.toGL
            (Matrix.SpecialLinearGroup.transvection
              (show (2 : Fin 3) ≠ 0 by decide) (1 : F))⁆ := by
        rw [map_commutatorElement]
    _ = ⁅Matrix.GeneralLinearGroup.elementary
            (1 : Fin 3) (2 : Fin 3) (by decide) a,
          Matrix.GeneralLinearGroup.elementary
            (2 : Fin 3) (0 : Fin 3) (by decide) (1 : F)⁆ := by
        have h12 :
            Matrix.SpecialLinearGroup.toGL
                (Matrix.SpecialLinearGroup.transvection
                  (show (1 : Fin 3) ≠ 2 by decide) a) =
              Matrix.GeneralLinearGroup.elementary
                (1 : Fin 3) (2 : Fin 3) (by decide) a := by
          apply Units.ext
          simp [Matrix.SpecialLinearGroup.transvection_coe,
            Matrix.GeneralLinearGroup.coe_elementary]
        have h20 :
            Matrix.SpecialLinearGroup.toGL
                (Matrix.SpecialLinearGroup.transvection
                  (show (2 : Fin 3) ≠ 0 by decide) (1 : F)) =
              Matrix.GeneralLinearGroup.elementary
                (2 : Fin 3) (0 : Fin 3) (by decide) (1 : F) := by
          apply Units.ext
          simp [Matrix.SpecialLinearGroup.transvection_coe,
            Matrix.GeneralLinearGroup.coe_elementary]
        rw [h12, h20]
    _ = Matrix.GeneralLinearGroup.elementary
            (1 : Fin 3) (0 : Fin 3) (by decide) a := by
        have hElem :=
          Matrix.GeneralLinearGroup.commutatorElement_elementary
            (1 : Fin 3) (0 : Fin 3) (2 : Fin 3)
            (by decide) (by decide) (by decide) a (1 : F)
        simpa [mul_one] using hElem
    _ = Matrix.SpecialLinearGroup.toGL
            (Matrix.SpecialLinearGroup.transvection
              (show (1 : Fin 3) ≠ 0 by decide) a) := by
        apply Units.ext
        simp [Matrix.SpecialLinearGroup.transvection_coe,
          Matrix.GeneralLinearGroup.coe_elementary]

private theorem leftLowerRootLift20_one_eq (F : Type u) [Field F] :
    leftLowerRootLift20 F (1 : F) =
      leftLowerAdjacentRootLift F 3 fin3_12_covBy (1 : F) *
        leftLowerAdjacentRootLift F 3 fin3_01_covBy (1 : F) *
        leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F) *
        leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F) := by
  unfold leftLowerRootLift20 leftLowerTwoStepRootLift
  simp only [commutatorElement_def]
  have hNeg12 :
      leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F) =
        (leftLowerAdjacentRootLift F 3 fin3_12_covBy (1 : F))⁻¹ := by
    have h := leftLowerAdjacentRootLift_neg (F := F) (n := 3)
      fin3_12_covBy (1 : F)
    have h1 : (-(1 : F)) = (-1 : F) := by simp
    rw [h1] at h
    exact h
  have hNeg01 :
      leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F) =
        (leftLowerAdjacentRootLift F 3 fin3_01_covBy (1 : F))⁻¹ := by
    have h := leftLowerAdjacentRootLift_neg (F := F) (n := 3)
      fin3_01_covBy (1 : F)
    have h1 : (-(1 : F)) = (-1 : F) := by simp
    rw [h1] at h
    exact h
  calc leftLowerAdjacentRootLift F 3 fin3_12_covBy (1 : F) *
          leftLowerAdjacentRootLift F 3 fin3_01_covBy (1 : F) *
            (leftLowerAdjacentRootLift F 3 fin3_12_covBy (1 : F))⁻¹ *
              (leftLowerAdjacentRootLift F 3 fin3_01_covBy (1 : F))⁻¹
      = leftLowerAdjacentRootLift F 3 fin3_12_covBy (1 : F) *
          leftLowerAdjacentRootLift F 3 fin3_01_covBy (1 : F) *
          leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F) *
          leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F) := by
        rw [← hNeg12, ← hNeg01]

private theorem G10_commutator_eq_stageFour_product
    (F : Type u) [Field F] (a : F) :
    ⁅leftUpperRootLift F 3 1 2 (by decide) a,
      leftLowerRootLift20 F (1 : F)⁆ =
      leftUpperRootLift F 3 1 2 (by decide) a *
        leftLowerAdjacentRootLift F 3 fin3_12_covBy (1 : F) *
        leftLowerAdjacentRootLift F 3 fin3_01_covBy (1 : F) *
        leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F) *
        leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F) *
        leftUpperRootLift F 3 1 2 (by decide) (-a) *
        (leftLowerRootLift20 F (1 : F))⁻¹ := by
  rw [commutatorElement_def, leftLowerRootLift20_one_eq]
  have h : (leftUpperRootLift F 3 1 2 (by decide) a)⁻¹ =
      leftUpperRootLift F 3 1 2 (by decide) (-a) := by
    have h := leftUpperRootLift_neg (F := F) (n := 3) 1 2 (by decide) a
    exact h.symm
  rw [h]
  simp only [mul_assoc]

private theorem G10_commutator_val2_eq_stageFour_product
    (F : Type u) [Field F] (a : F) :
    (⁅leftUpperRootLift F 3 1 2 (by decide) a,
      leftLowerRootLift20 F (1 : F)⁆).val.2 =
      (leftUpperRootLift F 3 1 2 (by decide) a).val.2 *
        (leftLowerAdjacentRootLift F 3 fin3_12_covBy (1 : F)).val.2 *
        (leftLowerAdjacentRootLift F 3 fin3_01_covBy (1 : F)).val.2 *
        (leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F)).val.2 *
        (leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F)).val.2 *
        (leftUpperRootLift F 3 1 2 (by decide) (-a)).val.2 *
        ((leftLowerRootLift20 F (1 : F))⁻¹).val.2 := by
  exact congrArg (fun p : leftExtensionSubgroup F 3 => p.val.2)
    (G10_commutator_eq_stageFour_product (F := F) a)

private theorem G10_commutator_val2_apply_X_one
    (F : Type u) [Field F] (a : F) :
    (⁅leftUpperRootLift F 3 1 2 (by decide) a,
      leftLowerRootLift20 F (1 : F)⁆).val.2 (X_one F 3) =
      (leftUpperRootLift F 3 1 2 (by decide) a).val.2
        ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (1 : F)).val.2
          ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (1 : F)).val.2
            ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F)).val.2
              ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F)).val.2
                ((leftUpperRootLift F 3 1 2 (by decide) (-a)).val.2
                  (((leftLowerRootLift20 F (1 : F))⁻¹).val.2
                    (X_one F 3))))))) := by
  rw [G10_commutator_val2_eq_stageFour_product]
  simp only [Equiv.Perm.mul_apply]

private theorem leftUpperRootLift_snd_apply
    (F : Type u) [Field F] (n : ℕ) (i j : Fin n) (hij : i < j)
    (r : F) (x : X F n) :
    X.snd ((leftUpperRootLift F n i j hij r).val.2 x) = X.snd x := by
  have hVal :
      (leftUpperRootLift F n i j hij r).val.2 =
        leftUpperPerm (UpperElementary.elementary i j hij r) := by
    simp [leftUpperRootLift_val]
  rw [hVal, leftUpperPerm_apply, leftUpper_snd]

private theorem G10_commutator_snd_eq_translatedStageFour
    (F : Type u) [Field F] (a : F) :
    X.snd
        ((⁅leftUpperRootLift F 3 1 2 (by decide) a,
          leftLowerRootLift20 F (1 : F)⁆).val.2 (X_one F 3)) =
      X.snd
        ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (1 : F)).val.2
          ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (1 : F)).val.2
            ((leftLowerAdjacentRootLift F 3 fin3_12_covBy (-1 : F)).val.2
              ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (-1 : F)).val.2
                ((leftUpperRootLift F 3 1 2 (by decide) (-a)).val.2
                  (((leftLowerRootLift20 F (1 : F))⁻¹).val.2
                    (X_one F 3))))))) := by
  rw [G10_commutator_val2_apply_X_one, leftUpperRootLift_snd_apply]

private theorem fin3_weyl01_mul_hTits_neg_one_eq_inv (F : Type u) [Field F] :
    weylHMTits F 3 (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fˣ) *
      hTits F 3 (0 : Fin 3) (1 : Fin 3) (by decide) (-1 : Fˣ) =
      (weylHMTits F 3 (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fˣ))⁻¹ := by
  have hMul := weylHMTits_mul_simple (F := F) (n := 3) (i := (0 : Fin 3))
    (j := (1 : Fin 3)) (hij := by decide) (u := (-1 : Fˣ)) (by decide)
  have hInv := weylHMTits_neg_one_eq_inv_of_covBy (F := F) fin3_01_covBy
  calc _ = _ * (_ * _) := by rw [← hMul]
    _ = _ * (_⁻¹ * _⁻¹) := by rw [hInv]
    _ = _⁻¹ := by rw [← mul_assoc, mul_inv_cancel, one_mul]
private theorem fin3_weyl12_mul_hTits_neg_one_eq_inv (F : Type u) [Field F] :
    weylHMTits F 3 (1 : Fin 3) (2 : Fin 3) (by decide) (1 : Fˣ) *
      hTits F 3 (1 : Fin 3) (2 : Fin 3) (by decide) (-1 : Fˣ) =
      (weylHMTits F 3 (1 : Fin 3) (2 : Fin 3) (by decide) (1 : Fˣ))⁻¹ := by
  have hMul := weylHMTits_mul_simple (F := F) (n := 3) (i := (1 : Fin 3))
    (j := (2 : Fin 3)) (hij := by decide) (u := (-1 : Fˣ)) (by decide)
  have hInv := weylHMTits_neg_one_eq_inv_of_covBy (F := F) fin3_12_covBy
  calc _ = _ * (_ * _) := by rw [← hMul]
    _ = _ * (_⁻¹ * _⁻¹) := by rw [hInv]
    _ = _⁻¹ := by rw [← mul_assoc, mul_inv_cancel, one_mul]
private theorem fin3_weyl_braid_tail (F : Type u) [Field F] :
    (weylHMTits F 3 (1 : Fin 3) (2 : Fin 3) (by decide) (1 : Fˣ))⁻¹ *
      weylHMTits F 3 (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fˣ) *
      weylHMTits F 3 (1 : Fin 3) (2 : Fin 3) (by decide) (1 : Fˣ) =
      weylHMTits F 3 (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fˣ) *
        weylHMTits F 3 (1 : Fin 3) (2 : Fin 3) (by decide) (1 : Fˣ) *
        (weylHMTits F 3 (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fˣ))⁻¹ := by
  let A := weylHMTits F 3 (1 : Fin 3) (2 : Fin 3) (by decide) (1 : Fˣ)
  let B := weylHMTits F 3 (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fˣ)
  have hC := fin3_weylHMTits_cycle F (1 : Fˣ)
  calc A⁻¹ * B * A = A⁻¹ * (B * A * B) * B⁻¹ := by group
    _ = A⁻¹ * (A * B * A) * B⁻¹ := by rw [← hC]
    _ = B * A * B⁻¹ := by group
private theorem fin3_weylHMTits_inv_braid_one (F : Type u) [Field F] :
    (weylHMTits F 3 (1 : Fin 3) (2 : Fin 3) (by decide) (1 : Fˣ))⁻¹ *
      (weylHMTits F 3 (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fˣ))⁻¹ *
      (weylHMTits F 3 (1 : Fin 3) (2 : Fin 3) (by decide) (1 : Fˣ))⁻¹ =
      (weylHMTits F 3 (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fˣ))⁻¹ *
        (weylHMTits F 3 (1 : Fin 3) (2 : Fin 3) (by decide) (1 : Fˣ))⁻¹ *
        (weylHMTits F 3 (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fˣ))⁻¹ := by
  have hC := fin3_weylHMTits_cycle F (1 : Fˣ)
  calc (weylHMTits F 3 (1 : Fin 3) (2 : Fin 3) (by decide) (1 : Fˣ))⁻¹ *
        (weylHMTits F 3 (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fˣ))⁻¹ *
        (weylHMTits F 3 (1 : Fin 3) (2 : Fin 3) (by decide) (1 : Fˣ))⁻¹
      = (weylHMTits F 3 (1 : Fin 3) (2 : Fin 3) (by decide) (1 : Fˣ) *
          weylHMTits F 3 (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fˣ) *
          weylHMTits F 3 (1 : Fin 3) (2 : Fin 3) (by decide) (1 : Fˣ))⁻¹ := by
          simp only [_root_.mul_inv_rev, mul_assoc]
      _ = (weylHMTits F 3 (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fˣ) *
          weylHMTits F 3 (1 : Fin 3) (2 : Fin 3) (by decide) (1 : Fˣ) *
          weylHMTits F 3 (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fˣ))⁻¹ := by
          rw [hC]
      _ = (weylHMTits F 3 (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fˣ))⁻¹ *
          (weylHMTits F 3 (1 : Fin 3) (2 : Fin 3) (by decide) (1 : Fˣ))⁻¹ *
          (weylHMTits F 3 (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fˣ))⁻¹ := by
          simp only [_root_.mul_inv_rev, mul_assoc]
private theorem fin3_weylHMTits_one_branch_word (F : Type u) [Field F] :
    (weylHMTits F 3 (1 : Fin 3) (2 : Fin 3) (by decide) (1 : Fˣ))⁻¹ *
      (weylHMTits F 3 (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fˣ))⁻¹ *
      (weylHMTits F 3 (1 : Fin 3) (2 : Fin 3) (by decide) (1 : Fˣ))⁻¹ *
      weylHMTits F 3 (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fˣ) *
      weylHMTits F 3 (1 : Fin 3) (2 : Fin 3) (by decide) (1 : Fˣ) =
      (weylHMTits F 3 (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fˣ))⁻¹ := by
  have hB := fin3_weylHMTits_inv_braid_one F
  calc _ = (weylHMTits F 3 (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fˣ))⁻¹ *
          (weylHMTits F 3 (1 : Fin 3) (2 : Fin 3) (by decide) (1 : Fˣ))⁻¹ *
          (weylHMTits F 3 (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fˣ))⁻¹ *
          weylHMTits F 3 (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fˣ) *
          weylHMTits F 3 (1 : Fin 3) (2 : Fin 3) (by decide) (1 : Fˣ) := by
          rw [hB]
      _ = (weylHMTits F 3 (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fˣ))⁻¹ := by
          group
private theorem fin3_hTits_cycle_conj_inv (F : Type u) [Field F] (a : Fˣ) :
    (weylHMTits F 3 (1 : Fin 3) 2 (by decide) (1 : Fˣ))⁻¹ *
      (weylHMTits F 3 (0 : Fin 3) 1 (by decide) (1 : Fˣ))⁻¹ *
      (hTits F 3 (1 : Fin 3) 2 (by decide) a)⁻¹ *
      (weylHMTits F 3 (0 : Fin 3) 1 (by decide) (1 : Fˣ) *
        weylHMTits F 3 (1 : Fin 3) 2 (by decide) (1 : Fˣ)) =
      (hTits F 3 (0 : Fin 3) 1 (by decide) a)⁻¹ := by
  have h := fin3_hTits_cycle_conj F a
  calc (weylHMTits F 3 (1 : Fin 3) 2 (by decide) (1 : Fˣ))⁻¹ *
          (weylHMTits F 3 (0 : Fin 3) 1 (by decide) (1 : Fˣ))⁻¹ *
          (hTits F 3 (1 : Fin 3) 2 (by decide) a)⁻¹ *
          (weylHMTits F 3 (0 : Fin 3) 1 (by decide) (1 : Fˣ) *
            weylHMTits F 3 (1 : Fin 3) 2 (by decide) (1 : Fˣ))
      = (((weylHMTits F 3 (1 : Fin 3) 2 (by decide) (1 : Fˣ))⁻¹ *
            (weylHMTits F 3 (0 : Fin 3) 1 (by decide) (1 : Fˣ))⁻¹) *
          hTits F 3 (1 : Fin 3) 2 (by decide) a *
          (weylHMTits F 3 (0 : Fin 3) 1 (by decide) (1 : Fˣ) *
            weylHMTits F 3 (1 : Fin 3) 2 (by decide) (1 : Fˣ)))⁻¹ := by
        simp only [_root_.mul_inv_rev, inv_inv, mul_assoc]
    _ = (hTits F 3 (0 : Fin 3) 1 (by decide) a)⁻¹ := by
        rw [h]
private theorem G10_crossRatio_z_eq_inv_one_sub
    (F : Type u) [Field F] (a : F)
    (hOneSub : (1 - a) ≠ 0) (hSum : a / (1 - a) + 1 ≠ 0) :
    Units.mk0 (a / (1 - a) + 1) hSum =
      (Units.mk0 (1 - a) hOneSub)⁻¹ := by
  apply Units.ext
  simp only [Units.val_mk0, Units.val_inv_eq_inv_val]
  calc a / (1 - a) + 1
      = (a + (1 - a)) / (1 - a) := by
        rw [add_div, div_self hOneSub]
    _ = 1 / (1 - a) := by
        rw [add_sub_cancel]
    _ = (1 - a)⁻¹ := by
        rw [one_div]
private theorem G10_crossRatio_p_one_z_inv_eq_a
    (F : Type u) [Field F] (a : F) (ha0 : a ≠ 0)
    (hOneSub : (1 - a) ≠ 0) (hRatio : a / (1 - a) ≠ 0)
    (hSum : a / (1 - a) + 1 ≠ 0) :
    Units.mk0 (a / (1 - a)) hRatio * (1 : Fˣ) *
        (Units.mk0 (a / (1 - a) + 1) hSum)⁻¹ =
      Units.mk0 a ha0 := by
  have hZ := G10_crossRatio_z_eq_inv_one_sub F a hOneSub hSum
  calc Units.mk0 (a / (1 - a)) hRatio * (1 : Fˣ) *
        (Units.mk0 (a / (1 - a) + 1) hSum)⁻¹
      = Units.mk0 (a / (1 - a)) hRatio * (1 : Fˣ) * Units.mk0 (1 - a) hOneSub := by
        rw [hZ, inv_inv]
    _ = Units.mk0 a ha0 := by
        apply Units.ext
        simp only [Units.val_mul, Units.val_mk0, mul_one]
        exact div_mul_cancel₀ a hOneSub
private theorem G10_crossRatio_sum_ne_zero
    (F : Type u) [Field F] (a : F) (hOneSub : (1 - a) ≠ 0) :
    a / (1 - a) + 1 ≠ 0 := by
  have hEq : a / (1 - a) + 1 = (1 - a)⁻¹ := by
    calc a / (1 - a) + 1
        = (a + (1 - a)) / (1 - a) := by
          rw [add_div, div_self hOneSub]
      _ = 1 / (1 - a) := by
          rw [add_sub_cancel]
      _ = (1 - a)⁻¹ := by
          rw [one_div]
  rw [hEq]
  exact inv_ne_zero hOneSub
private theorem G10_hTits_crossRatio_raw
    (F : Type u) [Field F] (a : F) (ha0 : a ≠ 0)
    (hOneSub : (1 - a) ≠ 0) (hRatio : a / (1 - a) ≠ 0)
    (hSum : a / (1 - a) + 1 ≠ 0) :
    (hTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne
        (Units.mk0 a ha0))⁻¹ =
      (hTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne
        (Units.mk0 (a / (1 - a)) hRatio))⁻¹ *
      hTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne
        (Units.mk0 (a / (1 - a) + 1) hSum) := by
  have hP := G10_crossRatio_p_one_z_inv_eq_a F a ha0 hOneSub hRatio hSum
  have h1 := hTits_one_of_covBy (F := F) fin3_12_covBy
  have hCR := hTits_cross_ratio_of_lt fin3_12_covBy.ne fin3_12_covBy.lt
    (Units.mk0 (a / (1 - a)) hRatio) (1 : Fˣ) hSum
  calc (hTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne
          (Units.mk0 a ha0))⁻¹
      = (hTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne
          (Units.mk0 (a / (1 - a)) hRatio * 1 *
            (Units.mk0 (a / (1 - a) + 1) hSum)⁻¹))⁻¹ := by rw [hP]
    _ = (hTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne
          (Units.mk0 (a / (1 - a)) hRatio * 1 *
            (Units.mk0 (a / (1 - a) + 1) hSum)⁻¹))⁻¹ *
        hTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ) := by
        simp [h1]
    _ = _ := by simpa using hCR
private theorem G10TranslatedStageTwo_hTits_cross_ratio_normalize
    (F : Type u) [Field F] (a : F) (ha0 : a ≠ 0) (_ha1 : a ≠ 1)
    (hOneSub : (1 - a) ≠ 0) (hRatio : a / (1 - a) ≠ 0) :
    (hTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne
        (Units.mk0 (a / (1 - a)) hRatio))⁻¹ *
      hTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne
        ((Units.mk0 (1 - a) hOneSub)⁻¹) =
      (hTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne
        (Units.mk0 a ha0))⁻¹ := by
  have hSum := G10_crossRatio_sum_ne_zero F a hOneSub
  have hZ := G10_crossRatio_z_eq_inv_one_sub F a hOneSub hSum
  have hRaw := G10_hTits_crossRatio_raw F a ha0 hOneSub hRatio hSum
  rw [hZ] at hRaw
  exact hRaw.symm
private theorem G10TranslatedStageFour_snd_generic_braid_cycle
    (F : Type u) [Field F] (a : F) (ha0 : a ≠ 0) :
    (weylHMTits F 3 (1 : Fin 3) (2 : Fin 3) (by decide) (1 : Fˣ))⁻¹ *
      (weylHMTits F 3 (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fˣ))⁻¹ *
      (hTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne
        (Units.mk0 a ha0))⁻¹ *
      (weylHMTits F 3 (1 : Fin 3) (2 : Fin 3) (by decide) (1 : Fˣ))⁻¹ *
      weylHMTits F 3 (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fˣ) *
      weylHMTits F 3 (1 : Fin 3) (2 : Fin 3) (by decide) (1 : Fˣ) =
      (hTits F 3 (0 : Fin 3) (1 : Fin 3) fin3_01_covBy.ne
        (Units.mk0 a ha0))⁻¹ *
      (weylHMTits F 3 (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fˣ))⁻¹ := by
  let W12 := weylHMTits F 3 (1 : Fin 3) (2 : Fin 3) (by decide) (1 : Fˣ)
  let W01 := weylHMTits F 3 (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fˣ)
  let H12 := hTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne (Units.mk0 a ha0)
  let H01 := hTits F 3 (0 : Fin 3) (1 : Fin 3) fin3_01_covBy.ne (Units.mk0 a ha0)
  have hTail := fin3_weyl_braid_tail F
  have hTailW : W12⁻¹ * W01 * W12 = W01 * W12 * W01⁻¹ := by
    simp only [W12, W01]; exact hTail
  have hCycle := fin3_hTits_cycle_conj_inv F (Units.mk0 a ha0)
  have hCycleW : W12⁻¹ * W01⁻¹ * H12⁻¹ * (W01 * W12) = H01⁻¹ := by
    simp only [W12, W01, H12, H01]; exact hCycle
  calc W12⁻¹ * W01⁻¹ * H12⁻¹ * W12⁻¹ * W01 * W12
      = W12⁻¹ * W01⁻¹ * H12⁻¹ * (W12⁻¹ * W01 * W12) := by group
    _ = W12⁻¹ * W01⁻¹ * H12⁻¹ * (W01 * W12 * W01⁻¹) := by rw [hTailW]
    _ = W12⁻¹ * W01⁻¹ * H12⁻¹ * (W01 * W12) * W01⁻¹ := by group
    _ = H01⁻¹ * W01⁻¹ := by rw [hCycleW]
private theorem fin3_hTits01_neg_one_inv_mul_weyl01_inv_eq_weyl01
    (F : Type u) [Field F] :
    (hTits F 3 (0 : Fin 3) (1 : Fin 3) (by decide) (-1 : Fˣ))⁻¹ *
      (weylHMTits F 3 (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fˣ))⁻¹ =
      weylHMTits F 3 (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fˣ) := by
  have h := fin3_weyl01_mul_hTits_neg_one_eq_inv F
  calc (hTits F 3 (0 : Fin 3) (1 : Fin 3) (by decide) (-1 : Fˣ))⁻¹ *
          (weylHMTits F 3 (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fˣ))⁻¹
      = (weylHMTits F 3 (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fˣ) *
          hTits F 3 (0 : Fin 3) (1 : Fin 3) (by decide) (-1 : Fˣ))⁻¹ := by
        rw [← _root_.mul_inv_rev]
    _ = ((weylHMTits F 3 (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fˣ))⁻¹)⁻¹ := by
        rw [h]
    _ = weylHMTits F 3 (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fˣ) := by
        rw [inv_inv]
private theorem fin3_hTits12_neg_one_inv_mul_weyl12_inv_eq_weyl12
    (F : Type u) [Field F] :
    (hTits F 3 (1 : Fin 3) (2 : Fin 3) (by decide) (-1 : Fˣ))⁻¹ *
      (weylHMTits F 3 (1 : Fin 3) (2 : Fin 3) (by decide) (1 : Fˣ))⁻¹ =
      weylHMTits F 3 (1 : Fin 3) (2 : Fin 3) (by decide) (1 : Fˣ) := by
  have h := fin3_weyl12_mul_hTits_neg_one_eq_inv F
  calc (hTits F 3 (1 : Fin 3) (2 : Fin 3) (by decide) (-1 : Fˣ))⁻¹ *
          (weylHMTits F 3 (1 : Fin 3) (2 : Fin 3) (by decide) (1 : Fˣ))⁻¹
      = (weylHMTits F 3 (1 : Fin 3) (2 : Fin 3) (by decide) (1 : Fˣ) *
          hTits F 3 (1 : Fin 3) (2 : Fin 3) (by decide) (-1 : Fˣ))⁻¹ := by
        rw [← _root_.mul_inv_rev]
    _ = ((weylHMTits F 3 (1 : Fin 3) (2 : Fin 3) (by decide) (1 : Fˣ))⁻¹)⁻¹ := by
        rw [h]
    _ = weylHMTits F 3 (1 : Fin 3) (2 : Fin 3) (by decide) (1 : Fˣ) := by
        rw [inv_inv]
private theorem G10Inverse_snd_normalize
    (F : Type u) [Field F] :
    X.snd (((leftLowerRootLift20 F (1 : F))⁻¹).val.2 (X_one F 3)) =
      (weylHMTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
        weylHMTits F 3 (0 : Fin 3) (1 : Fin 3) fin3_01_covBy.ne (1 : Fˣ) *
        weylHMTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ) := by
  have h := G10Inverse_snd (F := F)
  have h1 := hTits_one_of_covBy (F := F) fin3_12_covBy
  have h01 := fin3_hTits01_neg_one_inv_mul_weyl01_inv_eq_weyl01 (F := F)
  have h12 := fin3_hTits12_neg_one_inv_mul_weyl12_inv_eq_weyl12 (F := F)
  calc X.snd (((leftLowerRootLift20 F (1 : F))⁻¹).val.2 (X_one F 3))
      = (hTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
        (weylHMTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
          ((hTits F 3 (0 : Fin 3) (1 : Fin 3) fin3_01_covBy.ne (-1 : Fˣ))⁻¹ *
            (weylHMTits F 3 (0 : Fin 3) (1 : Fin 3) fin3_01_covBy.ne (1 : Fˣ))⁻¹ *
              ((hTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne (-1 : Fˣ))⁻¹ *
                (weylHMTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹)) := h
    _ = (weylHMTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ))⁻¹ *
        weylHMTits F 3 (0 : Fin 3) (1 : Fin 3) fin3_01_covBy.ne (1 : Fˣ) *
        weylHMTits F 3 (1 : Fin 3) (2 : Fin 3) fin3_12_covBy.ne (1 : Fˣ) := by
        simp [h1, h01, h12, mul_assoc]
private theorem G10_commutator_snd_generic
    (F : Type u) [Field F] (a : F) (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    X.snd
        ((⁅leftUpperRootLift F 3 1 2 (by decide) a,
          leftLowerRootLift20 F (1 : F)⁆).val.2 (X_one F 3)) =
      X.snd
        ((leftLowerAdjacentRootLift F 3 fin3_01_covBy a).val.2
          (X_one F 3)) := by
  have hOneSub : (1 - a) ≠ 0 := sub_ne_zero.mpr (Ne.symm ha1)
  have hRatio : a / (1 - a) ≠ 0 := div_ne_zero ha0 hOneSub
  calc X.snd
        ((⁅leftUpperRootLift F 3 1 2 (by decide) a,
          leftLowerRootLift20 F (1 : F)⁆).val.2 (X_one F 3))
      = (hTits F 3 (0 : Fin 3) (1 : Fin 3) fin3_01_covBy.ne (Units.mk0 a ha0))⁻¹ *
        (weylHMTits F 3 (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fˣ))⁻¹ := by
        rw [G10_commutator_snd_eq_translatedStageFour, G10TranslatedStageFour_snd,
          G10TranslatedStageThree_snd, G10TranslatedStageTwo_snd_generic F a ha0 ha1,
          G10TranslatedStageTwo_hTits_cross_ratio_normalize F a ha0 ha1 hOneSub hRatio,
          G10Inverse_snd_normalize, fin3_weyl12_mul_hTits_neg_one_eq_inv F,
          fin3_weyl01_mul_hTits_neg_one_eq_inv F]
        simp only [← mul_assoc]
        rw [G10TranslatedStageFour_snd_generic_braid_cycle F a ha0]
    _ = X.snd ((leftLowerAdjacentRootLift F 3 fin3_01_covBy a).val.2 (X_one F 3)) := by
        rw [leftLowerAdjacentRootLift_snd_X_one_of_ne_zero F 3 fin3_01_covBy a ha0]

private theorem G10_commutator_snd_one
    (F : Type u) [Field F] :
    X.snd
        ((⁅leftUpperRootLift F 3 1 2 (by decide) (1 : F),
          leftLowerRootLift20 F (1 : F)⁆).val.2 (X_one F 3)) =
      X.snd
        ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (1 : F)).val.2
          (X_one F 3)) := by
  calc X.snd
        ((⁅leftUpperRootLift F 3 1 2 (by decide) (1 : F),
          leftLowerRootLift20 F (1 : F)⁆).val.2 (X_one F 3))
      = (weylHMTits F 3 (1 : Fin 3) (2 : Fin 3) (by decide) (1 : Fˣ))⁻¹ *
        (weylHMTits F 3 (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fˣ))⁻¹ *
        (weylHMTits F 3 (1 : Fin 3) (2 : Fin 3) (by decide) (1 : Fˣ))⁻¹ *
        weylHMTits F 3 (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fˣ) *
        weylHMTits F 3 (1 : Fin 3) (2 : Fin 3) (by decide) (1 : Fˣ) := by
        rw [G10_commutator_snd_eq_translatedStageFour, G10TranslatedStageFour_snd,
          G10TranslatedStageThree_snd, G10TranslatedStageTwo_snd_one,
          G10Inverse_snd_normalize, fin3_weyl12_mul_hTits_neg_one_eq_inv,
          fin3_weyl01_mul_hTits_neg_one_eq_inv, ← mul_assoc, ← mul_assoc, ← mul_assoc]
    _ = (weylHMTits F 3 (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fˣ))⁻¹ := by
        rw [fin3_weylHMTits_one_branch_word]
    _ = X.snd ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (1 : F)).val.2 (X_one F 3)) := by
        rw [leftLowerAdjacentRootLift_snd_X_one_one, hTits_one_of_covBy (F := F) fin3_01_covBy,
          inv_one, one_mul]

private theorem G10_commutator_snd_zero
    (F : Type u) [Field F] :
    X.snd
        ((⁅leftUpperRootLift F 3 1 2 (by decide) (0 : F),
          leftLowerRootLift20 F (1 : F)⁆).val.2 (X_one F 3)) = 1 := by
  rw [G10_commutator_snd_eq_translatedStageFour, G10TranslatedStageFour_snd,
      G10TranslatedStageThree_snd, G10TranslatedStageTwo_snd_zero, G10Inverse_snd]
  simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel]

private theorem G10_target_snd_zero
    (F : Type u) [Field F] :
    X.snd
        ((leftLowerAdjacentRootLift F 3 fin3_01_covBy (0 : F)).val.2
          (X_one F 3)) = 1 := by
  simp [leftLowerAdjacentRootLift_zero, X_one_snd]

private theorem G10_commutator_snd
    (F : Type u) [Field F] (a : F) :
    X.snd
        ((⁅leftUpperRootLift F 3 1 2 (by decide) a,
          leftLowerRootLift20 F (1 : F)⁆).val.2 (X_one F 3)) =
      X.snd
        ((leftLowerAdjacentRootLift F 3 fin3_01_covBy a).val.2
          (X_one F 3)) := by
  by_cases ha0 : a = 0
  · have h0 : a = (0 : F) := ha0
    rw [h0]
    rw [G10_commutator_snd_zero, G10_target_snd_zero]
  · by_cases ha1 : a = 1
    · rw [ha1]
      exact G10_commutator_snd_one F
    · exact G10_commutator_snd_generic F a ha0 ha1

theorem G10_commutator_eq (F : Type u) [Field F] (a : F) :
    ⁅leftUpperRootLift F 3 1 2 (by decide) a, leftLowerRootLift20 F (1 : F)⁆ =
      leftLowerAdjacentRootLift F 3 fin3_01_covBy a :=
  leftExtension_eq_of_proj_eq_of_snd_X_one_eq (F := F) (n := 3) (by decide)
    ⁅leftUpperRootLift F 3 1 2 (by decide) a, leftLowerRootLift20 F (1 : F)⁆
    (leftLowerAdjacentRootLift F 3 fin3_01_covBy a)
    ((G10_commutator_proj (F := F) a).trans
      (leftExtensionProjHom_leftLowerAdjacentRootLift F 3 fin3_01_covBy a).symm)
    (G10_commutator_snd (F := F) a)

end MatsumotoTitsBruhatFiber

end
