/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.ConwayAxisTranspositionCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.ConwayAxisShortTransposition
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCentralizerTensorResidualLocalCoordinates

/-! The complete transposition polynomial for every actual signed short axis. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

private theorem axis_local_matrix (q : Q) (U : ConwayRawSpace) :
    (localConwayRawRepresentation (localFiberIncl q) U).1 = U.1 := by
  change conwayMatrixAction 1 U.1 = U.1
  rw [map_one]
  rfl

private theorem axis_local_tensor (r : GriessShortIndex) (c : ZMod 2)
    (U : ConwayRawSpace) (t : SpinIndex) (i : Fin 24) :
    (localConwayRawRepresentation (localFiberIncl (qCentral c * griessShortQ r)) U).2.2 t i =
      conwayShortAxisSignedSpin r c U.2.2 t i := by
  rw [localConwayRawRepresentation_apply]
  change localTensorRepresentation (localFiberIncl (qCentral c * griessShortQ r)) U.2.2 t i = _
  calc
    _ = spinRepresentation (qCentral c * griessShortQ r) (fun u => U.2.2 u i) t :=
      localFiberQ_tensor_columns _ _ _ _
    _ = spinRepresentation (qCentral c)
        (spinRepresentation (griessShortQ r) (fun u => U.2.2 u i)) t :=
      congrArg (fun F : SpinSpace ≃ₗ[ℝ] SpinSpace => F (fun u => U.2.2 u i) t)
        (spinRepresentation.map_mul _ _)
    _ = qSign c * spinRepresentation (griessShortQ r) (fun u => U.2.2 u i) t :=
      congrArg (fun x : SpinSpace => x t) (spinRepresentation_central c _)
    _ = _ := rfl

/-- The genuine local involution attached to an axis is its denominator-cleared
polynomial in actual multiplication and the actual Griess rank-one form. -/
theorem conwayShortAxisRaw_transposition_polynomial
    (r : GriessShortIndex) (c : ZMod 2) (U : ConwayRawSpace) :
    (14 : ℝ) • (localConwayRawRepresentation (localFiberIncl (qCentral c * griessShortQ r)) U) =
      (14 : ℝ) • U -
        (24 : ℝ) • (conwayRawForm (conwayShortAxisRaw r c) U • conwayShortAxisRaw r c) -
        (16 : ℝ) • conwayRawProduct (conwayShortAxisRaw r c) U +
        conwayRawProduct (conwayShortAxisRaw r c)
          (conwayRawProduct (conwayShortAxisRaw r c) U) := by
  apply Prod.ext
  · ext i j
    simp only [Prod.smul_fst, Prod.fst_add, Prod.fst_sub, Matrix.smul_apply,
      Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
    rw [axis_local_matrix, conwayShortAxisRaw_form]
    simpa only [conwayShortAxisRaw, Matrix.smul_apply, Matrix.vecMulVec_apply,
      smul_eq_mul, mul_assoc] using
      (conwayShortAxisRaw_matrix_transposition_polynomial r c U i j).symm
  · apply Prod.ext
    · funext u
      simp only [Prod.smul_snd, Prod.smul_fst, Prod.snd_add, Prod.snd_sub,
        Prod.fst_add, Prod.fst_sub, Pi.smul_apply, smul_eq_mul, Pi.add_apply, Pi.sub_apply]
      change 14 * localShortRepresentation
        (localFiberIncl (qCentral c * griessShortQ r)) U.2.1 u = _
      by_cases hur : u = r
      · subst u
        rw [conwayShortAxis_local_short_sign]
        have hc : conwayAxisShortCommutator r r = 0 := by
          change qBeta (griessShortQ r).base (griessShortQ r).base +
            qBeta (griessShortQ r).base (griessShortQ r).base = 0
          calc
            _ = (2 : ZMod 2) * qBeta (griessShortQ r).base (griessShortQ r).base := by ring
            _ = 0 := by rw [show (2 : ZMod 2) = 0 by decide, zero_mul]
        rw [hc, qSign_zero, one_mul, conwayShortAxisRaw_form]
        simpa only [conwayShortAxisRaw, Pi.smul_apply, Pi.single_eq_same,
          smul_eq_mul, mul_one, mul_assoc] using
          (conwayShortAxisRaw_short_on_axis_transposition_polynomial r c U).symm
      · have hz : (conwayShortAxisRaw r c).2.1 u = 0 := by
          simp [conwayShortAxisRaw, Pi.single_eq_of_ne hur]
        rw [hz, mul_zero, mul_zero, sub_zero]
        exact conwayShortAxisRaw_transposition_short_off_axis_local r u c U hur
    · funext t i
      simp only [Prod.smul_snd, Prod.snd_add, Prod.snd_sub, Pi.smul_apply,
        smul_eq_mul, Pi.add_apply, Pi.sub_apply]
      rw [axis_local_tensor]
      have hz : (conwayShortAxisRaw r c).2.2 t i = 0 := rfl
      rw [hz, mul_zero, mul_zero, sub_zero]
      exact (conwayShortAxisRaw_tensor_transposition_polynomial r c U t i).symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
