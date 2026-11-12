/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardPolygonJordanEquivalence
import Code.Onsager.GeneralUmlaufsatz
import Code.Onsager.KWDetLimit









namespace StatMech.FrontierA

open scoped BigOperators
open Finset
open StatMech.Onsager
open StatMech.Onsager.BaseCase


def kwRectilinearVector (d : Fin 4) : ℂ :=
  (stepOf d).1 + (stepOf d).2 * Complex.I

@[simp] theorem kwRectilinearVector_zero : kwRectilinearVector 0 = 1 := by
  norm_num [kwRectilinearVector, stepOf]

@[simp] theorem kwRectilinearVector_one : kwRectilinearVector 1 = Complex.I := by
  norm_num [kwRectilinearVector, stepOf]

@[simp] theorem kwRectilinearVector_two : kwRectilinearVector 2 = -1 := by
  norm_num [kwRectilinearVector, stepOf]

@[simp] theorem kwRectilinearVector_three : kwRectilinearVector 3 = -Complex.I := by
  norm_num [kwRectilinearVector, stepOf]

theorem kwRectilinearVector_ne_zero (d : Fin 4) :
    kwRectilinearVector d ≠ 0 := by
  fin_cases d <;> simp


noncomputable def kwRectilinearAngle (d : Fin 4) : Real.Angle :=
  match d with
  | 0 => 0
  | 1 => (Real.pi / 2 : ℝ)
  | 2 => (Real.pi : ℝ)
  | 3 => (-(Real.pi / 2) : ℝ)

theorem kwRectilinearVector_arg (d : Fin 4) :
    (Complex.arg (kwRectilinearVector d) : Real.Angle) =
      kwRectilinearAngle d := by
  fin_cases d <;>
    simp [kwRectilinearAngle, kwRectilinearVector, stepOf]

theorem kw_angle_coe_eq_of_sub_eq_full_turn {x y : ℝ}
    (h : x - y = 2 * Real.pi ∨ x - y = -(2 * Real.pi)) :
    (x : Real.Angle) = (y : Real.Angle) := by
  rw [← sub_eq_zero, ← Real.Angle.coe_sub]
  rcases h with h | h
  · rw [h, Real.Angle.coe_two_pi]
  · rw [h, Real.Angle.coe_neg, Real.Angle.coe_two_pi, neg_zero]

theorem kwRectilinearAngle_succ_sub_toReal (d : Fin 4) :
    (kwRectilinearAngle (d + 1) - kwRectilinearAngle d).toReal =
      Real.pi / 2 := by
  have hangle : kwRectilinearAngle (d + 1) - kwRectilinearAngle d =
      ((Real.pi / 2 : ℝ) : Real.Angle) := by
    fin_cases d
    · simp [kwRectilinearAngle]
    · change ((Real.pi - Real.pi / 2 : ℝ) : Real.Angle) = _
      congr 1
      ring
    · change ((-(Real.pi / 2) - Real.pi : ℝ) : Real.Angle) = _
      apply kw_angle_coe_eq_of_sub_eq_full_turn
      right
      ring
    · change ((0 - -(Real.pi / 2) : ℝ) : Real.Angle) = _
      congr 1
      ring
  rw [hangle, Real.Angle.toReal_pi_div_two]

theorem kwRectilinearAngle_pred_sub_toReal (d : Fin 4) :
    (kwRectilinearAngle (d + 3) - kwRectilinearAngle d).toReal =
      -(Real.pi / 2) := by
  have hangle : kwRectilinearAngle (d + 3) - kwRectilinearAngle d =
      ((-(Real.pi / 2) : ℝ) : Real.Angle) := by
    fin_cases d
    · simp [kwRectilinearAngle]
    · change ((0 - Real.pi / 2 : ℝ) : Real.Angle) = _
      congr 1
      ring
    · change ((Real.pi / 2 - Real.pi : ℝ) : Real.Angle) = _
      congr 1
      ring
    · change ((Real.pi - -(Real.pi / 2) : ℝ) : Real.Angle) = _
      apply kw_angle_coe_eq_of_sub_eq_full_turn
      left
      ring
  rw [hangle]
  apply Real.Angle.toReal_coe_eq_self_iff.mpr
  constructor <;> linarith [Real.pi_pos]

theorem kwAngleTurnPhase_pi_div_two :
    Complex.exp ((((Real.pi / 2 : ℝ) : ℂ) * Complex.I) / 2) =
      ons_turnRoot := by
  unfold ons_turnRoot
  congr 1
  push_cast
  ring

theorem kwAngleTurnPhase_neg_pi_div_two :
    Complex.exp ((((-(Real.pi / 2) : ℝ) : ℂ) * Complex.I) / 2) =
      ons_turnRoot⁻¹ := by
  calc
    Complex.exp ((((-(Real.pi / 2) : ℝ) : ℂ) * Complex.I) / 2) =
        (Complex.exp ((((Real.pi / 2 : ℝ) : ℂ) * Complex.I) / 2))⁻¹ := by
      rw [← Complex.exp_neg]
      congr 1
      push_cast
      ring
    _ = ons_turnRoot⁻¹ := congrArg Inv.inv kwAngleTurnPhase_pi_div_two



theorem kwVectorTurnPhase_rectilinear
    (d e : Fin 4) (hnu : e ≠ d + 2) :
    kwVectorTurnPhase (kwRectilinearVector d) (kwRectilinearVector e) =
      ons_turnW ons_turnRoot d e := by
  rw [kwVectorTurnPhase, kwRectilinearVector_arg,
    kwRectilinearVector_arg]
  by_cases heq : e = d
  · subst e
    simp [kwAngleTurnPhase, ons_turnW]
  · have hcases : e = d + 1 ∨ e = d + 3 := by
      fin_cases d <;> fin_cases e <;> simp_all
    rcases hcases with rfl | rfl
    · rw [kwAngleTurnPhase, kwRectilinearAngle_succ_sub_toReal,
        kwAngleTurnPhase_pi_div_two]
      simp [ons_turnW]
    · rw [kwAngleTurnPhase, kwRectilinearAngle_pred_sub_toReal,
        kwAngleTurnPhase_neg_pi_div_two]
      have hne0 : d + 3 ≠ d := by fin_cases d <;> decide
      have hne1 : d + 3 ≠ d + 1 := by fin_cases d <;> decide
      simp [ons_turnW, hne0, hne1]



theorem kwRectilinearVector_phaseProduct_eq_neg_one
    {n : ℕ} [NeZero n] (d : Fin n → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0)
    (hsimple : Function.Injective (pos d))
    (hn : 3 ≤ n) (hnu : ∀ i, d (i + 1) ≠ d i + 2) :
    (∏ i, kwVectorTurnPhase (kwRectilinearVector (d i))
      (kwRectilinearVector (d (i + 1)))) = -1 := by
  calc
    (∏ i, kwVectorTurnPhase (kwRectilinearVector (d i))
        (kwRectilinearVector (d (i + 1)))) =
        ∏ i, ons_turnW ons_turnRoot (d i) (d (i + 1)) := by
      apply Finset.prod_congr rfl
      intro i _
      exact kwVectorTurnPhase_rectilinear _ _ (hnu i)
    _ = -1 :=
      StatMech.Onsager.GeneralUmlaufsatz.turnWeightProduct_eq_neg_one
        ons_turnRoot (by simp [ons_turnRoot]) ons_turnRoot_sq
        d hclosed hsimple hn hnu

end StatMech.FrontierA
