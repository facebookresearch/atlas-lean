/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.QuaternionRotationAxisAngle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Tests for the quaternion axis-angle rotation formula
-/

@[expose] public section

namespace QuaternionRotation

/-- Quarter turn about `e₃`: the contract instance. -/
example : rotMatrix (axisAngle ![0, 0, 1] (Real.pi / 2)) = !![0, -1, 0; 1, 0, 0; 0, 0, 1] := by
  have hu : ((![0, 0, 1] : Fin 3 → ℝ) 0 ^ 2 + (![0, 0, 1] : Fin 3 → ℝ) 1 ^ 2 +
      (![0, 0, 1] : Fin 3 → ℝ) 2 ^ 2 = 1) := by
    norm_num [Matrix.cons_val_two]
  rw [rotMatrix_axisAngle hu, Real.cos_pi_div_two, Real.sin_pi_div_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.cons_val_two]

/-- The quarter turn sends `e₁` to `e₂`. -/
example : Matrix.mulVec (rotMatrix (axisAngle ![0, 0, 1] (Real.pi / 2))) ![1, 0, 0] =
    ![0, 1, 0] := by
  have hu : ((![0, 0, 1] : Fin 3 → ℝ) 0 ^ 2 + (![0, 0, 1] : Fin 3 → ℝ) 1 ^ 2 +
      (![0, 0, 1] : Fin 3 → ℝ) 2 ^ 2 = 1) := by
    norm_num [Matrix.cons_val_two]
  rw [rotMatrix_axisAngle hu, Real.cos_pi_div_two, Real.sin_pi_div_two]
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_three, Matrix.cons_val_two]

/-- The quarter turn sends `e₂` to `-e₁`. -/
example : Matrix.mulVec (rotMatrix (axisAngle ![0, 0, 1] (Real.pi / 2))) ![0, 1, 0] =
    ![-1, 0, 0] := by
  have hu : ((![0, 0, 1] : Fin 3 → ℝ) 0 ^ 2 + (![0, 0, 1] : Fin 3 → ℝ) 1 ^ 2 +
      (![0, 0, 1] : Fin 3 → ℝ) 2 ^ 2 = 1) := by
    norm_num [Matrix.cons_val_two]
  rw [rotMatrix_axisAngle hu, Real.cos_pi_div_two, Real.sin_pi_div_two]
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_three, Matrix.cons_val_two]

/-- The quarter turn fixes `e₃`. -/
example : Matrix.mulVec (rotMatrix (axisAngle ![0, 0, 1] (Real.pi / 2))) ![0, 0, 1] =
    ![0, 0, 1] := by
  have hu : ((![0, 0, 1] : Fin 3 → ℝ) 0 ^ 2 + (![0, 0, 1] : Fin 3 → ℝ) 1 ^ 2 +
      (![0, 0, 1] : Fin 3 → ℝ) 2 ^ 2 = 1) := by
    norm_num [Matrix.cons_val_two]
  rw [rotMatrix_axisAngle hu, Real.cos_pi_div_two, Real.sin_pi_div_two]
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_three, Matrix.cons_val_two]

/-- The Rodrigues formula sends `e₁` to `e₂` for the `e₃` quarter turn. -/
example : Matrix.mulVec (rotMatrix (axisAngle ![0, 0, 1] (Real.pi / 2))) ![1, 0, 0] =
    ![0, 1, 0] := by
  have hu : ((![0, 0, 1] : Fin 3 → ℝ) 0 ^ 2 + (![0, 0, 1] : Fin 3 → ℝ) 1 ^ 2 +
      (![0, 0, 1] : Fin 3 → ℝ) 2 ^ 2 = 1) := by
    norm_num [Matrix.cons_val_two]
  rw [rotMatrix_axisAngle_mulVec hu, Real.cos_pi_div_two, Real.sin_pi_div_two]
  funext i
  fin_cases i <;> simp [cross_apply, Matrix.cons_val_two]

/-- Angle `0` gives the quaternion `1`, for every axis. -/
example (u : Fin 3 → ℝ) : axisAngle u 0 = 1 := by
  simp only [axisAngle, zero_div, Real.cos_zero, Real.sin_zero, zero_mul]
  rfl

/-- Angle `0` gives the identity matrix, for a unit axis. -/
example : rotMatrix (axisAngle ![0, 0, 1] 0) = 1 := by
  have hu : ((![0, 0, 1] : Fin 3 → ℝ) 0 ^ 2 + (![0, 0, 1] : Fin 3 → ℝ) 1 ^ 2 +
      (![0, 0, 1] : Fin 3 → ℝ) 2 ^ 2 = 1) := by
    norm_num [Matrix.cons_val_two]
  rw [rotMatrix_axisAngle hu, Real.cos_zero, Real.sin_zero, Matrix.one_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.cons_val_two]

/-- The quarter-turn quaternion has norm `1`. -/
example : ‖axisAngle ![0, 0, 1] (Real.pi / 2)‖ = 1 := by
  have hu : ((![0, 0, 1] : Fin 3 → ℝ) 0 ^ 2 + (![0, 0, 1] : Fin 3 → ℝ) 1 ^ 2 +
      (![0, 0, 1] : Fin 3 → ℝ) 2 ^ 2 = 1) := by
    norm_num [Matrix.cons_val_two]
  exact norm_axisAngle hu _

/-- A non-coordinate axis is fixed by its own rotation. -/
example : Matrix.mulVec (rotMatrix (axisAngle ![3 / 5, 4 / 5, 0] (Real.pi / 3)))
    ![3 / 5, 4 / 5, 0] = ![3 / 5, 4 / 5, 0] := by
  have hu : ((![3 / 5, 4 / 5, 0] : Fin 3 → ℝ) 0 ^ 2 + (![3 / 5, 4 / 5, 0] : Fin 3 → ℝ) 1 ^ 2 +
      (![3 / 5, 4 / 5, 0] : Fin 3 → ℝ) 2 ^ 2 = 1) := by
    norm_num [Matrix.cons_val_two]
  exact rotMatrix_axisAngle_mulVec_self hu _

/-- A fixed axis with a negative coordinate is fixed by its own rotation. -/
example : Matrix.mulVec (rotMatrix (axisAngle ![-3 / 5, 0, 4 / 5] (Real.pi / 3)))
    ![-3 / 5, 0, 4 / 5] = ![-3 / 5, 0, 4 / 5] := by
  have hu : ((![-3 / 5, 0, 4 / 5] : Fin 3 → ℝ) 0 ^ 2 +
      (![-3 / 5, 0, 4 / 5] : Fin 3 → ℝ) 1 ^ 2 + (![-3 / 5, 0, 4 / 5] : Fin 3 → ℝ) 2 ^ 2 = 1) := by
    norm_num [Matrix.cons_val_two]
  exact rotMatrix_axisAngle_mulVec_self hu _

/-- Angle `2 * π` gives the identity matrix (the `-1` quaternion case). -/
example : rotMatrix (axisAngle ![0, 0, 1] (2 * Real.pi)) = 1 := by
  have hu : ((![0, 0, 1] : Fin 3 → ℝ) 0 ^ 2 + (![0, 0, 1] : Fin 3 → ℝ) 1 ^ 2 +
      (![0, 0, 1] : Fin 3 → ℝ) 2 ^ 2 = 1) := by
    norm_num [Matrix.cons_val_two]
  rw [rotMatrix_axisAngle hu, Real.cos_two_pi, Real.sin_two_pi, Matrix.one_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.cons_val_two]

end QuaternionRotation
