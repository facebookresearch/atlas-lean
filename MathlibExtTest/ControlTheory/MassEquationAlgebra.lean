/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.ControlTheory.MassEquationAlgebra
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

open ControlTheory
open scoped Matrix

/-- The diagonal mass matrix `diag(2, 3)` used in the examples. -/
private def massEx : Matrix (Fin 2) (Fin 2) ℝ := !![2, 0; 0, 3]

private theorem massEx_unit : IsUnit massEx.det := by
  rw [massEx, Matrix.det_fin_two]
  norm_num

-- Rectangular input matrix (2×3), torque, and state terms.
-- Net force: B *ᵥ τ = (2, 15), C *ᵥ v = (0, -2), so F = (1, 14),
-- and the acceleration is (1/2, 14/3).
example :
    massEx *ᵥ ![1 / 2, 14 / 3]
      = !![1, 2, -1; 4, -2, 5] *ᵥ ![1, 2, 3]
        - !![1, 1; 0, 2] *ᵥ ![1, -1] - ![1, 3] := by
  ext i
  fin_cases i <;>
    simp [massEx, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Fin.sum_univ_three] <;> norm_num

example :
    ![1 / 2, 14 / 3]
      = massEx⁻¹ *ᵥ (!![1, 2, -1; 4, -2, 5] *ᵥ ![1, 2, 3]
        - !![1, 1; 0, 2] *ᵥ ![1, -1] - ![1, 3]) :=
  (Matrix.mulVec_eq_iff_inv_mulVec (A := massEx) massEx_unit).mp (by
      ext i
      fin_cases i <;>
        simp [massEx, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
          Fin.sum_univ_three] <;> norm_num)

-- The zero mass matrix is excluded: its determinant is not a unit,
-- and the inversion equivalence fails for it.
example : ¬ IsUnit (0 : Matrix (Fin 2) (Fin 2) ℝ).det := by
  rw [Matrix.det_zero]
  exact not_isUnit_zero

example :
    (0 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ![1, 0] = 0
      ∧ ![1, 0] ≠ (0 : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ *ᵥ 0 := by
  refine ⟨by simp [Matrix.mulVec], ?_⟩
  simp

-- Gravity only (τ = 0, v = 0, g = (0, 9)): the acceleration is
-- (0, -3), i.e. M⁻¹ *ᵥ (-g) with the gravity sign preserved.
example :
    ![0, -3] = massEx⁻¹ *ᵥ (!![1, 2, -1; 4, -2, 5] *ᵥ 0
      - !![1, 1; 0, 2] *ᵥ 0 - ![0, 9]) :=
  (Matrix.mulVec_eq_iff_inv_mulVec (A := massEx) massEx_unit).mp (by
      ext i
      fin_cases i <;>
        simp [massEx, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
          Fin.sum_univ_three] <;> norm_num)

-- The first-order right-hand side at v = (1, 2), F = (4, 9) is
-- ((1, 2), (2, 3)); a pair with the wrong position derivative is
-- rejected even when its acceleration is correct.
example :
    (![1, 2], ![2, 3]) = firstOrderRhs massEx ![4, 9] ![1, 2] :=
  (eq_firstOrderRhs_iff massEx massEx_unit _ _ _ _).mpr ⟨rfl, by
    ext i
    fin_cases i <;>
      simp [massEx, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
        norm_num⟩

example :
    (![0, 2], ![2, 3]) ≠ firstOrderRhs massEx ![4, 9] ![1, 2] := by
  intro h
  have h1 := ((eq_firstOrderRhs_iff massEx massEx_unit _ _ _ _).mp h).1
  have h0 := congrFun h1 0
  norm_num at h0

#print axioms eq_firstOrderRhs_iff
