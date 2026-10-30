/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Matrix.MinkowskiDeterminant

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Tests for Minkowski's determinant inequality

* `diagonal ![1, 4]` and `diagonal ![4, 1]` are positive semidefinite,
  with `det = 4` for each and `det (A + B) = 25`, so Minkowski gives
  `2 + 2 ≤ 5`.
* `diagonal ![2, 1]` and `diagonal ![1, 3]` are positive semidefinite,
  with `det = 2` and `3` and `det (A + B) = 12`, so Minkowski gives
  `√2 + √3 ≤ √12`.
* `diagonal ![1, 0]` and `diagonal ![0, 1]` are singular positive
  semidefinite, with `det = 0` for each and `det (A + B) = 1`, so
  Minkowski gives `0 + 0 ≤ 1` (this exercises the `ε → 0⁺` limit:
  the first matrix is not positive definite).
* In dimension one, `diagonal ![2]` and `diagonal ![3]` give `2 + 3 ≤ 5`.
* Determinant monotonicity: `det (diagonal ![1, 3]) = 3 ≤ 12 =
  det (diagonal ![3, 4])`.
* Determinant monotonicity also applies in dimension zero, where both determinants are `1`.
-/

@[expose] public section

namespace MathlibExtTest.LinearAlgebra.Matrix.MinkowskiDeterminantTests

open scoped ComplexOrder

/-- `diagonal ![1, 4]` is positive semidefinite. -/
theorem psd_diag_one_four :
    (Matrix.diagonal ![((1 : ℝ) : ℂ), ((4 : ℝ) : ℂ)]).PosSemidef := by
  rw [Matrix.posSemidef_diagonal_iff]
  intro i
  fin_cases i <;> simp

/-- `diagonal ![4, 1]` is positive semidefinite. -/
theorem psd_diag_four_one :
    (Matrix.diagonal ![((4 : ℝ) : ℂ), ((1 : ℝ) : ℂ)]).PosSemidef := by
  rw [Matrix.posSemidef_diagonal_iff]
  intro i
  fin_cases i <;> simp

/-- Minkowski's inequality for `diagonal ![1, 4]` and `diagonal ![4, 1]`:
`√4 + √4 = 2 + 2 ≤ 5 = √25`. -/
theorem minkowski_diag_swap :
    ((Matrix.diagonal ![((1 : ℝ) : ℂ), ((4 : ℝ) : ℂ)]).det).re ^ ((2 : ℝ)⁻¹) +
      ((Matrix.diagonal ![((4 : ℝ) : ℂ), ((1 : ℝ) : ℂ)]).det).re ^ ((2 : ℝ)⁻¹) ≤
      ((Matrix.diagonal ![((1 : ℝ) : ℂ), ((4 : ℝ) : ℂ)] +
        Matrix.diagonal ![((4 : ℝ) : ℂ), ((1 : ℝ) : ℂ)]).det).re ^ ((2 : ℝ)⁻¹) := by
  have h := Matrix.PosSemidef.minkowski_det psd_diag_one_four psd_diag_four_one
    (show 0 < 2 by norm_num)
  have hA : ((Matrix.diagonal ![((1 : ℝ) : ℂ), ((4 : ℝ) : ℂ)]).det).re = 4 := by
    rw [Matrix.det_diagonal, Fin.prod_univ_two]
    norm_num
  have hB : ((Matrix.diagonal ![((4 : ℝ) : ℂ), ((1 : ℝ) : ℂ)]).det).re = 4 := by
    rw [Matrix.det_diagonal, Fin.prod_univ_two]
    norm_num
  have hAB : ((Matrix.diagonal ![((1 : ℝ) : ℂ), ((4 : ℝ) : ℂ)] +
      Matrix.diagonal ![((4 : ℝ) : ℂ), ((1 : ℝ) : ℂ)]).det).re = 25 := by
    have hsum : Matrix.diagonal ![((1 : ℝ) : ℂ), ((4 : ℝ) : ℂ)] +
        Matrix.diagonal ![((4 : ℝ) : ℂ), ((1 : ℝ) : ℂ)] =
        Matrix.diagonal ![((5 : ℝ) : ℂ), ((5 : ℝ) : ℂ)] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp <;> norm_num
    rw [hsum, Matrix.det_diagonal, Fin.prod_univ_two]
    norm_num
  rw [hA, hB, hAB] at h
  rw [hA, hB, hAB]
  have h' : (4 : ℝ) ^ ((2 : ℝ)⁻¹) + (4 : ℝ) ^ ((2 : ℝ)⁻¹) ≤ (25 : ℝ) ^ ((2 : ℝ)⁻¹) := h
  have h4 : (4 : ℝ) ^ ((2 : ℝ)⁻¹) = 2 := by
    rw [show ((2 : ℝ)⁻¹) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow,
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have h25 : (25 : ℝ) ^ ((2 : ℝ)⁻¹) = 5 := by
    rw [show ((2 : ℝ)⁻¹) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow,
      show (25 : ℝ) = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h4, h25]
  rw [h4, h25] at h'
  exact h' 

/-- `diagonal ![2, 1]` is positive semidefinite. -/
theorem psd_diag_two_one :
    (Matrix.diagonal ![((2 : ℝ) : ℂ), ((1 : ℝ) : ℂ)]).PosSemidef := by
  rw [Matrix.posSemidef_diagonal_iff]
  intro i
  fin_cases i <;> simp

/-- `diagonal ![1, 3]` is positive semidefinite. -/
theorem psd_diag_one_three :
    (Matrix.diagonal ![((1 : ℝ) : ℂ), ((3 : ℝ) : ℂ)]).PosSemidef := by
  rw [Matrix.posSemidef_diagonal_iff]
  intro i
  fin_cases i <;> simp

/-- Minkowski's inequality for `diagonal ![2, 1]` and `diagonal ![1, 3]`:
`√2 + √3 ≤ √12`. -/
theorem minkowski_diag_two_one_one_three :
    ((Matrix.diagonal ![((2 : ℝ) : ℂ), ((1 : ℝ) : ℂ)]).det).re ^ ((2 : ℝ)⁻¹) +
      ((Matrix.diagonal ![((1 : ℝ) : ℂ), ((3 : ℝ) : ℂ)]).det).re ^ ((2 : ℝ)⁻¹) ≤
      ((Matrix.diagonal ![((2 : ℝ) : ℂ), ((1 : ℝ) : ℂ)] +
        Matrix.diagonal ![((1 : ℝ) : ℂ), ((3 : ℝ) : ℂ)]).det).re ^ ((2 : ℝ)⁻¹) := by
  have h := Matrix.PosSemidef.minkowski_det psd_diag_two_one psd_diag_one_three
    (show 0 < 2 by norm_num)
  have hA : ((Matrix.diagonal ![((2 : ℝ) : ℂ), ((1 : ℝ) : ℂ)]).det).re = 2 := by
    rw [Matrix.det_diagonal, Fin.prod_univ_two]
    norm_num
  have hB : ((Matrix.diagonal ![((1 : ℝ) : ℂ), ((3 : ℝ) : ℂ)]).det).re = 3 := by
    rw [Matrix.det_diagonal, Fin.prod_univ_two]
    norm_num
  have hAB : ((Matrix.diagonal ![((2 : ℝ) : ℂ), ((1 : ℝ) : ℂ)] +
      Matrix.diagonal ![((1 : ℝ) : ℂ), ((3 : ℝ) : ℂ)]).det).re = 12 := by
    have hsum : Matrix.diagonal ![((2 : ℝ) : ℂ), ((1 : ℝ) : ℂ)] +
        Matrix.diagonal ![((1 : ℝ) : ℂ), ((3 : ℝ) : ℂ)] =
        Matrix.diagonal ![((3 : ℝ) : ℂ), ((4 : ℝ) : ℂ)] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp <;> norm_num
    rw [hsum, Matrix.det_diagonal, Fin.prod_univ_two]
    norm_num
  rw [hA, hB, hAB] at h
  have h' : (2 : ℝ) ^ ((2 : ℝ)⁻¹) + (3 : ℝ) ^ ((2 : ℝ)⁻¹) ≤ (12 : ℝ) ^ ((2 : ℝ)⁻¹) := h
  rw [show ((2 : ℝ)⁻¹) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow,
    ← Real.sqrt_eq_rpow] at h'
  rw [hA, hB, hAB]
  rw [show ((2 : ℝ)⁻¹) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow,
    ← Real.sqrt_eq_rpow]
  exact h' 

/-- `diagonal ![1, 0]` is positive semidefinite (singular). -/
theorem psd_diag_one_zero :
    (Matrix.diagonal ![((1 : ℝ) : ℂ), ((0 : ℝ) : ℂ)]).PosSemidef := by
  rw [Matrix.posSemidef_diagonal_iff]
  intro i
  fin_cases i <;> simp

/-- `diagonal ![0, 1]` is positive semidefinite (singular). -/
theorem psd_diag_zero_one :
    (Matrix.diagonal ![((0 : ℝ) : ℂ), ((1 : ℝ) : ℂ)]).PosSemidef := by
  rw [Matrix.posSemidef_diagonal_iff]
  intro i
  fin_cases i <;> simp

/-- Minkowski's inequality for the singular pair
`diagonal ![1, 0]`, `diagonal ![0, 1]`: `0 + 0 ≤ 1`. -/
theorem minkowski_diag_singular :
    ((Matrix.diagonal ![((1 : ℝ) : ℂ), ((0 : ℝ) : ℂ)]).det).re ^ ((2 : ℝ)⁻¹) +
      ((Matrix.diagonal ![((0 : ℝ) : ℂ), ((1 : ℝ) : ℂ)]).det).re ^ ((2 : ℝ)⁻¹) ≤
      ((Matrix.diagonal ![((1 : ℝ) : ℂ), ((0 : ℝ) : ℂ)] +
        Matrix.diagonal ![((0 : ℝ) : ℂ), ((1 : ℝ) : ℂ)]).det).re ^ ((2 : ℝ)⁻¹) := by
  have h := Matrix.PosSemidef.minkowski_det psd_diag_one_zero psd_diag_zero_one
    (show 0 < 2 by norm_num)
  have hA : ((Matrix.diagonal ![((1 : ℝ) : ℂ), ((0 : ℝ) : ℂ)]).det).re = 0 := by
    rw [Matrix.det_diagonal, Fin.prod_univ_two]
    norm_num
  have hB : ((Matrix.diagonal ![((0 : ℝ) : ℂ), ((1 : ℝ) : ℂ)]).det).re = 0 := by
    rw [Matrix.det_diagonal, Fin.prod_univ_two]
    norm_num
  have hAB : ((Matrix.diagonal ![((1 : ℝ) : ℂ), ((0 : ℝ) : ℂ)] +
      Matrix.diagonal ![((0 : ℝ) : ℂ), ((1 : ℝ) : ℂ)]).det).re = 1 := by
    have hsum : Matrix.diagonal ![((1 : ℝ) : ℂ), ((0 : ℝ) : ℂ)] +
        Matrix.diagonal ![((0 : ℝ) : ℂ), ((1 : ℝ) : ℂ)] =
        Matrix.diagonal ![((1 : ℝ) : ℂ), ((1 : ℝ) : ℂ)] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    rw [hsum, Matrix.det_diagonal, Fin.prod_univ_two]
    norm_num
  rw [hA, hB, hAB] at h
  have h' : (0 : ℝ) ^ ((2 : ℝ)⁻¹) + (0 : ℝ) ^ ((2 : ℝ)⁻¹) ≤ (1 : ℝ) ^ ((2 : ℝ)⁻¹) := h
  rw [Real.zero_rpow (by norm_num : ((2 : ℝ)⁻¹) ≠ 0), Real.one_rpow] at h'
  rw [hA, hB, hAB]
  rw [Real.zero_rpow (by norm_num : ((2 : ℝ)⁻¹) ≠ 0), Real.one_rpow]
  exact h' 

/-- `diagonal ![2]` is positive semidefinite. -/
theorem psd_diag_single_two :
    (Matrix.diagonal ![((2 : ℝ) : ℂ)]).PosSemidef := by
  rw [Matrix.posSemidef_diagonal_iff]
  intro i
  fin_cases i
  simp

/-- `diagonal ![3]` is positive semidefinite. -/
theorem psd_diag_single_three :
    (Matrix.diagonal ![((3 : ℝ) : ℂ)]).PosSemidef := by
  rw [Matrix.posSemidef_diagonal_iff]
  intro i
  fin_cases i
  simp

/-- Minkowski's inequality in dimension one: `2 + 3 ≤ 5`. -/
theorem minkowski_one_dim :
    ((Matrix.diagonal ![((2 : ℝ) : ℂ)]).det).re ^ ((1 : ℝ)⁻¹) +
      ((Matrix.diagonal ![((3 : ℝ) : ℂ)]).det).re ^ ((1 : ℝ)⁻¹) ≤
      ((Matrix.diagonal ![((2 : ℝ) : ℂ)] +
        Matrix.diagonal ![((3 : ℝ) : ℂ)]).det).re ^ ((1 : ℝ)⁻¹) := by
  have h := Matrix.PosSemidef.minkowski_det psd_diag_single_two psd_diag_single_three
    (show 0 < 1 by norm_num)
  have hA : ((Matrix.diagonal ![((2 : ℝ) : ℂ)]).det).re = 2 := by
    rw [Matrix.det_diagonal, Fin.prod_univ_one]
    norm_num
  have hB : ((Matrix.diagonal ![((3 : ℝ) : ℂ)]).det).re = 3 := by
    rw [Matrix.det_diagonal, Fin.prod_univ_one]
    norm_num
  have hAB : ((Matrix.diagonal ![((2 : ℝ) : ℂ)] +
      Matrix.diagonal ![((3 : ℝ) : ℂ)]).det).re = 5 := by
    have hsum : Matrix.diagonal ![((2 : ℝ) : ℂ)] +
        Matrix.diagonal ![((3 : ℝ) : ℂ)] =
        Matrix.diagonal ![((5 : ℝ) : ℂ)] := by
      ext i j
      fin_cases i
      fin_cases j
      simp
      norm_num
    rw [hsum, Matrix.det_diagonal, Fin.prod_univ_one]
    norm_num
  rw [hA, hB, hAB] at h
  have h' : (2 : ℝ) ^ ((1 : ℝ)⁻¹) + (3 : ℝ) ^ ((1 : ℝ)⁻¹) ≤ (5 : ℝ) ^ ((1 : ℝ)⁻¹) := by
    simpa using h
  rw [show ((1 : ℝ)⁻¹) = 1 by norm_num, Real.rpow_one, Real.rpow_one, Real.rpow_one] at h'
  rw [hA, hB, hAB]
  rw [show ((1 : ℝ)⁻¹) = 1 by norm_num, Real.rpow_one, Real.rpow_one, Real.rpow_one]
  exact h' 

/-- Determinant monotonicity: `3 = det (diagonal ![1, 3]) ≤
det (diagonal ![3, 4]) = 12`. -/
theorem det_le_det_add_diag :
    ((Matrix.diagonal ![((1 : ℝ) : ℂ), ((3 : ℝ) : ℂ)]).det).re ≤
      ((Matrix.diagonal ![((2 : ℝ) : ℂ), ((1 : ℝ) : ℂ)] +
        Matrix.diagonal ![((1 : ℝ) : ℂ), ((3 : ℝ) : ℂ)]).det).re := by
  have h := Matrix.PosSemidef.det_le_det_add psd_diag_two_one psd_diag_one_three
  have hB : ((Matrix.diagonal ![((1 : ℝ) : ℂ), ((3 : ℝ) : ℂ)]).det).re = 3 := by
    rw [Matrix.det_diagonal, Fin.prod_univ_two]
    norm_num
  have hAB : ((Matrix.diagonal ![((2 : ℝ) : ℂ), ((1 : ℝ) : ℂ)] +
      Matrix.diagonal ![((1 : ℝ) : ℂ), ((3 : ℝ) : ℂ)]).det).re = 12 := by
    have hsum : Matrix.diagonal ![((2 : ℝ) : ℂ), ((1 : ℝ) : ℂ)] +
        Matrix.diagonal ![((1 : ℝ) : ℂ), ((3 : ℝ) : ℂ)] =
        Matrix.diagonal ![((3 : ℝ) : ℂ), ((4 : ℝ) : ℂ)] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp <;> norm_num
    rw [hsum, Matrix.det_diagonal, Fin.prod_univ_two]
    norm_num
  rw [hB, hAB] at h
  rw [hB, hAB]
  exact h

/-- Determinant monotonicity includes zero-dimensional positive semidefinite matrices. -/
theorem det_le_det_add_zero_dim {A B : Matrix (Fin 0) (Fin 0) ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (B.det).re ≤ ((A + B).det).re := by
  exact Matrix.PosSemidef.det_le_det_add hA hB

end MathlibExtTest.LinearAlgebra.Matrix.MinkowskiDeterminantTests
