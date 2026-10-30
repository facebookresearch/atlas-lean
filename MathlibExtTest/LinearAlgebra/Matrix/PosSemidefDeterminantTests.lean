/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Matrix.PosSemidefDeterminant

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Tests for determinant inequalities of positive semidefinite matrices

* `!![2, 1; 1, 2]` is positive semidefinite (it is `1 + uᴴ * u` for
  `u = [1, 1]`), with determinant `3` and diagonal product `4`, so
  `det ≤ ∏ diag` holds strictly.
* `diagonal ![2, 3]` is positive semidefinite, with determinant `6`
  and trace `5`, so `6 ≤ (5 / 2) ^ 2`.
* `(2 : ℂ) • 1` is a nonnegative scalar matrix, so equality holds in
  the AM–GM bound.
* The trace of the product of `!![2, 1; 1, 2]` and `diagonal ![2, 3]`
  is `10 ≥ 0`.
-/

@[expose] public section

namespace MathlibExtTest.LinearAlgebra.Matrix.PosSemidefDeterminantTests

open scoped ComplexOrder

/-- `(0 : ℂ) ≤ 2` via the real-part order. -/
theorem zero_le_two_complex : (0 : ℂ) ≤ 2 := by
  rw [Complex.le_def]
  exact ⟨by simp, by simp⟩

/-- `(0 : ℂ) ≤ 3` via the real-part order. -/
theorem zero_le_three_complex : (0 : ℂ) ≤ 3 := by
  rw [Complex.le_def]
  exact ⟨by simp, by simp⟩

/-- `!![2, 1; 1, 2]` is positive semidefinite: it is `1 + uᴴ * u`. -/
theorem psd_two_one_one_two :
    (!![(2 : ℂ), 1; 1, 2]).PosSemidef := by
  have h : (!![(2 : ℂ), 1; 1, 2]) =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        Matrix.conjTranspose (!![(1 : ℂ), 1] : Matrix (Fin 1) (Fin 2) ℂ) *
          !![(1 : ℂ), 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply] <;> norm_num
  rw [h]
  exact Matrix.PosSemidef.one.add (Matrix.posSemidef_conjTranspose_mul_self _)

/-- The determinant of `!![2, 1; 1, 2]` is `3`. -/
theorem det_two_one_one_two : (!![(2 : ℂ), 1; 1, 2]).det = 3 := by
  rw [Matrix.det_fin_two]
  norm_num

/-- The diagonal product of `!![2, 1; 1, 2]` is `4`. -/
theorem prod_diag_two_one_one_two :
    ∏ i, ((!![(2 : ℂ), 1; 1, 2]) i i).re = 4 := by
  rw [Fin.prod_univ_two]
  norm_num [Matrix.of_apply]

/-- Hadamard's inequality for `!![2, 1; 1, 2]`: `3 ≤ 4`. -/
theorem det_le_prod_diag_two_one_one_two :
    ((!![(2 : ℂ), 1; 1, 2]).det).re ≤
      ∏ i, ((!![(2 : ℂ), 1; 1, 2]) i i).re :=
  psd_two_one_one_two.det_re_le_prod_diag_re

/-- `diagonal ![2, 3]` is positive semidefinite. -/
theorem psd_diag_two_three :
    (Matrix.diagonal ![(2 : ℂ), 3]).PosSemidef := by
  rw [Matrix.posSemidef_diagonal_iff]
  intro i
  fin_cases i
  · exact zero_le_two_complex
  · exact zero_le_three_complex

/-- The determinant of `diagonal ![2, 3]` is `6`. -/
theorem det_diag_two_three :
    (Matrix.diagonal ![(2 : ℂ), 3]).det = 6 := by
  rw [Matrix.det_diagonal, Fin.prod_univ_two]
  norm_num

/-- The trace of `diagonal ![2, 3]` is `5`. -/
theorem trace_diag_two_three :
    (Matrix.diagonal ![(2 : ℂ), 3]).trace = 5 := by
  rw [Matrix.trace_diagonal, Fin.sum_univ_two]
  norm_num

/-- AM–GM power form for `diagonal ![2, 3]`: `6 ≤ (5 / 2) ^ 2`. -/
theorem det_le_pow_trace_div_diag_two_three :
    ((Matrix.diagonal ![(2 : ℂ), 3]).det).re ≤
      (((Matrix.diagonal ![(2 : ℂ), 3]).trace).re / (2 : ℝ)) ^ 2 :=
  psd_diag_two_three.det_re_le_pow_trace_div (by norm_num)

/-- `(2 : ℂ) • 1` is positive semidefinite. -/
theorem psd_two_smul_one :
    (((2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))).PosSemidef :=
  Matrix.PosSemidef.smul (a := (2 : ℂ)) Matrix.PosSemidef.one zero_le_two_complex

/-- Equality in the AM–GM bound for the scalar matrix `(2 : ℂ) • 1`. -/
theorem amgm_eq_scalar_two :
    ((((2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)).det).re ^ ((2 : ℝ)⁻¹)) =
      ((((2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)).trace).re / (2 : ℝ)) :=
  (psd_two_smul_one.amgm_eq_iff (by norm_num)).mpr ⟨2, by norm_num, rfl⟩

/-- The `(0, 0)` entry of the product of `!![2, 1; 1, 2]` and
`diagonal ![2, 3]` is `4`. -/
theorem mul_diag_entry_zero_zero :
    (!![(2 : ℂ), 1; 1, 2] * Matrix.diagonal ![(2 : ℂ), 3]) 0 0 = 4 := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  simp
  norm_num

/-- The `(1, 1)` entry of the product of `!![2, 1; 1, 2]` and
`diagonal ![2, 3]` is `6`. -/
theorem mul_diag_entry_one_one :
    (!![(2 : ℂ), 1; 1, 2] * Matrix.diagonal ![(2 : ℂ), 3]) 1 1 = 6 := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  simp
  norm_num

/-- The trace of the product of `!![2, 1; 1, 2]` and
`diagonal ![2, 3]` is `10`. -/
theorem trace_mul_two_one_one_two_diag_two_three :
    ((!![(2 : ℂ), 1; 1, 2] * Matrix.diagonal ![(2 : ℂ), 3]).trace) = 10 := by
  show (∑ i, (!![(2 : ℂ), 1; 1, 2] * Matrix.diagonal ![(2 : ℂ), 3]) i i) = 10
  rw [Fin.sum_univ_two, mul_diag_entry_zero_zero, mul_diag_entry_one_one]
  norm_num

/-- The trace of the product of two positive semidefinite matrices is
nonnegative. -/
theorem trace_mul_nonneg_two_one_one_two_diag_two_three :
    0 ≤ (((!![(2 : ℂ), 1; 1, 2] * Matrix.diagonal ![(2 : ℂ), 3]).trace)).re :=
  psd_two_one_one_two.trace_mul_nonneg_re psd_diag_two_three

end MathlibExtTest.LinearAlgebra.Matrix.PosSemidefDeterminantTests
