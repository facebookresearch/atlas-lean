/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import all MathlibExt.LinearAlgebra.Matrix.Factorizations.Polar
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

namespace Matrix

/-- The canonical polar factor of a zero matrix is zero in all dimensions. -/
example (m n : ℕ) : polarFactor (0 : Matrix (Fin m) (Fin n) ℝ) = 0 := by
  rw [polarFactor_eq_of_svd (U := 1) (V := 1) (σ := 0) (by simp) (by simp)
    (one_mem _) (one_mem _) (by ext i j; simp [polarRectangularDiagonal])]
  ext i j
  simp [polarRectangularDiagonal]

/-- For this rank-one `2 × 3` matrix, the factor normalizes the nonzero singular value
and does not fill in the second diagonal entry. -/
example : polarFactor (!![2, 0, 0; 0, 0, 0] : Matrix (Fin 2) (Fin 3) ℝ) =
    !![1, 0, 0; 0, 0, 0] := by
  let σ : Fin 3 → ℝ := ![2, 0, 0]
  have hσ (j : Fin 3) : 0 ≤ σ j := by
    fin_cases j <;> norm_num [σ, Matrix.cons_val_zero, Matrix.cons_val_succ]
  have hzero (j : Fin 3) (hj : 2 ≤ j.val) : σ j = 0 := by
    fin_cases j <;> norm_num [σ, Matrix.cons_val_zero, Matrix.cons_val_succ] at *
  have hG : (!![2, 0, 0; 0, 0, 0] : Matrix (Fin 2) (Fin 3) ℝ) =
      (1 : Matrix (Fin 2) (Fin 2) ℝ) * polarRectangularDiagonal σ *
        (1 : Matrix (Fin 3) (Fin 3) ℝ)ᵀ := by
    simp only [transpose_one, Matrix.one_mul, Matrix.mul_one]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [σ, Matrix.cons_val_zero, Matrix.cons_val_succ]
  rw [polarFactor_eq_of_svd hσ hzero (one_mem _) (one_mem _) hG,
    transpose_one, Matrix.one_mul, Matrix.mul_one]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [σ, Matrix.cons_val_zero, Matrix.cons_val_succ]

/-- For this `2 × 1` matrix, with more rows than columns, an SVD with left factor the rotation
`!![0, 1; -1, 0]` shows that the polar factor is the unit column `!![0; -1]`. -/
example : polarFactor (!![0; -3] : Matrix (Fin 2) (Fin 1) ℝ) = !![0; -1] := by
  let U : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]
  have hU : U ∈ orthogonalGroup (Fin 2) ℝ := by
    rw [mem_orthogonalGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [U, Matrix.mul_apply, Fin.sum_univ_two]
  have hG : (!![0; -3] : Matrix (Fin 2) (Fin 1) ℝ) =
      U * polarRectangularDiagonal ![3] * (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [U, Matrix.mul_apply, Matrix.vecHead, Matrix.vecTail]
  rw [polarFactor_eq_of_svd (by simp) (fun j hj => absurd hj (by have := j.isLt; omega)) hU
    (one_mem _) hG]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [U, Matrix.mul_apply, Matrix.vecHead, Matrix.vecTail]

end Matrix
