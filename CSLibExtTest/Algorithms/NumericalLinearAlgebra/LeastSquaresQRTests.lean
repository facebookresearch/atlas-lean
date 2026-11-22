/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.NumericalLinearAlgebra.LeastSquaresQR

@[expose] public section

open Matrix Cslib.MachineLearning.LeastSquares Cslib.Algorithms.NumericalLinearAlgebra.LeastSquaresQR

namespace CSLibExtTest.Algorithms.NumericalLinearAlgebra.LeastSquaresQR

/-- With `Q = R = I` the least-squares solution of `I θ = y` is `y` itself. -/
example (y θ₀ : Fin 2 → ℝ) :
    (∀ θ, rss (1 : Matrix (Fin 2) (Fin 2) ℝ) y θ₀ ≤ rss (1 : Matrix (Fin 2) (Fin 2) ℝ) y θ) ↔ θ₀ = y := by
  rw [rss_le_iff_of_qr (Q := 1) (R := 1) (by simp) (by simp) (by simp)]
  simp

/-- Fitting a constant to the data `(0, 2)`: `X = (1, 1)ᵀ = Q R` with `Q = (1, 1)ᵀ / √2` and
`R = √2`, so the solution is `R⁻¹ Qᵀ y = 1`, the mean. -/
example : ∀ θ, rss (!![1; 1] : Matrix (Fin 2) (Fin 1) ℝ) ![0, 2] ![1] ≤
    rss !![1; 1] ![0, 2] θ := by
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs0 : Real.sqrt 2 ≠ 0 := by positivity
  rw [rss_le_iff_of_qr (Q := !![1 / Real.sqrt 2; 1 / Real.sqrt 2]) (R := !![Real.sqrt 2])]
  · ext i; fin_cases i
    simp [mulVec, dotProduct]
    field_simp
    linarith
  · ext i j; fin_cases i; fin_cases j
    simp [mul_apply, Fin.sum_univ_two]
    field_simp
    linarith
  · simp [hs0]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, hs0]

/-- With linearly independent columns the least-squares solution is unique. -/
example (y : Fin 3 → ℝ) :
    ∃! θ₀ : Fin 3 → ℝ, ∀ θ, rss (1 : Matrix (Fin 3) (Fin 3) ℝ) y θ₀ ≤ rss (1 : Matrix (Fin 3) (Fin 3) ℝ) y θ :=
  existsUnique_rss_le _ (by
    rw [transpose_one]; exact Matrix.linearIndependent_rows_of_det_ne_zero (by simp)) y

end CSLibExtTest.Algorithms.NumericalLinearAlgebra.LeastSquaresQR
