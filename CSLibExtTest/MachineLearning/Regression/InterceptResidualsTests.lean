/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Regression.InterceptResiduals
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Tests for intercept residuals

A constant design with responses `1, 3` has fit `2` and residuals `-1, 1`; a rank-deficient
design with two identical intercept columns still has zero residual sum; a design without an
intercept (`x = (1, 2)`, `y = (1, 1)`, fit `3/5`) has residual sum `1/5 ≠ 0`.
-/

@[expose] public section

namespace CSLibExtTest.MachineLearning.Regression.InterceptResidualsTests

open Cslib.MachineLearning.LeastSquares
open Matrix
open Finset

-- Test section (ST01.T01 acceptance examples).


private def Xa : Matrix (Fin 2) (Fin 1) ℝ := fun _ _ => 1
private def ya : Fin 2 → ℝ := ![1, 3]
private def θa : Fin 1 → ℝ := fun _ => 2

-- (a) Normal equations for the one-constant-column design.
example : Xaᵀ *ᵥ (Xa *ᵥ θa) = Xaᵀ *ᵥ ya := by
  funext j
  fin_cases j
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Fin.sum_univ_two,
    Fin.sum_univ_one, Xa, ya, θa, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

-- (a) Residuals sum to zero, via `sum_residual_eq_zero_of_normal`.
example : ∑ k, (ya - Xa *ᵥ θa) k = 0 := by
  have hθ : Xaᵀ *ᵥ (Xa *ᵥ θa) = Xaᵀ *ᵥ ya := by
    funext j
    fin_cases j
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Fin.sum_univ_two,
      Fin.sum_univ_one, Xa, ya, θa, Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  have hj : HasInterceptColumn Xa 0 := fun _ => rfl
  exact sum_residual_eq_zero_of_normal hθ hj

-- (a) Residuals sum to zero, via `sum_residual_eq_zero_of_rss_le`.
example : ∑ k, (ya - Xa *ᵥ θa) k = 0 := by
  have hθ : Xaᵀ *ᵥ (Xa *ᵥ θa) = Xaᵀ *ᵥ ya := by
    funext j
    fin_cases j
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Fin.sum_univ_two,
      Fin.sum_univ_one, Xa, ya, θa, Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  have hj : HasInterceptColumn Xa 0 := fun _ => rfl
  exact sum_residual_eq_zero_of_rss_le (rss_le_of_normal hθ) hj

-- (a) Residuals compute to `-1, 1`.
example : (ya - Xa *ᵥ θa) 0 = -1 ∧ (ya - Xa *ᵥ θa) 1 = 1 := by
  constructor
  · simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_one, Xa, ya, θa,
      Matrix.cons_val_zero]
    norm_num
  · simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_one, Xa, ya, θa,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num

private def Xb : Matrix (Fin 2) (Fin 2) ℝ := fun _ _ => 1
private def yb : Fin 2 → ℝ := ![1, 3]
private def θb : Fin 2 → ℝ := ![1, 1]

-- (b) Normal equations for the rank-deficient two-identical-columns design.
example : Xbᵀ *ᵥ (Xb *ᵥ θb) = Xbᵀ *ᵥ yb := by
  funext j
  fin_cases j
  · simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Fin.sum_univ_two, Xb, yb,
      θb, Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  · simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Fin.sum_univ_two, Xb, yb,
      θb, Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num

-- (b) Residuals sum to zero (no rank condition needed).
example : ∑ k, (yb - Xb *ᵥ θb) k = 0 := by
  have hθ : Xbᵀ *ᵥ (Xb *ᵥ θb) = Xbᵀ *ᵥ yb := by
    funext j
    fin_cases j
    · simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Fin.sum_univ_two, Xb, yb,
        θb, Matrix.cons_val_zero, Matrix.cons_val_one]
      norm_num
    · simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Fin.sum_univ_two, Xb, yb,
        θb, Matrix.cons_val_zero, Matrix.cons_val_one]
      norm_num
  have hj : HasInterceptColumn Xb 0 := fun _ => rfl
  exact sum_residual_eq_zero_of_normal hθ hj

-- `Xc` is the `!![1; 2]` design: one column with entries `1, 2` (no intercept).
private def Xc : Matrix (Fin 2) (Fin 1) ℝ := fun k _ => ![1, 2] k
private def yc : Fin 2 → ℝ := ![1, 1]
private noncomputable def θc : Fin 1 → ℝ := fun _ => 3 / 5

-- (c) `Xc` has entries `1, 2`.
example : Xc 0 0 = 1 ∧ Xc 1 0 = 2 := by
  constructor
  · simp only [Xc, Matrix.cons_val_zero]
  · simp only [Xc, Matrix.cons_val_zero, Matrix.cons_val_one]

-- (c) Normal equations hold for `θ = 3/5`.
example : Xcᵀ *ᵥ (Xc *ᵥ θc) = Xcᵀ *ᵥ yc := by
  funext j
  fin_cases j
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Fin.sum_univ_two,
    Fin.sum_univ_one, Xc, yc, θc, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

-- (c) Without an intercept, the residual sum is `1/5 ≠ 0`.
example : ∑ k, (yc - Xc *ᵥ θc) k = 1 / 5 := by
  simp only [Fin.sum_univ_two]
  have h0 : (yc - Xc *ᵥ θc) 0 = 2 / 5 := by
    simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_one, Xc, yc, θc,
      Matrix.cons_val_zero]
    norm_num
  have h1 : (yc - Xc *ᵥ θc) 1 = -(1 / 5) := by
    simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_one, Xc, yc, θc,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  rw [h0, h1]
  norm_num

example : ∑ k, (yc - Xc *ᵥ θc) k ≠ 0 := by
  have h : ∑ k, (yc - Xc *ᵥ θc) k = 1 / 5 := by
    simp only [Fin.sum_univ_two]
    have h0 : (yc - Xc *ᵥ θc) 0 = 2 / 5 := by
      simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_one, Xc, yc, θc,
        Matrix.cons_val_zero]
      norm_num
    have h1 : (yc - Xc *ᵥ θc) 1 = -(1 / 5) := by
      simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_one, Xc, yc, θc,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      norm_num
    rw [h0, h1]
    norm_num
  rw [h]
  norm_num

end CSLibExtTest.MachineLearning.Regression.InterceptResidualsTests
