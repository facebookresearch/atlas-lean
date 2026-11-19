/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.LinearSEM
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring

/-!
# Tests for interventions in linear structural equation models

The two-node chain `X_0 = e_0`, `X_1 = 3 X_0 + e_1` (`B = !![0, 0; 3, 0]`):

* `do(X_0 = 2)` gives `X_1 = 6 + e_1`;
* `do(X_1 = 5)` leaves the upstream node `X_0 = e_0` unchanged.

Invertibility of `1 - B` for a strictly lower triangular `3 × 3` matrix, the unique solution of
its structural equations, and the singular boundary case with a nonzero diagonal.
-/

@[expose] public section

namespace Cslib.MachineLearning.LinearSEMTests

open Cslib.MachineLearning.GraphicalModels.LinearSEM in
example (e : Fin 2 → ℝ) :
    doSolve (!![0, 0; 3, 0] : Matrix (Fin 2) (Fin 2) ℝ) 0 2 e 1 = 6 + e 1 := by
  have hB : ∀ i j : Fin 2, i ≤ j → (!![0, 0; 3, 0] : Matrix (Fin 2) (Fin 2) ℝ) i j = 0 := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have hx := (eq_doSolve_iff hB 0 2 e _).mpr rfl
  obtain ⟨h0, hrest⟩ := hx
  have h1 := hrest 1 (by decide)
  have e10 : (!![0, 0; 3, 0] : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 3 := rfl
  have e11 : (!![0, 0; 3, 0] : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = 0 := rfl
  rw [h1, Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two, e10, e11, h0]
  ring

open Cslib.MachineLearning.GraphicalModels.LinearSEM in
example (e : Fin 2 → ℝ) :
    doSolve (!![0, 0; 3, 0] : Matrix (Fin 2) (Fin 2) ℝ) 1 5 e 0 = e 0 := by
  have hB : ∀ i j : Fin 2, i ≤ j → (!![0, 0; 3, 0] : Matrix (Fin 2) (Fin 2) ℝ) i j = 0 := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have hx := (eq_doSolve_iff hB 1 5 e _).mpr rfl
  obtain ⟨h1, hrest⟩ := hx
  have h0 := hrest 0 (by decide)
  have e00 : (!![0, 0; 3, 0] : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = 0 := rfl
  have e01 : (!![0, 0; 3, 0] : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = 0 := rfl
  rw [h0, Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two, e00, e01]
  ring

end Cslib.MachineLearning.LinearSEMTests

namespace Cslib.MachineLearning.LinearSEMInvertibilityTests

open Cslib.MachineLearning.GraphicalModels.LinearSEM Matrix

/-- Test matrix: strictly lower triangular 3×3. -/
def B₃ : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, 0; 2, 0, 0; 3, -1, 0]

theorem B₃_strict : ∀ i j : Fin 3, i ≤ j → B₃ i j = 0 := by
  intro i j
  fin_cases i <;> fin_cases j <;> intro hij
  · rfl
  · rfl
  · rfl
  · exact absurd hij (by decide)
  · rfl
  · rfl
  · exact absurd hij (by decide)
  · exact absurd hij (by decide)
  · rfl

example : (1 - B₃).det = 1 := det_one_sub_eq_one B₃_strict

example : IsUnit (1 - B₃) := isUnit_one_sub B₃_strict

example : solve B₃ ![1, 1, 1] = ![1, 3, 1] := by
  have hcheck : (![1, 3, 1] : Fin 3 → ℝ) = B₃ *ᵥ ![1, 3, 1] + ![1, 1, 1] := by
    funext i
    fin_cases i <;> simp [B₃]; ring
  exact ((eq_solve_iff B₃_strict _ _).mp hcheck).symm

example : (1 - (1 : Matrix (Fin 1) (Fin 1) ℝ)).det = 0 := by
  rw [Matrix.det_fin_one]
  simp

example : ¬ IsUnit (1 - (1 : Matrix (Fin 1) (Fin 1) ℝ)) := by
  intro h
  rw [sub_self, Matrix.isUnit_iff_isUnit_det, Matrix.det_fin_one] at h
  simp at h

end Cslib.MachineLearning.LinearSEMInvertibilityTests
