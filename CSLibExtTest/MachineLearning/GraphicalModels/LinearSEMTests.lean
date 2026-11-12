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
