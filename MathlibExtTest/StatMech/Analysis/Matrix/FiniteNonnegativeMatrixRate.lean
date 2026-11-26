/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Matrix.FiniteNonnegativeMatrixRate

/-!
# Tests for `MathlibExt.Analysis.Matrix.FiniteNonnegativeMatrixRate`

* `MatrixPositiveReachable` for the identity matrix (diagonal entries only).
* `exists_matrixCoefficient_log_div_tendsto_of_nonnegative` for the all-ones `2 × 2` matrix and
  for `2 • 1`, with `f = 1`.
-/

@[expose] public section

open StatMech Matrix Filter

namespace MathlibExtTest.StatMech.Analysis.Matrix.FiniteNonnegativeMatrixRate

example : MatrixPositiveReachable (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0 := ⟨0, by simp⟩

example : ∃ rate : ℝ, Tendsto (fun n : ℕ =>
    Real.log ((((Matrix.of fun _ _ => (1 : ℝ) : Matrix (Fin 2) (Fin 2) ℝ) ^ n) *ᵥ
      (fun _ : Fin 2 => (1 : ℝ))) 0) / (n : ℝ))
    atTop (nhds rate) :=
  exists_matrixCoefficient_log_div_tendsto_of_nonnegative _ (fun _ _ => zero_le_one)
    (fun _ => one_pos) _ (fun _ => one_pos) 0

example : ∃ rate : ℝ, Tendsto (fun n : ℕ =>
    Real.log ((((2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) ^ n *ᵥ (fun _ => (1 : ℝ))) 1) / (n : ℝ))
    atTop (nhds rate) :=
  exists_matrixCoefficient_log_div_tendsto_of_nonnegative _
    (fun i j => by by_cases h : i = j <;> simp [h])
    (fun i => by simp) _ (fun _ => one_pos) 1

end MathlibExtTest.StatMech.Analysis.Matrix.FiniteNonnegativeMatrixRate
