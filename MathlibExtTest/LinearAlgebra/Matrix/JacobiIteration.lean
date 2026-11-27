/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.LinearAlgebra.Matrix.JacobiIteration
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

/-! # Tests for `MathlibExt.LinearAlgebra.Matrix.JacobiIteration` -/

namespace MathlibExtTest.LinearAlgebra.Matrix.JacobiIteration

open MathlibExt.LinearAlgebra.Matrix.JacobiIterationWanted

-- Test section: the strictly diagonally dominant system `2x + y = 3`, `x + 3y = 4`. The Jacobi
-- iterates converge to a solution, and that solution is `(1, 1)`.
example : ∃ xStar : Fin 2 → ℝ, xStar = ![1, 1] ∧ ∀ x₀ : Fin 2 → ℝ,
    Filter.Tendsto
      (fun k ↦ (fun x : Fin 2 → ℝ ↦ fun i ↦
        (![3, 4] i - ∑ j ∈ Finset.univ.erase i, !![2, 1; 1, 3] i j * x j) /
          !![2, 1; 1, 3] i i)^[k] x₀)
      Filter.atTop (nhds xStar) := by
  obtain ⟨xStar, hsol, hconv⟩ := jacobi_iteration_converges !![(2 : ℝ), 1; 1, 3] ![3, 4]
    (fun i ↦ by fin_cases i <;> simp [Finset.sum_erase_eq_sub, Fin.sum_univ_two])
  refine ⟨xStar, ?_, hconv⟩
  have h0 := congr_fun hsol 0
  have h1 := congr_fun hsol 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
  ext i
  fin_cases i <;> simp <;> linarith

-- Test section: an empty system, where diagonal dominance holds vacuously.
example (A : Matrix (Fin 0) (Fin 0) ℝ) (b : Fin 0 → ℝ) :
    ∃ xStar : Fin 0 → ℝ, A.mulVec xStar = b ∧ ∀ x₀ : Fin 0 → ℝ,
      Filter.Tendsto
        (fun k ↦ (fun x : Fin 0 → ℝ ↦ fun i ↦
          (b i - ∑ j ∈ Finset.univ.erase i, A i j * x j) / A i i)^[k] x₀)
        Filter.atTop (nhds xStar) :=
  jacobi_iteration_converges A b fun i ↦ i.elim0

end MathlibExtTest.LinearAlgebra.Matrix.JacobiIteration
