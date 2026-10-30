/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Process.ContinuousTimeMarkovChain.RateMatrix
public import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Linarith

/-!
# Tests for rate matrices

A two-state rate matrix as the non-vacuity witness for `IsRateMatrix`, the zero matrix as the
boundary case, a matrix that is not a rate matrix, the diagonal identity, `Q *ᵥ 1 = 0`, and
the uniformization shift at the smallest admissible constant.
-/

@[expose] public section

open Finset Matrix ProbabilityTheory

namespace MathlibExtTest.Probability.Process.ContinuousTimeMarkovChain.RateMatrix

/-- A two-state rate matrix: rate `1` from state `0` to `1`, rate `2` back. -/
def q2 : Matrix (Fin 2) (Fin 2) ℝ := !![-1, 1; 2, -2]

-- Non-vacuity witness: `q2` is a rate matrix.
theorem isRateMatrix_q2 : IsRateMatrix q2 where
  nonneg_of_ne i j h := by fin_cases i <;> fin_cases j <;> simp_all [q2]
  sum_row i := by fin_cases i <;> simp [q2, Fin.sum_univ_two]

-- Boundary case: the zero matrix is a rate matrix (the constant chain).
example : IsRateMatrix (0 : Matrix (Fin 3) (Fin 3) ℝ) :=
  ⟨fun _ _ _ => le_rfl, fun _ => by simp⟩

-- A matrix with a negative off-diagonal entry is not a rate matrix.
example : ¬ IsRateMatrix (!![1, -1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) := fun h => by
  have : (0 : ℝ) ≤ -1 := h.nonneg_of_ne (i := 0) (j := 1) (by decide)
  linarith

-- The diagonal is minus the off-diagonal row sum, and is nonpositive.
example : q2 1 1 = -∑ j ∈ univ.erase 1, q2 1 j := isRateMatrix_q2.diag_eq 1
example : q2 0 0 ≤ 0 := isRateMatrix_q2.diag_nonpos 0

-- The constant vector is in the kernel.
example : q2 *ᵥ 1 = 0 := isRateMatrix_q2.mulVec_one

-- Uniformization at `c = 2 = max (-q2 i i)`: `q2 + 2 • 1 = !![1, 1; 2, 0] ≥ 0`.
example (i j : Fin 2) : 0 ≤ (q2 + (2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j :=
  isRateMatrix_q2.add_smul_one_nonneg (fun i => by fin_cases i <;> norm_num [q2]) i j
example : ∃ c : ℝ, 0 ≤ c ∧ ∀ i j, 0 ≤ (q2 + c • (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j :=
  isRateMatrix_q2.exists_add_smul_one_nonneg

#print axioms IsRateMatrix.add_smul_one_nonneg
#print axioms IsRateMatrix.exists_add_smul_one_nonneg

end MathlibExtTest.Probability.Process.ContinuousTimeMarkovChain.RateMatrix
