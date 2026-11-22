/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.ZeroSumBestResponse
import Mathlib.Tactic

/-!
# Tests for `MathlibExt.GameTheory.ZeroSumBestResponse`

In the game `!![1, 0; 0, 2]`, column `1` pays `0` to row `0` and `2` to row `1`, and the even
column mix pays `1/2` and `1`. In both cases the pure best response produced by
`exists_pure_best_response` must be row `1`, and that single row bounds every mixed row strategy.
-/

@[expose] public section

namespace MathlibExtTest.GameTheory.ZeroSumBestResponse

open Matrix Convexity MathlibExt.GameTheory.ZeroSumBestResponse

/-- The payoff matrix of the examples. -/
abbrev A : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 2]

/-- The even mix of the two columns. -/
noncomputable def evenCols : StdSimplex ℝ (Fin 2) :=
  StdSimplex.duple 0 1 (s := 1 / 2) (t := 1 / 2) (by norm_num) (by norm_num) (by norm_num)

/-- Row payoffs against column `1`. -/
theorem A_mulVec_col1 : A *ᵥ (StdSimplex.single (R := ℝ) (1 : Fin 2)).weights = ![0, 2] := by
  ext i
  fin_cases i <;>
    simp [A, StdSimplex.single, Finsupp.single_eq_pi_single, mulVec, dotProduct, Fin.sum_univ_two]

/-- Row payoffs against the even column mix. -/
theorem A_mulVec_evenCols : A *ᵥ evenCols.weights = ![1 / 2, 1] := by
  ext i
  fin_cases i <;>
    simp [A, evenCols, Finsupp.single_eq_pi_single, mulVec, dotProduct, Fin.sum_univ_two]

/-- Against column `1`, the pure best response is row `1`. -/
example : ∃ i : Fin 2, i = 1 ∧ ∀ p : StdSimplex ℝ (Fin 2),
    p.weights ⬝ᵥ (A *ᵥ (StdSimplex.single (R := ℝ) 1).weights) ≤
      (StdSimplex.single (R := ℝ) i).weights ⬝ᵥ
        (A *ᵥ (StdSimplex.single (R := ℝ) 1).weights) := by
  obtain ⟨i, hi⟩ := exists_pure_best_response A (StdSimplex.single (R := ℝ) (1 : Fin 2))
  refine ⟨i, ?_, hi⟩
  have h := hi (StdSimplex.single (R := ℝ) 1)
  rw [single_weights_dotProduct, single_weights_dotProduct, A_mulVec_col1] at h
  fin_cases i
  · norm_num at h
  · rfl

/-- One pure row bounds every mixed row strategy against column `1` by `2`. -/
example (p : StdSimplex ℝ (Fin 2)) :
    p.weights ⬝ᵥ (A *ᵥ (StdSimplex.single (R := ℝ) 1).weights) ≤ 2 := by
  obtain ⟨i, hi⟩ := exists_pure_best_response A (StdSimplex.single (R := ℝ) (1 : Fin 2))
  refine (hi p).trans ?_
  rw [single_weights_dotProduct, A_mulVec_col1]
  fin_cases i <;> norm_num

/-- Against the even column mix, the pure best response is row `1`, and it bounds every mixed row
strategy by `1`. -/
example : ∃ i : Fin 2, i = 1 ∧ ∀ p : StdSimplex ℝ (Fin 2),
    p.weights ⬝ᵥ (A *ᵥ evenCols.weights) ≤ 1 := by
  obtain ⟨i, hi⟩ := exists_pure_best_response A evenCols
  have h := hi (StdSimplex.single (R := ℝ) 1)
  rw [single_weights_dotProduct, single_weights_dotProduct, A_mulVec_evenCols] at h
  have hi1 : i = 1 := by
    fin_cases i
    · norm_num at h
    · rfl
  subst hi1
  refine ⟨1, rfl, fun p => (hi p).trans ?_⟩
  rw [single_weights_dotProduct, A_mulVec_evenCols]
  norm_num

end MathlibExtTest.GameTheory.ZeroSumBestResponse

end
