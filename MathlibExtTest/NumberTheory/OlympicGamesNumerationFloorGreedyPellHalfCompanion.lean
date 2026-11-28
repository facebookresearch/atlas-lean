/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.OlympicGamesNumerationFloorGreedyPellHalfCompanion
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith

/-!
# Tests for the greedy Pell floor identity

Compute both alternating recurrences at their first indices and the floor and shifted sum for
concrete greedy inputs, including the empty sum and maximal digits at both parities.
-/

namespace MathlibExtTest.NumberTheory.OlympicGamesNumerationFloorGreedyPellHalfCompanion

open Finset MetaMathlibExt

private def inputWeight (k : ℕ) : ℕ :=
  if k % 2 = 1 then pellNumber k else pellLucasSequence k

private def outputWeight (k : ℕ) : ℕ :=
  if k % 2 = 1 then pellLucasSequence k else pellNumber k

example : inputWeight 2 + inputWeight 0 = 4 * inputWeight 1 ∧
    inputWeight 3 + inputWeight 1 = 2 * inputWeight 2 := by decide

private theorem sqrt_two_bounds : (1414 : ℝ) / 1000 < Real.sqrt 2 ∧
    Real.sqrt 2 < (1415 : ℝ) / 1000 :=
  ⟨(Real.lt_sqrt (by norm_num)).mpr (by norm_num),
    (Real.sqrt_lt (by norm_num) (by norm_num)).mpr (by norm_num)⟩

example (a : ℕ → ℕ) :
    ⌊((∑ k ∈ Icc 1 0, a k * inputWeight k : ℕ) : ℝ) * (1 + Real.sqrt 2)⌋₊ = 0 ∧
      (∑ k ∈ Icc 1 0, a k * outputWeight (k + 1)) = 0 := by simp

private def digitsFour (k : ℕ) : ℕ := [0, 1, 1].getD k 0

private theorem digitsFour_greedy (m : ℕ) (hm : 1 ≤ m) (hm' : m ≤ 3) :
    ∑ k ∈ Ico 1 m, digitsFour k * inputWeight k < inputWeight m := by
  interval_cases m <;> decide

-- The even-indexed weight 3 is used once, and the lower prefix contributes 1.
example :
    (∀ m, 1 ≤ m → m ≤ 3 → ∑ k ∈ Ico 1 m, digitsFour k * inputWeight k < inputWeight m) ∧
      ⌊((∑ k ∈ Icc 1 2, digitsFour k * inputWeight k : ℕ) : ℝ) * (1 + Real.sqrt 2)⌋₊ = 9 ∧
      (∑ k ∈ Icc 1 2, digitsFour k * outputWeight (k + 1)) = 9 := by
  have hsum : (∑ k ∈ Icc 1 2, digitsFour k * inputWeight k) = 4 := by decide
  refine ⟨digitsFour_greedy, ?_, by decide⟩
  rw [hsum, Nat.floor_eq_iff (by positivity)]
  constructor <;> norm_num <;> linarith only [sqrt_two_bounds.1, sqrt_two_bounds.2]

private def digitsSixteen (k : ℕ) : ℕ := [0, 1, 0, 3].getD k 0

-- Three copies of 5 fit with one copy of 1, but a second copy hits the strict cutoff at 17.
example :
    (∀ m, 1 ≤ m → m ≤ 4 → ∑ k ∈ Ico 1 m, digitsSixteen k * inputWeight k < inputWeight m) ∧
      (∑ k ∈ Icc 1 3, digitsSixteen k * inputWeight k) + inputWeight 1 = inputWeight 4 ∧
      ⌊((∑ k ∈ Icc 1 3, digitsSixteen k * inputWeight k : ℕ) : ℝ) * (1 + Real.sqrt 2)⌋₊ = 38 ∧
      (∑ k ∈ Icc 1 3, digitsSixteen k * outputWeight (k + 1)) = 38 := by
  refine ⟨?_, by decide, ?_, by decide⟩
  · intro m hm hm'
    interval_cases m <;> decide
  · have hsum : (∑ k ∈ Icc 1 3, digitsSixteen k * inputWeight k) = 16 := by decide
    rw [hsum, Nat.floor_eq_iff (by positivity)]
    constructor <;> norm_num <;> linarith only [sqrt_two_bounds.1, sqrt_two_bounds.2]

-- Client example: the same floor rule applies with a leading zero.
example : ⌊(4 : ℝ) * (1 + Real.sqrt 2)⌋₊ = 9 := by
  have h := floor_greedy_pell_halfCompanion_sum_mul_one_add_sqrt_two inputWeight outputWeight
    (fun _ ↦ rfl) (fun _ ↦ rfl) 3 digitsFour (by intro m hm hm'; interval_cases m <;> decide)
  have hin : (∑ k ∈ Icc 1 3, digitsFour k * inputWeight k) = 4 := by decide
  have hout : (∑ k ∈ Icc 1 3, digitsFour k * outputWeight (k + 1)) = 9 := by decide
  simpa only [hin, hout, Nat.cast_ofNat] using h

end MathlibExtTest.NumberTheory.OlympicGamesNumerationFloorGreedyPellHalfCompanion
