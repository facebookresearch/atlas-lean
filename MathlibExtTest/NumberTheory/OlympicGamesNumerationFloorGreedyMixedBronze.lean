/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.OlympicGamesNumerationFloorGreedyMixedBronze
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Tests for the mixed bronze floor identity

Checks the three classes of input and shifted output weights, and evaluates concrete floors
from rational square-root bounds independently of the theorem. The multi-block tests cover
a prefix at the cutoff and a four-digit block with a nonzero prefix below the cutoff.
-/

namespace MathlibExtTest.NumberTheory.OlympicGamesNumerationFloorGreedyMixedBronze

open Finset MetaMathlibExt

local notation "β" => (((5 + Real.sqrt 13) / 6) : ℝ)

private def inputWeight (k : ℕ) : ℤ :=
  if k % 3 = 0 then bronzeCompanionSecond (2 * (k / 3))
  else if k % 3 = 1 then 3 * lucasU bronzeLucasParams (2 * (k / 3) + 1)
  else lucasU bronzeLucasParams (2 * (k / 3) + 1) + bronzeCompanionFirst (2 * (k / 3) + 2)

private def outputWeight (k : ℕ) : ℤ :=
  if k % 3 = 0 then bronzeCompanionSecond (2 * (k / 3))
  else if k % 3 = 1 then lucasU bronzeLucasParams (2 * (k / 3) + 1)
  else bronzeCompanionFirst (2 * (k / 3) + 2)

example : (List.range 7).map inputWeight = [1, 3, 5, 7, 30, 53, 76] ∧
    (List.range 6).map (fun k => outputWeight (k + 1)) = [1, 4, 7, 10, 43, 76] := by
  decide

private theorem sqrt13_bounds : (3605 : ℝ) / 1000 < Real.sqrt 13 ∧
    Real.sqrt 13 < (3606 : ℝ) / 1000 := by
  exact ⟨(Real.lt_sqrt (by norm_num)).mpr (by norm_num),
    (Real.sqrt_lt (by norm_num) (by norm_num)).mpr (by norm_num)⟩

-- Each residue class can contribute a nonzero digit; the all-zero sum is also allowed.
example : ⌊(0 : ℝ) * β⌋ = 0 ∧ ⌊(2 : ℝ) * β⌋ = 2 ∧ ⌊(3 : ℝ) * β⌋ = 4 ∧ ⌊(5 : ℝ) * β⌋ = 7 := by
  obtain ⟨hlo, hhi⟩ := sqrt13_bounds
  refine ⟨by simp, ?_, ?_, ?_⟩ <;>
    apply Int.floor_eq_iff.mpr <;> constructor <;> norm_num <;> linarith only [hlo, hhi]

-- This completed prefix is 23 = 2 * 10 + 3, exactly the second block's small-prefix cutoff.
example :
    let a (k : ℕ) : ℕ := [2, 0, 0, 3].getD k 0
    (∀ m ≤ 6, ∑ k ∈ range m, (a k : ℤ) * inputWeight k < inputWeight m) ∧
      ⌊((∑ k ∈ range 6, (a k : ℤ) * inputWeight k : ℤ) : ℝ) * β⌋ = 32 ∧
      (∑ k ∈ range 6, (a k : ℤ) * outputWeight (k + 1)) = 32 := by
  dsimp only
  refine ⟨?_, ?_, by decide⟩
  · intro m hm
    interval_cases m <;> decide
  · have hsum : (∑ k ∈ range 6, (([2, 0, 0, 3] : List ℕ).getD k 0 : ℤ) * inputWeight k) = 23 :=
      by decide
    rw [hsum, Int.floor_eq_iff]
    obtain ⟨hlo, hhi⟩ := sqrt13_bounds
    constructor <;> norm_num <;> linarith only [hlo, hhi]

private def fourDigitBlock (k : ℕ) : ℕ := [1, 0, 0, 4].getD k 0

private theorem fourDigitBlock_greedy (m : ℕ) (hm : m ≤ 6) :
    ∑ k ∈ range m, (fourDigitBlock k : ℤ) * inputWeight k < inputWeight m := by
  interval_cases m <;> decide

-- Four copies of 7 leave room for one copy of 1, but not two: 30 is the next weight.
example :
    (∑ k ∈ range 4, (([2, 0, 0, 4] : List ℕ).getD k 0 : ℤ) * inputWeight k) = inputWeight 4 := by
  decide

private theorem fourDigitBlock_input :
    (∑ k ∈ range 6, (fourDigitBlock k : ℤ) * inputWeight k) = 29 := by
  decide

example :
    ⌊((∑ k ∈ range 6, (fourDigitBlock k : ℤ) * inputWeight k : ℤ) : ℝ) * β⌋ = 41 ∧
      (∑ k ∈ range 6, (fourDigitBlock k : ℤ) * outputWeight (k + 1)) = 41 := by
  refine ⟨?_, by decide⟩
  rw [fourDigitBlock_input, Int.floor_eq_iff]
  obtain ⟨hlo, hhi⟩ := sqrt13_bounds
  constructor <;> norm_num <;> linarith only [hlo, hhi]

-- A client may use the same digits with two leading zeros in the last block.
example : ⌊(29 : ℝ) * β⌋ = 41 := by
  have h := floor_greedy_mixed_bronze_sum_mul inputWeight outputWeight
    (fun _ => rfl) (fun _ => rfl) 5 fourDigitBlock fourDigitBlock_greedy
  have hOut : (∑ k ∈ range 6, (fourDigitBlock k : ℤ) * outputWeight (k + 1)) = 41 := by decide
  rw [fourDigitBlock_input, hOut] at h
  exact_mod_cast h

end MathlibExtTest.NumberTheory.OlympicGamesNumerationFloorGreedyMixedBronze
