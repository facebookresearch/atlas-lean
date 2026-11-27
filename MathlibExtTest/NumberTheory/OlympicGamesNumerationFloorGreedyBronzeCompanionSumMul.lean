/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.OlympicGamesNumerationFloorGreedyBronzeCompanionSumMul
import Mathlib.Tactic.IntervalCases
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.NumberTheory.Rayleigh
import MathlibExt.NumberTheory.GreedyOddFibonacciFloor
import MathlibExt.NumberTheory.OddFibonacciGoldenRatio
import MathlibExt.NumberTheory.OddFibonacciRepresentation
import MathlibExt.NumberTheory.PellLucasSequence
import MathlibExt.NumberTheory.PellNumberSequence
import MathlibExt.NumberTheory.PellSilverRatio

/-!
# Tests for floors of greedy bronze sums

These examples apply the floor theorem to nonzero greedy digits in each of the three index
classes.

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Theorem 10 (1).
-/

namespace MathlibExtTest.NumberTheory.OlympicGamesNumerationFloorGreedyBronzeCompanionSumMul
public section

open Finset MetaMathlibExt
private def bronzeWeights (k : ℕ) : ℤ :=
  if k % 3 = 1 then lucasU bronzeLucasParams (2 * (k / 3) + 1)
  else if k % 3 = 2 then bronzeCompanionFirst (2 * (k / 3) + 2)
  else bronzeCompanionSecond (2 * (k / 3))
private def bronzeShiftedWeights (k : ℕ) : ℤ :=
  if k % 3 = 1 then bronzeCompanionSecond (2 * (k / 3) + 1)
  else if k % 3 = 2 then lucasU bronzeLucasParams (2 * (k / 3) + 2)
  else bronzeCompanionFirst (2 * (k / 3) + 1)
/-- The greedy digits consisting of three copies of the first weight give floor `9`. -/
theorem floor_three_mul : ⌊(3 : ℝ) * ((3 + Real.sqrt 13) / 2)⌋ = 9 := by
  have h := floor_greedy_bronze_companion_sum_mul bronzeWeights bronzeShiftedWeights
    (fun _ => rfl) (fun _ => rfl) 1 (fun k => if k = 1 then 3 else 0) (by
      intro m hm hm'
      interval_cases m <;> decide)
  change ⌊(3 : ℝ) * ((3 + Real.sqrt 13) / 2)⌋ = 9 at h
  exact h
/-- Two copies of the first weight and one of the second give floor `19`. -/
theorem floor_six_mul : ⌊(6 : ℝ) * ((3 + Real.sqrt 13) / 2)⌋ = 19 := by
  have h := floor_greedy_bronze_companion_sum_mul bronzeWeights bronzeShiftedWeights
    (fun _ => rfl) (fun _ => rfl) 2
    (fun k => if k = 1 then 2 else if k = 2 then 1 else 0) (by
      intro m hm hm'
      interval_cases m <;> decide)
  change ⌊(6 : ℝ) * ((3 + Real.sqrt 13) / 2)⌋ = 19 at h
  exact h
/-- Two copies of the first weight and one of the third give floor `29`. -/
theorem floor_nine_mul : ⌊(9 : ℝ) * ((3 + Real.sqrt 13) / 2)⌋ = 29 := by
  have h := floor_greedy_bronze_companion_sum_mul bronzeWeights bronzeShiftedWeights
    (fun _ => rfl) (fun _ => rfl) 3
    (fun k => if k = 1 then 2 else if k = 3 then 1 else 0) (by
      intro m hm hm'
      interval_cases m <;> decide)
  change ⌊(9 : ℝ) * ((3 + Real.sqrt 13) / 2)⌋ = 29 at h
  exact h
end

end MathlibExtTest.NumberTheory.OlympicGamesNumerationFloorGreedyBronzeCompanionSumMul
