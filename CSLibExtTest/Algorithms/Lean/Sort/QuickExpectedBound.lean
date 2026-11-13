/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

-- Anonymous examples and axiom checks need this import even without retained declarations.
import CSLibExt.Algorithms.Lean.Sort.QuickExpectedBound -- shake: keep
import all CSLibExt.Algorithms.Lean.Sort.QuickExpected

/-!
# Consumers and boundary checks for quicksort's expected comparison bounds

The exact rational checks below are independent of the new inequalities. The negative
case records why duplicate lists cannot use the inherited pair-set formula. Ideal-shuffle
consumers use a fixed array through its size-indexed vector, not an assumed uniform law.
-/

open Cslib.Algorithms.Lean.TimeM
open scoped ENNReal

-- The actual expectation, not only a bound, vanishes at the two small boundaries.
example : (expectedTime (quickSort (α := ℕ)) (uniformPermutation [])).toReal = 0 := by
  rw [quickSort_expectedTime_uniformPermutation_toReal _ (by decide)]
  simp

example : (expectedTime (quickSort (α := ℕ)) (uniformPermutation [7])).toReal = 0 := by
  rw [quickSort_expectedTime_uniformPermutation_toReal _ (by decide)]
  norm_num [Finset.sum_filter]

example : (expectedTime (quickSort (α := ℕ)) (uniformPermutation [9, 2])).toReal = 1 := by
  rw [quickSort_expectedTime_uniformPermutation_toReal _ (by decide)]
  have hp : (([9, 2] : List ℕ).toFinset ×ˢ ([9, 2] : List ℕ).toFinset).filter
      (fun p => p.1 < p.2) = {(2, 9)} := by decide
  rw [hp]
  norm_num [betweenCount]

example : (expectedTime (quickSort (α := ℕ))
    (uniformPermutation [30, 10, 20])).toReal = 8 / 3 := by
  rw [quickSort_expectedTime_uniformPermutation_toReal _ (by decide)]
  have hp : (([30, 10, 20] : List ℕ).toFinset ×ˢ
      ([30, 10, 20] : List ℕ).toFinset).filter (fun p => p.1 < p.2) =
      {(10, 20), (10, 30), (20, 30)} := by decide
  rw [hp]
  norm_num [betweenCount]

-- Independently execute the cost model on all six input orderings.
example : ([[10, 20, 30], [10, 30, 20], [20, 10, 30], [20, 30, 10],
    [30, 10, 20], [30, 20, 10]] : List (List ℕ)).map (fun xs => (quickSort xs).time) =
    [3, 3, 2, 2, 3, 3] := by decide

-- Actual final theorem applications, including a nontrivial positive sample.
example : (expectedTime (quickSort (α := ℕ)) (uniformPermutation [])).toReal ≤ 0 := by
  simpa using quickSort_expectedTime_le_harmonic ([] : List ℕ) (by decide)

example : (expectedTime (quickSort (α := ℕ)) (uniformPermutation [7])).toReal ≤ 2 := by
  simpa [harmonic] using quickSort_expectedTime_le_log ([7] : List ℕ) (by decide)

example : (expectedTime (quickSort (α := ℕ))
    (uniformPermutation [4, 1, 3, 2])).toReal ≤ 2 * 4 * (harmonic 4 : ℝ) := by
  simpa using quickSort_expectedTime_le_harmonic ([4, 1, 3, 2] : List ℕ) (by decide)

example : (expectedTime (quickSort (α := ℕ))
    (uniformPermutation [9, 2])).toReal ≤ 6 * 2 * Real.log 2 := by
  simpa using quickSort_expectedTime_le_mul_log ([9, 2] : List ℕ) (by decide) (by decide)

-- The finiteness theorem is stronger than the Nodup-bound interface.
example : expectedTime (quickSort (α := ℕ)) (uniformPermutation [1, 1, 2]) ≠ ⊤ :=
  quickSort_expectedTime_uniformPermutation_ne_top _

example : ¬ ([1, 1, 2] : List ℕ).Nodup := by decide

example : True := by
  fail_if_success have := quickSort_expectedTime_le_harmonic ([1, 1, 2] : List ℕ) (by decide)
  trivial

-- n≥2 is not silently solved for a singleton when using the pure n log n API.
example : True := by
  fail_if_success have := quickSort_expectedTime_le_mul_log ([7] : List ℕ) (by decide) (by decide)
  trivial

-- Canonical asymptotic consumer: no assumed expectation bound.
example : (fun n => (expectedTime (quickSort (α := ℕ))
      (uniformPermutation (List.range n))).toReal)
    =O[Filter.atTop] (fun n => (n : ℝ) * Real.log n) :=
  quickSort_expectedTime_isBigO List.range (fun _ => List.nodup_range) (fun _ => List.length_range)

-- Fixed-array Fisher–Yates consumers, with actual output law and no shuffle-cost claim.
example : (expectedTime (quickSort (α := ℕ))
    ((randomlyPermuteDistribution (#[3, 1, 2] : Array ℕ).toVector).map
      (fun r => r.ret.toList))).toReal ≤ 2 * 3 * (harmonic 3 : ℝ) := by
  exact quickSort_expectedTime_randomlyPermute_le_harmonic _ (by decide)

example : (expectedTime (quickSort (α := ℕ))
    ((randomlyPermuteDistribution (#[3, 1, 2] : Array ℕ).toVector).map
      (fun r => r.ret.toList))).toReal ≤ 2 * 3 * (1 + Real.log 3) := by
  exact quickSort_expectedTime_randomlyPermute_le_log _ (by decide)

example : (expectedTime (quickSort (α := ℕ))
    ((randomlyPermuteDistribution (#[] : Array ℕ).toVector).map
      (fun r => r.ret.toList))).toReal ≤ 0 := by
  simpa using quickSort_expectedTime_randomlyPermute_le_log
    (#[] : Array ℕ).toVector (by decide)

example : expectedTime (quickSort (α := ℕ))
    ((randomlyPermuteDistribution (#[3, 1, 2] : Array ℕ).toVector).map
      (fun r => r.ret.toList)) ≠ ⊤ :=
  quickSort_expectedTime_randomlyPermute_ne_top _

#print axioms quickSort_expectedTime_uniformPermutation_ne_top
#print axioms quickSort_expectedTime_le_harmonic
#print axioms quickSort_expectedTime_le_log
#print axioms quickSort_expectedTime_le_mul_log
#print axioms quickSort_expectedTime_isBigO
#print axioms quickSort_expectedTime_randomlyPermute_ne_top
#print axioms quickSort_expectedTime_randomlyPermute_le_harmonic
#print axioms quickSort_expectedTime_randomlyPermute_le_log
