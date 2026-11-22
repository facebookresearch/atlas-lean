/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import all CSLibExt.Algorithms.Lean.Sort.QuickExpected

/-!
# Tests for the expected comparison count of quicksort

Concrete expected comparison counts for `quickSort` on uniformly
random orderings of `[1, 2]`, `[1, 2, 3]`, and `[1, 2, 3, 4]`, obtained
from the pair-sum formula `∑_{a < b} 2 / (d_{a,b} + 2)`, plus a direct
enumeration of all six orderings of `[1, 2, 3]` by `decide`,
independent of the general proof.
-/

open Cslib.Algorithms.Lean.TimeM
open scoped ENNReal

/-- Quicksort on a random ordering of `[1, 2]` uses `1` comparison in
expectation: the single pair has `d = 0` and contributes `2 / 2`. -/
example : expectedTime (quickSort (α := ℕ))
    (uniformPermutation ([1, 2] : List ℕ)) = 1 := by
  rw [quickSort_expectedTime_uniformPermutation _ (by decide)]
  have hfin : (([1, 2] : List ℕ).toFinset ×ˢ
        ([1, 2] : List ℕ).toFinset).filter (fun p => p.1 < p.2) =
      {(1, 2)} := by
    decide
  rw [hfin, Finset.sum_singleton]
  have hbc : betweenCount ([1, 2] : List ℕ) 1 2 = 0 := by
    decide
  rw [hbc]
  simp
  exact ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top

/-- Quicksort on a random ordering of `[1, 2, 3]` uses `8 / 3`
comparisons in expectation: the pairs contribute `2 / 2 + 2 / 3 +
2 / 2`. -/
example : (expectedTime (quickSort (α := ℕ))
    (uniformPermutation ([1, 2, 3] : List ℕ))).toReal = 8 / 3 := by
  rw [quickSort_expectedTime_uniformPermutation_toReal _ (by decide)]
  have hfin : (([1, 2, 3] : List ℕ).toFinset ×ˢ
        ([1, 2, 3] : List ℕ).toFinset).filter (fun p => p.1 < p.2) =
      {(1, 2), (1, 3), (2, 3)} := by
    decide
  rw [hfin]
  norm_num [Finset.sum_insert, Finset.sum_singleton, betweenCount]

/-- Direct enumeration, independent of the pair-sum formula: over the
six orderings of `[1, 2, 3]`, the comparison counts total `16`, and
`16 / 6 = 8 / 3`. -/
example : (∑ σ : Equiv.Perm (Fin 3),
    (quickSort
      (List.ofFn (fun p => ([1, 2, 3] : List ℕ).get (σ p)))).time) =
    16 := by
  decide

/-- Quicksort on a random ordering of `[1, 2, 3, 4]` uses `29 / 6`
comparisons in expectation: by distance, three pairs contribute
`2 / 2`, two contribute `2 / 3`, and one contributes `2 / 4`, totalling
`3 + 4 / 3 + 1 / 2`. -/
example : (expectedTime (quickSort (α := ℕ))
    (uniformPermutation ([1, 2, 3, 4] : List ℕ))).toReal = 29 / 6 := by
  rw [quickSort_expectedTime_uniformPermutation_toReal _ (by decide)]
  have hfin : (([1, 2, 3, 4] : List ℕ).toFinset ×ˢ
        ([1, 2, 3, 4] : List ℕ).toFinset).filter
        (fun p => p.1 < p.2) =
      {(1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)} := by
    decide
  rw [hfin]
  norm_num [Finset.sum_insert, Finset.sum_singleton, betweenCount]

#print axioms
  Cslib.Algorithms.Lean.TimeM.quickSort_expectedTime_uniformPermutation
#print axioms
  Cslib.Algorithms.Lean.TimeM.quickSort_expectedTime_uniformPermutation_toReal
