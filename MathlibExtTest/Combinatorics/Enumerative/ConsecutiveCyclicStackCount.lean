/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.ConsecutiveCyclicStackCount
import Mathlib.Data.List.Permutation

open MetaMathlibExt

-- At length two the tail is a singleton, so it gives only one choice.
example : (sortedPermutations (consecutiveCyclicStackSort [3, 2, 1]) 2).card = 1 :=
  card_sortedPermutations_consecutiveCyclicStackSort_321 (n := 2) (by decide)

-- At length four both endpoint choices occur twice. An interior second entry cannot sort.
example : sortedPermutations (consecutiveCyclicStackSort [3, 2, 1]) 4 =
    {[4, 1, 2, 3], [4, 1, 3, 2], [4, 3, 1, 2], [4, 3, 2, 1]} := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff, sortedPermutations,
      Finset.mem_filter, List.mem_toFinset, List.mem_permutations]
    decide
  · rw [card_sortedPermutations_consecutiveCyclicStackSort_321 (by decide)]
    decide

-- The smallest admissible size gives a sorted permutation with a singleton tail.
example : ([2, 1] : List ℕ).head? = some 2 ∧ IsGoodSeq [1] :=
  head_tail_of_mem_sortedPermutations_consecutiveCyclicStackSort_321
    (n := 2) (π := [2, 1]) (by decide) (by
      simp only [sortedPermutations, Finset.mem_filter, List.mem_toFinset, List.mem_permutations]
      decide)

-- The maximum comes first, but 2 lies strictly between the two later entries.
example : [4, 2, 1, 3] ∉ sortedPermutations (consecutiveCyclicStackSort [3, 2, 1]) 4 := by
  intro h
  have hg := (head_tail_of_mem_sortedPermutations_consecutiveCyclicStackSort_321 (by decide) h).2
  exact (by decide : ¬ IsGoodSeq [2, 1, 3]) hg
