/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.FlattenedStirlingTypeBWord

namespace MetaMathlibExt.typeBFlattenedWord_mem_flattenedStirling

-- At order zero the partition of {0} gives the word 1 1 of order one.
example : IsStirlingPermutation 1 ![1, 1] ∧ IsFlattenedWord ![1, 1] := by
  let P := Finpartition.indiscrete (a := Finset.Icc (-((0 : ℕ) : ℤ)) (0 : ℕ)) (by decide)
  have word : typeBFlattenedWord P = ![1, 1] := by
    have hz : typeBShift ((P.part 0).filter (0 ≤ ·)) = {1} := by decide
    have hlabels : adlerBlockLabels P = ∅ := by decide
    unfold typeBFlattenedWord
    simp only [typeBFlattenedWordList, hz, hlabels, wrappedWord_singleton,
      Finset.sort_empty, List.flatMap_nil, List.append_nil]
    decide
  rw [← word]
  exact typeBFlattenedWord_mem_flattenedStirling P (isTypeBSetPartition_indiscrete 0)

-- The zero block wraps 6, the first labelled block doubles 5, and the second wraps 4.
private def partition : Finpartition (Finset.Icc (-((5 : ℕ) : ℤ)) (5 : ℕ)) where
  parts := {{0, -5, 5}, {1, -4}, {-1, 4}, {2, 3}, {-2, -3}}
  supIndep := by
    rw [Finset.supIndep_iff_disjoint_erase]
    decide
  sup_parts := by decide
  bot_notMem := by decide

private theorem typeB : IsTypeBSetPartition partition := by
  refine ⟨by decide, {0, -5, 5}, ⟨by decide, by decide⟩, ?_⟩
  rintro b ⟨hb, hneg⟩
  simp only [partition, Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl
  · rfl
  all_goals revert hneg; decide

private theorem sort_eq {α : Type*} [LinearOrder α] (s : Finset α) (xs : List α)
    (h : s = xs.toFinset) (hs : xs.SortedLT) : s.sort (· ≤ ·) = xs := by
  apply s.sortedLT_sort.eq_of_mem_iff hs
  simp [h]

-- The descents land on 1, 2 and 3, so the first two runs have the same leader.
example : IsStirlingPermutation 6 ![1, 6, 6, 1, 5, 5, 2, 2, 3, 4, 4, 3] ∧
    IsFlattenedWord ![1, 6, 6, 1, 5, 5, 2, 2, 3, 4, 4, 3] := by
  have word : typeBFlattenedWord partition = ![1, 6, 6, 1, 5, 5, 2, 2, 3, 4, 4, 3] := by
    have labels := sort_eq (adlerBlockLabels partition) [1, 2] (by decide) (by decide)
    unfold typeBFlattenedWord
    simp only [typeBFlattenedWordList, labels, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, doubledWord, wrappedWord]
    rw [sort_eq _ [1, 6] (by decide) (by decide), sort_eq _ [5] (by decide) (by decide),
      sort_eq _ [2] (by decide) (by decide), sort_eq _ [] (by decide) (by decide),
      sort_eq _ [3, 4] (by decide) (by decide)]
    decide
  rw [← word]
  exact typeBFlattenedWord_mem_flattenedStirling partition typeB

end MetaMathlibExt.typeBFlattenedWord_mem_flattenedStirling
