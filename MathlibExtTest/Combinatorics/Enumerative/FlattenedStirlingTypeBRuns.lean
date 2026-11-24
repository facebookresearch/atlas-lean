/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.FlattenedStirlingTypeBRuns

namespace MetaMathlibExt

-- For `n = 0` the only partition is `{0}`: its word `1 1` is a single run.
example : wordRunCount (typeBFlattenedWord
    (Finpartition.indiscrete (a := Finset.Icc (-((0 : ℕ) : ℤ)) (0 : ℕ)) (by decide))) = 1 := by
  rw [wordRunCount_typeBFlattenedWord _ (isTypeBSetPartition_indiscrete 0)]
  decide

-- The one-block partition of `[-2, 2]` has no labelled block; its zero block has three
-- nonnegative elements, so its word `1 2 2 3 3 1` has two runs.
example : wordRunCount (typeBFlattenedWord
    (Finpartition.indiscrete (a := Finset.Icc (-((2 : ℕ) : ℤ)) (2 : ℕ)) (by decide))) = 2 := by
  rw [wordRunCount_typeBFlattenedWord _ (isTypeBSetPartition_indiscrete 2)]
  decide

-- The type `B` set partition `{0} | {1, 2, -3} | {-1, -2, 3}` of `[-3, 3]`.
private def mixedPartition : Finpartition (Finset.Icc (-((3 : ℕ) : ℤ)) (3 : ℕ)) where
  parts := {{0}, {1, 2, -3}, {-1, -2, 3}}
  supIndep := by
    rw [Finset.supIndep_iff_disjoint_erase]
    decide
  sup_parts := by decide
  bot_notMem := by decide

private theorem isTypeBSetPartition_mixedPartition : IsTypeBSetPartition mixedPartition := by
  refine ⟨by decide, {0}, ⟨by decide, by decide⟩, ?_⟩
  rintro b ⟨hb, hneg⟩
  simp only [mixedPartition, Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl | rfl
  · rfl
  · revert hneg
    decide
  · revert hneg
    decide

-- Adler's labelling keeps only `{1, 2, -3}`, the block of the pair holding `1`.
example : adlerBlockLabels mixedPartition = {1} := by
  decide

-- The kept block's negative element adds a run, and so do its two positive elements: the word
-- `1 1 4 4 2 3 3 2` has the three runs `1 1 4 4`, `2 3 3` and `2`.
example : wordRunCount (typeBFlattenedWord mixedPartition) = 3 := by
  rw [wordRunCount_typeBFlattenedWord _ isTypeBSetPartition_mixedPartition]
  decide

end MetaMathlibExt
