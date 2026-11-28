/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.FlattenedStirlingTypeBBijection

namespace MetaMathlibExt.bijOn_typeBFlattenedWord

private def signed : Finpartition (Finset.Icc (-((3 : ℕ) : ℤ)) (3 : ℕ)) where
  parts := {{0}, {1, -2, 3}, {-1, 2, -3}}
  supIndep := by rw [Finset.supIndep_iff_disjoint_erase]; decide
  sup_parts := by decide
  bot_notMem := by decide

private def zeroBlock : Finpartition (Finset.Icc (-((3 : ℕ) : ℤ)) (3 : ℕ)) :=
  Finpartition.indiscrete (by decide)

private theorem signed_typeB : IsTypeBSetPartition signed := by
  apply isTypeBSetPartition_iff.mpr
  refine ⟨by decide, {0}, ⟨by decide, by decide⟩, ?_⟩
  rintro b ⟨hb, hs⟩
  simp only [signed, Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl | rfl
  · rfl
  all_goals revert hs; decide

private theorem word_eq_of_list {n : ℕ} {P : Finpartition (Finset.Icc (-(n : ℤ)) n)}
    {l : List ℕ} {w : Fin (2 * (n + 1)) → ℕ} (hl : typeBFlattenedWordList P = l)
    (hw : ∀ i : Fin (2 * (n + 1)), l.getD i 0 = w i) : typeBFlattenedWord P = w := by
  funext i
  rw [typeBFlattenedWord_apply, hl, hw]

private theorem signed_word : typeBFlattenedWord signed = ![1, 1, 3, 3, 2, 4, 4, 2] := by
  have hz : typeBShift ((signed.part 0).filter (0 ≤ ·)) = {1} := by decide
  have hl : adlerBlockLabels signed = {1} := by decide
  have hn : typeBShift ((signed.part 1).filter (· < 0)) = {3} := by decide
  have hp : typeBShift ((signed.part 1).filter (0 < ·)) = {2, 4} := by decide
  have hs : ({2, 4} : Finset ℕ).sort (· ≤ ·) = [2, 4] := by
    apply (Finset.sortedLT_sort _).eq_of_mem_iff (by decide)
    simp
  apply word_eq_of_list (l := [1, 1, 3, 3, 2, 4, 4, 2]) _ (by decide)
  simp [typeBFlattenedWordList_eq, hz, hl, hn, hp, wrappedWord_singleton, doubledWord_singleton,
    wrappedWord_eq_of_sort_eq hs]

private theorem zero_word : typeBFlattenedWord zeroBlock = ![1, 2, 2, 3, 3, 4, 4, 1] := by
  have hz : typeBShift ((zeroBlock.part 0).filter (0 ≤ ·)) = {1, 2, 3, 4} := by decide
  have hl : adlerBlockLabels zeroBlock = ∅ := by decide
  have hs : ({1, 2, 3, 4} : Finset ℕ).sort (· ≤ ·) = [1, 2, 3, 4] := by
    apply (Finset.sortedLT_sort _).eq_of_mem_iff (by decide)
    simp
  apply word_eq_of_list (l := [1, 2, 2, 3, 3, 4, 4, 1]) _ (by decide)
  simp [typeBFlattenedWordList_eq, hz, hl, wrappedWord_eq_of_sort_eq hs]

-- Check the two codomain words directly, without using the bijection or its maps-to lemma.
example : IsStirlingPermutation 4 ![1, 1, 3, 3, 2, 4, 4, 2] ∧ IsFlattenedWord ![1, 1, 3, 3, 2, 4, 4, 2] := by
  rw [isStirlingPermutation_iff]
  decide

example : IsStirlingPermutation 4 ![1, 2, 2, 3, 3, 4, 4, 1] ∧ IsFlattenedWord ![1, 2, 2, 3, 3, 4, 4, 1] := by
  rw [isStirlingPermutation_iff]
  decide

-- The negative-pair and zero-block encodings separate these two distinct partitions.
example : signed ≠ zeroBlock ∧ typeBFlattenedWord signed ≠ typeBFlattenedWord zeroBlock := by
  constructor
  · intro h
    have e := congrArg Finpartition.parts h
    revert e
    decide
  · rw [signed_word, zero_word]
    decide

-- Exhibit the preimages directly, once with a negative segment and once with a nontrivial
-- zero block.
example : ∃ P : Finpartition (Finset.Icc (-((3 : ℕ) : ℤ)) (3 : ℕ)),
    IsTypeBSetPartition P ∧ typeBFlattenedWord P = ![1, 1, 3, 3, 2, 4, 4, 2] :=
  ⟨signed, signed_typeB, signed_word⟩

example : ∃ P : Finpartition (Finset.Icc (-((3 : ℕ) : ℤ)) (3 : ℕ)),
    IsTypeBSetPartition P ∧ typeBFlattenedWord P = ![1, 2, 2, 3, 3, 4, 4, 1] :=
  ⟨zeroBlock, isTypeBSetPartition_indiscrete 3, zero_word⟩

-- With only the zero block, the boundary case maps to the two copies of 1.
example : typeBFlattenedWord (n := 0) (Finpartition.indiscrete (by decide)) = ![1, 1] := by
  let P : Finpartition (Finset.Icc (-((0 : ℕ) : ℤ)) (0 : ℕ)) := Finpartition.indiscrete (by decide)
  have hz : typeBShift ((P.part 0).filter (0 ≤ ·)) = {1} := by decide
  have hl : adlerBlockLabels P = ∅ := by decide
  apply word_eq_of_list (P := P) (l := [1, 1]) _ (by decide)
  simp [typeBFlattenedWordList_eq, hz, hl, wrappedWord_singleton]

-- A public API client can use surjectivity for a concrete target.
example : ∃ P : Finpartition (Finset.Icc (-((1 : ℕ) : ℤ)) (1 : ℕ)),
    IsTypeBSetPartition P ∧ typeBFlattenedWord P = ![1, 2, 2, 1] :=
  (bijOn_typeBFlattenedWord 1).surjOn (a := ![1, 2, 2, 1]) (by
    change IsStirlingPermutation 2 ![1, 2, 2, 1] ∧ IsFlattenedWord ![1, 2, 2, 1]
    rw [isStirlingPermutation_iff]
    decide)

-- The second partition in Buck et al.'s Example 2 has Adler labels 1 and 2.
private def twoLabelPartition : Finpartition (Finset.Icc (-((4 : ℕ) : ℤ)) (4 : ℕ)) where
  parts := {{0}, {1}, {-1}, {2, 3, -4}, {-2, -3, 4}}
  supIndep := by rw [Finset.supIndep_iff_disjoint_erase]; decide
  sup_parts := by decide
  bot_notMem := by decide

private def twoLabelWord : Fin (2 * (4 + 1)) → ℕ := ![1, 1, 2, 2, 5, 5, 3, 4, 4, 3]

private theorem twoLabelPartition_typeB : IsTypeBSetPartition twoLabelPartition := by
  apply isTypeBSetPartition_iff.mpr
  refine ⟨by decide, {0}, ⟨by decide, by decide⟩, ?_⟩
  rintro b ⟨hb, hs⟩
  simp only [twoLabelPartition, Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl
  · rfl
  all_goals revert hs; decide

private theorem twoLabelPartition_word : typeBFlattenedWord twoLabelPartition = twoLabelWord := by
  have hz : typeBShift ((twoLabelPartition.part 0).filter (0 ≤ ·)) = {1} := by decide
  have hl : adlerBlockLabels twoLabelPartition = {1, 2} := by decide
  have hls : ({1, 2} : Finset ℤ).sort (· ≤ ·) = [1, 2] := by
    apply (Finset.sortedLT_sort _).eq_of_mem_iff (by decide)
    simp
  have hn₁ : typeBShift ((twoLabelPartition.part 1).filter (· < 0)) = ∅ := by decide
  have hp₁ : typeBShift ((twoLabelPartition.part 1).filter (0 < ·)) = {2} := by decide
  have hn₂ : typeBShift ((twoLabelPartition.part 2).filter (· < 0)) = {5} := by decide
  have hp₂ : typeBShift ((twoLabelPartition.part 2).filter (0 < ·)) = {3, 4} := by decide
  have hps : ({3, 4} : Finset ℕ).sort (· ≤ ·) = [3, 4] := by
    apply (Finset.sortedLT_sort _).eq_of_mem_iff (by decide)
    simp
  have he : doubledWord ∅ = [] := by simp [doubledWord_eq_flatMap]
  apply word_eq_of_list (l := [1, 1, 2, 2, 5, 5, 3, 4, 4, 3]) _ (by decide)
  simp [typeBFlattenedWordList_eq, hz, hl, hls, hn₁, hp₁, hn₂, hp₂, he,
    wrappedWord_singleton, doubledWord_singleton, wrappedWord_eq_of_sort_eq hps]

-- The two descents both land on 3, even though the two nonzero labels differ.
example : Finset.univ.filter (wordRunStart twoLabelWord) = {0, 6, 9} := by decide

private theorem twoLabelWord_preimage : ∃ P : Finpartition (Finset.Icc (-((4 : ℕ) : ℤ)) (4 : ℕ)),
    IsTypeBSetPartition P ∧ typeBFlattenedWord P = twoLabelWord :=
  (bijOn_typeBFlattenedWord 4).surjOn (a := twoLabelWord) (by
    change IsStirlingPermutation 5 twoLabelWord ∧ IsFlattenedWord twoLabelWord
    rw [isStirlingPermutation_iff]
    decide)

-- The preimage supplied by surjectivity is exactly the partition from Example 2.
example : Classical.choose twoLabelWord_preimage = twoLabelPartition := by
  obtain ⟨hP, hword⟩ := Classical.choose_spec twoLabelWord_preimage
  exact (bijOn_typeBFlattenedWord 4).injOn hP twoLabelPartition_typeB
    (hword.trans twoLabelPartition_word.symm)

end MetaMathlibExt.bijOn_typeBFlattenedWord
