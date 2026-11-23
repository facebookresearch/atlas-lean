/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.Assembly.StringOverlap
public meta import CSLibExt.Bioinformatics.Assembly.StringOverlap

/-!
# Tests for the string overlap/merge library

Concrete evaluations on `Nat` and `Char` lists, plus instances of the general
lemmas at concrete values and axiom probes for every test.
-/

namespace Cslib.Bioinformatics.Assembly.StringOverlap


/-- No common suffix/prefix: overlap is `0`. -/
theorem test_overlap_zero : overlap [1, 2] [3, 4] = 0 := by decide

/-- Partial overlap of length `1`. -/
theorem test_overlap_one : overlap [1, 2, 3] [3, 4] = 1 := by decide

/-- Partial overlap of length `3`. -/
theorem test_overlap_three : overlap [1, 2, 1, 2] [2, 1, 2, 3] = 3 := by decide

/-- Full overlap: `b` is absorbed. -/
theorem test_overlap_full : overlap [1, 2, 3] [2, 3] = 2 := by decide

/-- Full overlap of identical strings. -/
theorem test_overlap_self : overlap [1, 2] [1, 2] = 2 := by decide

/-- Empty left input overlaps nothing. -/
theorem test_overlap_nil_left : overlap ([] : List Nat) [1, 2] = 0 := by decide

/-- Empty right input overlaps nothing. -/
theorem test_overlap_nil_right : overlap [1, 2] ([] : List Nat) = 0 := by decide

/-- Periodic strings overlap. -/
theorem test_overlap_periodic : overlap [1, 1, 1] [1, 1] = 2 := by decide

/-- Overlap over `Char` lists. -/
theorem test_overlap_char : overlap ['a', 'b', 'a'] ['b', 'a', 'c'] = 2 := by decide

/-- Merge splices along the overlap. -/
theorem test_merge_splice : merge [1, 2, 3] [3, 4] = [1, 2, 3, 4] := by decide

/-- Merge with no overlap concatenates. -/
theorem test_merge_concat : merge [1, 2] [3, 4] = [1, 2, 3, 4] := by decide

/-- Merge with full overlap absorbs `b`. -/
theorem test_merge_absorb : merge [1, 2, 3] [2, 3] = [1, 2, 3] := by decide

/-- Merging onto the empty string returns `b`. -/
theorem test_merge_nil : merge ([] : List Nat) [1, 2] = [1, 2] := by decide

/-- Merge over `Char` lists. -/
theorem test_merge_char : merge ['a', 'b'] ['b', 'c'] = ['a', 'b', 'c'] := by decide

/-- Length formula at concrete values, via `length_merge`. -/
theorem test_length_merge_splice : (merge [1, 2, 3] [3, 4]).length = 4 := by
  have h := length_merge [1, 2, 3] [3, 4]
  rw [test_overlap_one] at h
  exact h

/-- Length formula at concrete values with zero overlap, via `length_merge`. -/
theorem test_length_merge_concat : (merge [1, 2] [3, 4]).length = 4 := by
  have h := length_merge [1, 2] [3, 4]
  rw [test_overlap_zero] at h
  exact h

/-- Folded merge of three strings. -/
theorem test_mergeAll_value :
    mergeAll [[1, 2], [2, 3], [3, 4]] = [1, 2, 3, 4] := by decide

/-- First input appears in the folded merge. -/
theorem test_mergeAll_contains_first :
    [1, 2] <:+: (mergeAll [[1, 2], [2, 3], [3, 4]]) :=
  mem_mergeAll_contains _ _ (by simp)

/-- Second input appears in the folded merge. -/
theorem test_mergeAll_contains_second :
    [2, 3] <:+: (mergeAll [[1, 2], [2, 3], [3, 4]]) :=
  mem_mergeAll_contains _ _ (by simp)

/-- Third input appears in the folded merge. -/
theorem test_mergeAll_contains_third :
    [3, 4] <:+: (mergeAll [[1, 2], [2, 3], [3, 4]]) :=
  mem_mergeAll_contains _ _ (by simp)

/-- Prefix property at concrete values. -/
theorem test_prefix_instance : [1, 2] <+: merge [1, 2] [2, 3] :=
  isPrefix_merge_self [1, 2] [2, 3]

/-- Suffix property at concrete values. -/
theorem test_suffix_instance : [2, 3] <:+ merge [1, 2] [2, 3] :=
  isSuffix_merge [1, 2] [2, 3]

/-- Overlap characterization at concrete values. -/
theorem test_spec_instance :
    OverlapMatch [1, 2, 3] [3, 4] 1 ∧
      ∀ k' : Nat, OverlapMatch [1, 2, 3] [3, 4] k' → k' ≤ 1 :=
  (overlap_spec [1, 2, 3] [3, 4] 1).mp test_overlap_one.symm

/-- Full-overlap/suffix equivalence at concrete values. -/
theorem test_suffix_iff_instance :
    overlap [1, 2, 3] [2, 3] = [2, 3].length ↔ [2, 3] <:+ [1, 2, 3] :=
  overlap_eq_right_length_iff_suffix [1, 2, 3] [2, 3]

/-- `[3, 4]` is not a substring of `[1, 2]`. -/
theorem test_not_contains_right : ¬[3, 4] <:+: [1, 2] := by
  intro h
  obtain ⟨x, y, hxy⟩ := h
  cases x with
  | nil => simp at hxy
  | cons h t =>
    have hlen := congrArg List.length hxy
    simp [List.length_append] at hlen
    omega

/-- `[1, 2]` is not a substring of `[3, 4]`. -/
theorem test_not_contains_left : ¬[1, 2] <:+: [3, 4] := by
  intro h
  obtain ⟨x, y, hxy⟩ := h
  cases x with
  | nil => simp at hxy
  | cons h t =>
    have hlen := congrArg List.length hxy
    simp [List.length_append] at hlen
    omega

/-- Substring-free inputs overlap strictly below full length. -/
theorem test_substring_free :
    overlap [1, 2] [3, 4] < 2 ∧ overlap [3, 4] [1, 2] < 2 :=
  overlap_lt_of_substring_free [1, 2] [3, 4]
    test_not_contains_right test_not_contains_left

/-- Fold regrouping coherence at concrete values. -/
theorem test_mergeAll_append_instance :
    mergeAll ([[1, 2]] ++ [[2, 3]]) =
      [[2, 3]].foldl merge (mergeAll [[1, 2]]) :=
  mergeAll_append _ _

/-- Folded length over a cons ordering at concrete values. -/
theorem test_length_mergeAll_cons_instance :
    (mergeAll [[1, 2], [2, 3]]).length =
      ([[2, 3]].foldl merge (merge [] [1, 2])).length :=
  length_mergeAll_cons _ _

/-- Tracked-length fold equals the actual length at concrete values. -/
theorem test_length_mergeAll_fold_instance :
    (mergeAll [[1, 2], [2, 3]]).length =
      ([[1, 2], [2, 3]].foldl mergeLenStep ([], 0)).2 :=
  length_mergeAll_fold _

/-- Binary `merge` is not associative. -/
theorem test_merge_not_associative :
    merge (merge [1] [2]) [1, 2] ≠ merge [1] (merge [2] [1, 2]) :=
  merge_not_associative

#print axioms test_overlap_zero
#print axioms test_overlap_one
#print axioms test_overlap_three
#print axioms test_overlap_full
#print axioms test_overlap_self
#print axioms test_overlap_nil_left
#print axioms test_overlap_nil_right
#print axioms test_overlap_periodic
#print axioms test_overlap_char
#print axioms test_merge_splice
#print axioms test_merge_concat
#print axioms test_merge_absorb
#print axioms test_merge_nil
#print axioms test_merge_char
#print axioms test_length_merge_splice
#print axioms test_length_merge_concat
#print axioms test_mergeAll_value
#print axioms test_mergeAll_contains_first
#print axioms test_mergeAll_contains_second
#print axioms test_mergeAll_contains_third
#print axioms test_prefix_instance
#print axioms test_suffix_instance
#print axioms test_spec_instance
#print axioms test_suffix_iff_instance
#print axioms test_not_contains_right
#print axioms test_not_contains_left
#print axioms test_substring_free
#print axioms overlap_spec
#print axioms length_merge
#print axioms isPrefix_merge_self
#print axioms isSuffix_merge
#print axioms mem_mergeAll_contains
#print axioms overlap_eq_right_length_iff_suffix
#print axioms overlap_lt_of_substring_free
#print axioms test_mergeAll_append_instance
#print axioms test_length_mergeAll_cons_instance
#print axioms test_length_mergeAll_fold_instance
#print axioms test_merge_not_associative
#print axioms mergeAll_append
#print axioms length_foldl_merge_cons
#print axioms length_mergeAll_cons
#print axioms foldl_mergeLenStep_snd
#print axioms length_mergeAll_fold
#print axioms merge_not_associative

end Cslib.Bioinformatics.Assembly.StringOverlap
