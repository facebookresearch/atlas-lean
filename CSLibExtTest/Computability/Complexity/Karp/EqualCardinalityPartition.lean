/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Computability.Complexity.Karp.EqualCardinalityPartition

/-! Tests of equal-cardinality PARTITION on encoded lists. -/

open MetaMathlibExt.BitstringEncoding
open MetaMathlibExt.Complexity.NPComplete.EqualCardinalityPartition

example : equalCardinalityPartitionDec ∈ MetaMathlibExt.ComplexityTheory.NP :=
  equalCardinalityPartition_npComplete.1

private theorem accepts_encode (as : List ℕ) : equalCardinalityPartitionDec (bitEncode as) = true ↔
    WellFormed as ∧ EqualCardinalityPartitionFeasible as := by
  simp [equalCardinalityPartitionDec]

example : equalCardinalityPartitionDec (bitEncode ([] : List ℕ)) = true := by
  apply (accepts_encode _).2
  exact ⟨by simp [WellFormed], [], .slnil, rfl, rfl⟩

-- The two copies of each weight have distinct positions.
example : equalCardinalityPartitionDec (bitEncode ([1, 1, 2, 2] : List ℕ)) = true := by
  apply (accepts_encode _).2
  exact ⟨by simp [WellFormed], [1, 2], by decide, rfl, rfl⟩

-- An ordinary balanced partition need not have two equal-length halves.
example : equalCardinalityPartitionDec (bitEncode ([1, 2, 3] : List ℕ)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨_, s, _, hl, _⟩ := (accepts_encode _).1 h
  simp only [List.length_cons, List.length_nil] at hl
  omega

-- Although [0, 0] has a balanced singleton, it is not a well-formed instance.
example : equalCardinalityPartitionDec (bitEncode ([0, 0] : List ℕ)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  exact (Nat.lt_irrefl 0) ((accepts_encode _).1 h |>.1 0 (by simp))

-- Balancing the sum and halving the cardinality separately does not suffice.
example : equalCardinalityPartitionDec (bitEncode ([1, 1, 1, 3] : List ℕ)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨_, s, hs, hl, ht⟩ := (accepts_encode _).1 h
  have hnone : ¬ ∃ t ∈ ([1, 1, 1, 3] : List ℕ).sublists, t.length = 2 ∧ t.sum = 3 :=
    by decide
  simp only [List.length_cons, List.length_nil] at hl
  simp only [List.sum_cons, List.sum_nil] at ht
  exact hnone ⟨s, List.mem_sublists.2 hs, by omega, by omega⟩

-- The one-bit payload [false] is a noncanonical representation of 2, not of zero.
example : equalCardinalityPartitionDec (delimit [false] ++ delimit [false]) = true := by
  have hd : bitDecode (α := List ℕ) (delimit [false] ++ delimit [false]) = some [2, 2] :=
    by decide
  simp only [equalCardinalityPartitionDec, hd, decide_eq_true_eq]
  exact ⟨by simp [WellFormed], [2], by decide, rfl, rfl⟩

-- This opening marker is missing its payload.
example : equalCardinalityPartitionDec [true] = false := by
  rfl
