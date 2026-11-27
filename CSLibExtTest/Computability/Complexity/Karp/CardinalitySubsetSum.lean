/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Computability.Complexity.Karp.CardinalitySubsetSum

/-!
# Exact-cardinality subset sum on encoded instances

These examples cover empty selections, repeated entries, exact cardinality,
noncanonical binary payloads, and truncated frames.
-/

open MetaMathlibExt.BitstringEncoding
open MetaMathlibExt.Complexity.NPComplete.CardinalitySubsetSum

private theorem accepts_encode (i : CardinalitySubsetSumInstance) :
    cardinalitySubsetSumDec (bitEncode i) = true ↔ CardinalitySubsetSumFeasible i := by
  simp [cardinalitySubsetSumDec]

example : cardinalitySubsetSumDec (bitEncode (([], 0, 0) : CardinalitySubsetSumInstance)) := by
  exact (accepts_encode _).2 ⟨[], .slnil, rfl, rfl⟩

example : cardinalitySubsetSumDec (bitEncode (([2, 7, 2], 2, 4) :
    CardinalitySubsetSumInstance)) := by
  exact (accepts_encode _).2 ⟨[2, 2], by decide, rfl, rfl⟩

-- The target is achievable, but every two-entry selection includes both entries.
example : cardinalitySubsetSumDec (bitEncode (([0, 2], 2, 0) :
    CardinalitySubsetSumInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨s, hs, hk, ht⟩ := (accepts_encode _).1 h
  have he := hs.eq_of_length hk
  subst s
  contradiction

-- The one-bit raw payload [false] decodes to two, including in the item list.
example : cardinalitySubsetSumDec
    (delimit (delimit [false]) ++ delimit [true] ++ [false]) := by
  have hd : bitDecode (α := CardinalitySubsetSumInstance)
      (delimit (delimit [false]) ++ delimit [true] ++ [false]) = some ([2], 1, 2) := by decide
  simp only [cardinalitySubsetSumDec, hd, decide_eq_true_eq]
  exact ⟨[2], .refl _, rfl, rfl⟩

example : cardinalitySubsetSumDec (delimit [true] ++ delimit [] ++ []) = false := by
  rfl

example : cardinalitySubsetSumDec (delimit [] ++ [true]) = false := by
  rfl
