/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Computability.Complexity.Karp.PairedPartition

namespace CSLibExtTest.Computability.Complexity.Karp.PairedPartition

open MetaMathlibExt.BitstringEncoding MetaMathlibExt.Complexity.NPComplete.PairedPartition

-- Two equal pairs are distinct occurrences; choose the first size in one and the second in the other.
example : pairedPartitionDec (bitEncode ([(2, 5), (2, 5)] : PairedPartitionInstance)) = true := by
  simp only [pairedPartitionDec, bitDecode_bitEncode, decide_eq_true_eq]
  exact ⟨by simp [WellFormed], [true, false], by decide, by decide⟩

-- Even total weight alone does not make an instance feasible.
example : pairedPartitionDec (bitEncode ([(1, 3)] : PairedPartitionInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq]
  simp only [pairedPartitionDec, bitDecode_bitEncode, decide_eq_true_eq]
  rintro ⟨_, w, h, hs⟩
  cases w with
  | nil => simp at h
  | cons b w => cases b <;> simp [chosen] at hs

-- The empty instance is feasible, but zero weights are not allowed.
example : pairedPartitionDec [] = true := by
  have h : bitDecode (α := PairedPartitionInstance) [] = some [] := rfl
  simp only [pairedPartitionDec, h, decide_eq_true_eq]
  exact ⟨by simp [WellFormed], [], rfl, rfl⟩

example : pairedPartitionDec (bitEncode ([(0, 0)] : PairedPartitionInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq]
  simp [pairedPartitionDec, WellFormed]

-- A noncanonical false-ended payload decodes to 2, not 0.
example : pairedPartitionDec (delimit (delimit [false] ++ [false])) = true := by
  have h : bitDecode (α := PairedPartitionInstance) (delimit (delimit [false] ++ [false])) =
      some [(2, 2)] := by decide
  simp only [pairedPartitionDec, h, decide_eq_true_eq]
  exact ⟨by simp [WellFormed], [true], by decide, by decide⟩

-- Reject a truncated outer frame and an incomplete first component inside a complete outer frame.
example : pairedPartitionDec [true] = false := rfl
example : pairedPartitionDec (delimit [true]) = false := rfl

#check pairedPartition_npComplete

end CSLibExtTest.Computability.Complexity.Karp.PairedPartition
