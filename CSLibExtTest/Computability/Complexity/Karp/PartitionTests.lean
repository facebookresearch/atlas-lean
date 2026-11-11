/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.PartitionReductions

/-! # Boundary tests for exact binary PARTITION semantics -/

open MetaMathlibExt.Complexity.NPComplete.Partition
open MetaMathlibExt.BitstringEncoding Cslib.Complexity.Karp

example : PartitionFeasible [] := ⟨[], .slnil, rfl⟩

example : PartitionFeasible [0, 0] :=
  ⟨[], List.nil_sublist _, rfl⟩

example : PartitionFeasible [3, 3] :=
  ⟨[3], by decide, rfl⟩

example : ¬ PartitionFeasible [3] := by
  rintro ⟨s, _, h⟩
  simp only [List.sum_cons, List.sum_nil] at h
  omega

example : ¬ PartitionFeasible [1, 2] := by
  rintro ⟨s, _, h⟩
  simp only [List.sum_cons, List.sum_nil] at h
  omega

example : fromSubsetSum [] 0 = [0, 0] := rfl
example : fromSubsetSum [] 1 = [0, 2] := rfl
example : fromSubsetSum [2, 2] 2 = [4, 4, 2, 2] := rfl

example : ¬ PartitionFeasible (fromSubsetSum [1, 2] 4) := by
  rw [fromSubsetSum_feasible]
  rintro ⟨s, hs, he⟩
  have hb := hs.sum_le_sum (fun _ _ => Nat.zero_le _)
  simp only [List.sum_cons, List.sum_nil] at hb
  omega

example : PartitionFeasible (fromSubsetSum [1, 2] 0) :=
  (fromSubsetSum_feasible _ _).2 ⟨[], List.nil_sublist _, rfl⟩

example : PartitionFeasible (fromSubsetSum [1, 2] 3) :=
  (fromSubsetSum_feasible _ _).2 ⟨[1, 2], List.Sublist.refl _, rfl⟩

-- A false-ended payload decodes to 2, not zero: multiplicity matters.
example : partitionDec [true, false, false, true, false, false] = true := by
  have hd : bitDecode (α := List ℕ)
      [true, false, false, true, false, false] = some [2, 2] := by decide
  simp only [partitionDec, hd, decide_eq_true_eq]
  exact ⟨[2], by decide, rfl⟩

example : partitionDec [true] = false := by
  have hd : bitDecode (α := List ℕ) [true] = none := by decide
  simp only [partitionDec, hd]

example : partitionDec [true, false] = false := by
  have hd : bitDecode (α := List ℕ) [true, false] = none := by decide
  simp only [partitionDec, hd]

example : reduceFromSubsetSum [] = bitEncode ([1] : List ℕ) := by decide
example : reduceToSubsetSum [true] = noSS := by decide
example : reduceToSubsetSum [] = encodeSS [] 0 := by decide

-- The existing SUBSET-SUM verifier consumes actual reduction output.
example : SSVerify.ssCheck
    (reduceToSubsetSum (bitEncode ([2, 2] : List ℕ))) [true, false] = true :=
  by decide

example : SSVerify.ssCheck
    (reduceToSubsetSum [true, false, false, true, false, false])
    [true, false] = true := by decide

example : SSVerify.ssCheck
    (reduceToSubsetSum (bitEncode ([1, 2] : List ℕ))) [true, false] = false :=
  by decide

example : reduceFromSubsetSum (encodeSS [2, 2] 2) =
    bitEncode ([4, 4, 2, 2] : List ℕ) := by decide
