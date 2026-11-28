/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.SingleTransferableVoteManipulationDefs

namespace MetaMathlibExt.Complexity.NPComplete.SingleTransferableVoteManipulation

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : SingleTransferableVoteManipulationInstance) :
    singleTransferableVoteManipulationDec (bitEncode i) = true ↔
      WellFormed i ∧ SingleTransferableVoteManipulationFeasible i := by
  simp [singleTransferableVoteManipulationDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : singleTransferableVoteManipulationDec [true] = false := by
  have h : bitDecode (α := SingleTransferableVoteManipulationInstance) [true] = none := rfl
  simp [singleTransferableVoteManipulationDec, h]

/-- A rearrangement of a list of two distinct entries is one of its two orders. -/
private theorem perm_two {α : Type} {s : List α} {x y : α} (hxy : x ≠ y) (h : s.Perm [x, y]) :
    s = [x, y] ∨ s = [y, x] := by
  have hlen := h.length_eq
  have hnd : s.Nodup := h.nodup_iff.2 (by simp [hxy])
  match s, hlen with
  | [a, b], _ =>
    have ha : a ∈ [x, y] := h.subset (by simp)
    have hb : b ∈ [x, y] := h.subset (by simp)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
    have hab : a ≠ b := by simpa using hnd
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp_all

/-- Candidates `0, 1, 2` with sincere ballots `1 0 2` and `2 1 0`: the manipulator ranks `0`
first, the three-way tie eliminates `0` (first in tie-breaking order), its vote transfers to `1`,
and `1` wins with two votes. -/
example : singleTransferableVoteManipulationDec
    (bitEncode (([0, 1, 2], [[1, 0, 2], [2, 1, 0]], 1) :
      SingleTransferableVoteManipulationInstance)) = true := by
  refine (accepts_encoding _).2 ⟨⟨by decide, by decide, ?_⟩, [0, 1, 2], List.Perm.refl _, by decide⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨List.Perm.swap _ _ _, by decide⟩

/-- Candidates `0, 1` with one sincere ballot `1 0`: candidate `1` can be made to win, but
candidate `0` cannot, since at best the tie is broken against it. -/
example : singleTransferableVoteManipulationDec
      (bitEncode (([0, 1], [[1, 0]], 1) : SingleTransferableVoteManipulationInstance)) = true ∧
    singleTransferableVoteManipulationDec
      (bitEncode (([0, 1], [[1, 0]], 0) : SingleTransferableVoteManipulationInstance)) =
        false := by
  constructor
  · exact (accepts_encoding _).2
      ⟨⟨by decide, by decide, by simpa using List.Perm.swap 0 1 []⟩, [1, 0],
        List.Perm.swap _ _ _, by decide⟩
  · rw [Bool.eq_false_iff]
    intro h
    obtain ⟨-, p, hp, hwin⟩ := (accepts_encoding _).1 h
    rcases perm_two (by decide) hp with rfl | rfl <;> revert hwin <;> decide

/-- A ballot missing a candidate makes the instance malformed. -/
example : singleTransferableVoteManipulationDec
    (bitEncode (([0, 1], [[1]], 1) : SingleTransferableVoteManipulationInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  have := (((accepts_encoding _).1 h).1.2.2 [1] (by simp)).length_eq
  simp at this

end MetaMathlibExt.Complexity.NPComplete.SingleTransferableVoteManipulation
