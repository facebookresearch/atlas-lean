/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.BlockSortingDefs

namespace MetaMathlibExt.Complexity.NPComplete.BlockSorting

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : BlockSortingInstance) :
    blockSortingDec (bitEncode i) = true ↔ WellFormed i ∧ BlockSortingFeasible i := by
  simp [blockSortingDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : blockSortingDec [true] = false := by
  have h : bitDecode (α := BlockSortingInstance) [true] = none := rfl
  simp [blockSortingDec, h]

/-- In `2 1` the blocks are the singletons `2` and `1`; moving the block `2` to the end sorts the
permutation in one block move. -/
example : blockSortingDec (bitEncode (([2, 1], 1) : BlockSortingInstance)) = true := by
  refine (accepts_encoding _).2 ⟨by unfold WellFormed identity; decide, [[1, 2]], by decide, ?_,
    by decide⟩
  refine List.IsChain.cons_cons ⟨[], [2], [1], [1], [], rfl, ⟨by simp, by decide, by decide, ?_⟩,
    rfl, rfl, by decide⟩ (List.isChain_singleton _)
  intro B' _ h₁ h₂
  have key : ∀ B' ∈ ([2, 1] : List ℕ).sublists, [2] <:+: B' → B' <:+: identity 2 → B' = [2] := by
    decide
  exact key B' (List.mem_sublists.2 h₁.sublist) ‹_› h₂

/-- `2 1` is not the identity, so it cannot be sorted with `0` block moves. -/
example : blockSortingDec (bitEncode (([2, 1], 0) : BlockSortingInstance)) = false := by
  rw [Bool.eq_false_iff, Ne, accepts_encoding]
  rintro ⟨-, s, hs, -, hl⟩
  obtain rfl : s = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hs)
  exact absurd hl (by decide)

end MetaMathlibExt.Complexity.NPComplete.BlockSorting
