/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.MinimumExactCoverDefs

namespace MetaMathlibExt.Complexity.NPComplete.MinimumExactCover

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : MinimumExactCoverInstance) :
    minimumExactCoverDec (bitEncode i) = true ↔ WellFormed i ∧ MinimumExactCoverFeasible i := by
  simp [minimumExactCoverDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : minimumExactCoverDec [true] = false := by
  have h : bitDecode (α := MinimumExactCoverInstance) [true] = none := rfl
  simp [minimumExactCoverDec, h]

/-- The members `{0, 1}` and `{2}` cover `{0, 1, 2}` with total size three. -/
example :
    minimumExactCoverDec
      (bitEncode ((3, [[0, 1], [1, 2], [2]], 3) : MinimumExactCoverInstance)) = true := by
  apply (accepts_encoding _).2
  refine ⟨by unfold WellFormed ExactCover.WellFormed; decide, {0, 2}, by decide, by decide⟩

/-- The only cover uses both overlapping members, of total size four, above the bound three. -/
example :
    minimumExactCoverDec
      (bitEncode ((3, [[0, 1], [1, 2]], 3) : MinimumExactCoverInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  have hf := ((accepts_encoding _).1 h).2
  revert hf
  unfold MinimumExactCoverFeasible
  decide

end MetaMathlibExt.Complexity.NPComplete.MinimumExactCover
