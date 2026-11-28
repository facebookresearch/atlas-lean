/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.MinimumEquivalentDigraphDefs

namespace MetaMathlibExt.Complexity.NPComplete.MinimumEquivalentDigraph

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : MinimumEquivalentDigraphInstance) :
    minimumEquivalentDigraphDec (bitEncode i) = true ↔
      WellFormed i ∧ MinimumEquivalentDigraphFeasible i := by
  simp [minimumEquivalentDigraphDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : minimumEquivalentDigraphDec [true] = false := by
  have h : bitDecode (α := MinimumEquivalentDigraphInstance) [true] = none := rfl
  simp [minimumEquivalentDigraphDec, h]

/-- Keeping the only arc preserves reachability and meets a budget of one. -/
example :
    minimumEquivalentDigraphDec
      (bitEncode ((2, [(0, 1)], 1) : MinimumEquivalentDigraphInstance)) = true := by
  apply (accepts_encoding _).2
  refine ⟨?_, [(0, 1)], List.Sublist.refl _, by decide, ?_⟩
  · unfold WellFormed
    decide
  · intro u _ v _
    rfl

end MetaMathlibExt.Complexity.NPComplete.MinimumEquivalentDigraph
