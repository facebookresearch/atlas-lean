/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.BandwidthDefs

namespace MetaMathlibExt.Complexity.NPComplete.Bandwidth

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : BandwidthInstance) :
    bandwidthDec (bitEncode i) = true ↔ WellFormed i ∧ BandwidthFeasible i := by
  simp [bandwidthDec, bitDecode_bitEncode]

private theorem rejects_undecodable (bits : List Bool)
    (h : bitDecode (α := BandwidthInstance) bits = none) :
    bandwidthDec bits = false := by
  simp [bandwidthDec, h]

/-- A lone continuation bit is a truncated instance encoding. -/
example : bandwidthDec [true] = false :=
  rejects_undecodable [true] rfl

/-- A single edge has bandwidth at most one in the natural ordering. -/
example :
    bandwidthDec (bitEncode ((2, [(0, 1)], 1) : BandwidthInstance)) = true := by
  apply (accepts_encoding _).2
  refine ⟨?_, [0, 1], List.Perm.refl _, ?_⟩
  · unfold WellFormed
    decide
  · decide

end MetaMathlibExt.Complexity.NPComplete.Bandwidth
