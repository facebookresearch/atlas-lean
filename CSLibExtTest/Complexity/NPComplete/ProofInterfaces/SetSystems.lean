/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.SetSplittingDefs

namespace MetaMathlibExt.Complexity.NPComplete.SetSplitting

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : SetSplittingInstance) :
    setSplittingDec (bitEncode i) = true ↔ WellFormed i ∧ SetSplittingFeasible i := by
  simp [setSplittingDec, bitDecode_bitEncode]

private theorem rejects_undecodable (bits : List Bool)
    (h : bitDecode (α := SetSplittingInstance) bits = none) :
    setSplittingDec bits = false := by
  simp [setSplittingDec, h]

/-- A lone continuation bit is a truncated instance encoding. -/
example : setSplittingDec [true] = false :=
  rejects_undecodable [true] rfl

/-- The set containing zero and one is split by choosing zero. -/
example :
    setSplittingDec (bitEncode ((2, [[0, 1]]) : SetSplittingInstance)) = true := by
  apply (accepts_encoding _).2
  refine ⟨?_, {0}, ?_, ?_⟩
  · unfold WellFormed
    decide
  · decide
  · intro s hs
    have hs' : s = [0, 1] := by simpa using hs
    subst s
    exact ⟨⟨0, by simp, by simp⟩, ⟨1, by simp, by decide⟩⟩

end MetaMathlibExt.Complexity.NPComplete.SetSplitting
