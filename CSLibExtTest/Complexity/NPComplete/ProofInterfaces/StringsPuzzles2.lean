/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.WordHomomorphismDefs

namespace MetaMathlibExt.Complexity.NPComplete.WordHomomorphism

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

example (i : WordHomomorphismInstance) :
    wordHomomorphismDec (bitEncode i) = true ↔ WellFormed i ∧ WordHomomorphismFeasible i := by
  simp [wordHomomorphismDec, bitDecode_bitEncode]

private theorem rejects_undecodable (bits : List Bool)
    (h : bitDecode (α := WordHomomorphismInstance) bits = none) :
    wordHomomorphismDec bits = false := by
  simp [wordHomomorphismDec, h]

/-- A lone continuation bit is a truncated instance encoding. -/
example : wordHomomorphismDec [true] = false :=
  rejects_undecodable [true] rfl

private theorem rejects_malformed (i : WordHomomorphismInstance)
    (h : ¬ WellFormed i) :
    wordHomomorphismDec (bitEncode i) = false := by
  simp [wordHomomorphismDec, bitDecode_bitEncode, h]

/-- The target word cannot contain a letter outside the target alphabet. -/
example :
    wordHomomorphismDec (bitEncode ((1, [0], 1, [1]) : WordHomomorphismInstance)) = false := by
  apply rejects_malformed _
  unfold WellFormed
  decide

end MetaMathlibExt.Complexity.NPComplete.WordHomomorphism
