/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.RelationInstanceKeyDefs

namespace MetaMathlibExt.Complexity.NPComplete.RelationInstanceKey

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

example (i : RelationInstanceKeyInstance) :
    relationInstanceKeyDec (bitEncode i) = true ↔ WellFormed i ∧ RelationInstanceKeyFeasible i := by
  simp [relationInstanceKeyDec, bitDecode_bitEncode]

private theorem rejects_undecodable (bits : List Bool)
    (h : bitDecode (α := RelationInstanceKeyInstance) bits = none) :
    relationInstanceKeyDec bits = false := by
  simp [relationInstanceKeyDec, h]

/-- A lone continuation bit is a truncated instance encoding. -/
example : relationInstanceKeyDec [true] = false :=
  rejects_undecodable [true] rfl

private theorem rejects_malformed (i : RelationInstanceKeyInstance)
    (h : ¬ WellFormed i) :
    relationInstanceKeyDec (bitEncode i) = false := by
  simp [relationInstanceKeyDec, bitDecode_bitEncode, h]

/-- A relation of arity two cannot contain a one-column tuple. -/
example :
    relationInstanceKeyDec (bitEncode ((2, [[0]], 1) : RelationInstanceKeyInstance)) = false := by
  apply rejects_malformed _
  unfold WellFormed
  decide

end MetaMathlibExt.Complexity.NPComplete.RelationInstanceKey
