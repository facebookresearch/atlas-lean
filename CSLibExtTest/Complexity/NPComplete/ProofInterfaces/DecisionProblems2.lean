/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.PartialDigestSupersetDefs

namespace MetaMathlibExt.Complexity.NPComplete.PartialDigestSuperset

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

example (i : PartialDigestSupersetInstance) :
    partialDigestSupersetDec (bitEncode i) = true ↔
      WellFormed i ∧ PartialDigestSupersetFeasible i := by
  simp [partialDigestSupersetDec, bitDecode_bitEncode]

private theorem rejects_undecodable (bits : List Bool)
    (h : bitDecode (α := PartialDigestSupersetInstance) bits = none) :
    partialDigestSupersetDec bits = false := by
  simp [partialDigestSupersetDec, h]

/-- A lone continuation bit is a truncated instance encoding. -/
example : partialDigestSupersetDec [true] = false :=
  rejects_undecodable [true] rfl

private theorem rejects_malformed (i : PartialDigestSupersetInstance)
    (h : ¬ WellFormed i) :
    partialDigestSupersetDec (bitEncode i) = false := by
  simp [partialDigestSupersetDec, bitDecode_bitEncode, h]

/-- A zero distance is excluded from the input multiset. -/
example :
    partialDigestSupersetDec (bitEncode (([0], 2) : PartialDigestSupersetInstance)) = false := by
  apply rejects_malformed _
  unfold WellFormed
  decide

end MetaMathlibExt.Complexity.NPComplete.PartialDigestSuperset
