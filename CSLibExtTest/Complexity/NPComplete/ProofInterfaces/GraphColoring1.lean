/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.AchromaticNumberDefs

namespace MetaMathlibExt.Complexity.NPComplete.AchromaticNumber

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

example (i : AchromaticNumberInstance) :
    achromaticNumberDec (bitEncode i) = true ↔ WellFormed i ∧ AchromaticNumberFeasible i := by
  simp [achromaticNumberDec, bitDecode_bitEncode]

private theorem rejects_undecodable (bits : List Bool)
    (h : bitDecode (α := AchromaticNumberInstance) bits = none) :
    achromaticNumberDec bits = false := by
  simp [achromaticNumberDec, h]

/-- A lone continuation bit is a truncated instance encoding. -/
example : achromaticNumberDec [true] = false :=
  rejects_undecodable [true] rfl

private theorem rejects_malformed (i : AchromaticNumberInstance)
    (h : ¬ WellFormed i) :
    achromaticNumberDec (bitEncode i) = false := by
  simp [achromaticNumberDec, bitDecode_bitEncode, h]

/-- A self-loop is not a valid input edge. -/
example :
    achromaticNumberDec (bitEncode ((1, [(0, 0)], 1) : AchromaticNumberInstance)) = false := by
  apply rejects_malformed _
  unfold WellFormed
  decide

end MetaMathlibExt.Complexity.NPComplete.AchromaticNumber
