/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.PositiveOneInThreeSatDefs

namespace MetaMathlibExt.Complexity.NPComplete.PositiveOneInThreeSat

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open OneInThreeSat (OneInThreeSatInstance)

example (i : OneInThreeSatInstance) :
    positiveOneInThreeSatDec (bitEncode i) = true ↔
      WellFormed i ∧ OneInThreeSat.OneInThreeSatFeasible i := by
  simp [positiveOneInThreeSatDec, bitDecode_bitEncode]

private theorem rejects_undecodable (bits : List Bool)
    (h : bitDecode (α := OneInThreeSatInstance) bits = none) :
    positiveOneInThreeSatDec bits = false := by
  simp [positiveOneInThreeSatDec, h]

/-- A lone continuation bit is a truncated instance encoding. -/
example : positiveOneInThreeSatDec [true] = false :=
  rejects_undecodable [true] rfl

private theorem rejects_malformed (i : OneInThreeSatInstance)
    (h : ¬ WellFormed i) :
    positiveOneInThreeSatDec (bitEncode i) = false := by
  simp [positiveOneInThreeSatDec, bitDecode_bitEncode, h]

/-- The positive-only language rejects a clause containing a negative literal. -/
example :
    positiveOneInThreeSatDec
      (bitEncode ((3, [[(0, false), (1, true), (2, true)]]) : OneInThreeSatInstance)) =
        false := by
  apply rejects_malformed _
  intro h
  exact Bool.noConfusion
    (h.2 [(0, false), (1, true), (2, true)] (by simp) (0, false) (by simp))

end MetaMathlibExt.Complexity.NPComplete.PositiveOneInThreeSat
