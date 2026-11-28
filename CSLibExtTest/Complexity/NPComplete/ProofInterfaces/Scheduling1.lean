/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.ThreeProcessorOpenShopSchedulingDefs

namespace MetaMathlibExt.Complexity.NPComplete.ThreeProcessorOpenShopScheduling

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open OpenShopScheduling (OpenShopSchedulingInstance)

example (i : OpenShopSchedulingInstance) :
    threeProcessorOpenShopSchedulingDec (bitEncode i) = true ↔
      WellFormed i ∧ OpenShopScheduling.OpenShopSchedulingFeasible i := by
  simp [threeProcessorOpenShopSchedulingDec, bitDecode_bitEncode]

private theorem rejects_undecodable (bits : List Bool)
    (h : bitDecode (α := OpenShopSchedulingInstance) bits = none) :
    threeProcessorOpenShopSchedulingDec bits = false := by
  simp [threeProcessorOpenShopSchedulingDec, h]

/-- A lone continuation bit is a truncated instance encoding. -/
example : threeProcessorOpenShopSchedulingDec [true] = false :=
  rejects_undecodable [true] rfl

private theorem rejects_malformed (i : OpenShopSchedulingInstance)
    (h : ¬ WellFormed i) :
    threeProcessorOpenShopSchedulingDec (bitEncode i) = false := by
  simp [threeProcessorOpenShopSchedulingDec, bitDecode_bitEncode, h]

/-- Two processors do not meet the fixed three-processor restriction. -/
example :
    threeProcessorOpenShopSchedulingDec
      (bitEncode ((2, [[1, 1]], 2) : OpenShopSchedulingInstance)) =
        false := by
  apply rejects_malformed _
  intro h
  exact (by decide : (2 : Nat) ≠ 3) h.2

end MetaMathlibExt.Complexity.NPComplete.ThreeProcessorOpenShopScheduling
