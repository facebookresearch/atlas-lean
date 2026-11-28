/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.TwoProcessorJobShopThreeTasksDefs

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorJobShopThreeTasks

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open JobShopScheduling (JobShopSchedulingInstance)

example (i : JobShopSchedulingInstance) :
    twoProcessorJobShopThreeTasksDec (bitEncode i) = true ↔
      WellFormed i ∧ JobShopScheduling.JobShopSchedulingFeasible i := by
  simp [twoProcessorJobShopThreeTasksDec, bitDecode_bitEncode]

private theorem rejects_undecodable (bits : List Bool)
    (h : bitDecode (α := JobShopSchedulingInstance) bits = none) :
    twoProcessorJobShopThreeTasksDec bits = false := by
  simp [twoProcessorJobShopThreeTasksDec, h]

/-- A lone continuation bit is a truncated instance encoding. -/
example : twoProcessorJobShopThreeTasksDec [true] = false :=
  rejects_undecodable [true] rfl

private theorem rejects_malformed (i : JobShopSchedulingInstance)
    (h : ¬ WellFormed i) :
    twoProcessorJobShopThreeTasksDec (bitEncode i) = false := by
  simp [twoProcessorJobShopThreeTasksDec, bitDecode_bitEncode, h]

/-- A job of four alternating tasks exceeds the three-task limit. -/
example :
    twoProcessorJobShopThreeTasksDec
      (bitEncode ((2, [[(1, 1), (1, 2), (1, 1), (1, 2)]], 4) : JobShopSchedulingInstance)) =
        false := by
  apply rejects_malformed _
  intro h
  exact (by decide : ¬ (4 : Nat) ≤ 3)
    (h.2.2 [(1, 1), (1, 2), (1, 1), (1, 2)] (by simp))

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorJobShopThreeTasks
