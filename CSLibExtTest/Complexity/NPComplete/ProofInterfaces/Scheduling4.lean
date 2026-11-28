/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.UnrelatedMachinesMakespanTwoDefs

namespace MetaMathlibExt.Complexity.NPComplete.UnrelatedMachinesMakespanTwo

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

example (i : UnrelatedMachinesMakespanTwoInstance) :
    unrelatedMachinesMakespanTwoDec (bitEncode i) = true ↔
      WellFormed i ∧ UnrelatedMachinesMakespanTwoFeasible i := by
  simp [unrelatedMachinesMakespanTwoDec, bitDecode_bitEncode]

private theorem rejects_undecodable (bits : List Bool)
    (h : bitDecode (α := UnrelatedMachinesMakespanTwoInstance) bits = none) :
    unrelatedMachinesMakespanTwoDec bits = false := by
  simp [unrelatedMachinesMakespanTwoDec, h]

/-- A lone continuation bit is a truncated instance encoding. -/
example : unrelatedMachinesMakespanTwoDec [true] = false :=
  rejects_undecodable [true] rfl

private theorem rejects_malformed (i : UnrelatedMachinesMakespanTwoInstance)
    (h : ¬ WellFormed i) :
    unrelatedMachinesMakespanTwoDec (bitEncode i) = false := by
  simp [unrelatedMachinesMakespanTwoDec, bitDecode_bitEncode, h]

/-- A job must specify a processing time on each machine. -/
example :
    unrelatedMachinesMakespanTwoDec
      (bitEncode ((2, [[1]]) : UnrelatedMachinesMakespanTwoInstance)) =
        false := by
  apply rejects_malformed _
  unfold WellFormed
  decide

end MetaMathlibExt.Complexity.NPComplete.UnrelatedMachinesMakespanTwo
