/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.FiveProcessorTaskSizeMakespanDefs

namespace MetaMathlibExt.Complexity.NPComplete.FiveProcessorTaskSizeMakespan

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open RCPSP (RCPSPInstance)

example (i : RCPSPInstance) :
    fiveProcessorTaskSizeMakespanDec (bitEncode i) = true ↔
      WellFormed i ∧ RCPSP.RCPSPFeasible i := by
  simp [fiveProcessorTaskSizeMakespanDec, bitDecode_bitEncode]

private theorem rejects_undecodable (bits : List Bool)
    (h : bitDecode (α := RCPSPInstance) bits = none) :
    fiveProcessorTaskSizeMakespanDec bits = false := by
  simp [fiveProcessorTaskSizeMakespanDec, h]

/-- A lone continuation bit is a truncated instance encoding. -/
example : fiveProcessorTaskSizeMakespanDec [true] = false :=
  rejects_undecodable [true] rfl

private theorem rejects_malformed (i : RCPSPInstance)
    (h : ¬ WellFormed i) :
    fiveProcessorTaskSizeMakespanDec (bitEncode i) = false := by
  simp [fiveProcessorTaskSizeMakespanDec, bitDecode_bitEncode, h]

/-- A resource capacity of four does not meet the five-processor restriction. -/
example :
    fiveProcessorTaskSizeMakespanDec
      (bitEncode (([(1, 1)], [], 4, 1) : RCPSPInstance)) =
        false := by
  apply rejects_malformed _
  intro h
  exact (by decide : (4 : Nat) ≠ 5) h.2.2.1

end MetaMathlibExt.Complexity.NPComplete.FiveProcessorTaskSizeMakespan
