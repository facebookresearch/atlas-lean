/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.DynamicStorageAllocationDefs

namespace MetaMathlibExt.Complexity.NPComplete.DynamicStorageAllocation

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

example (i : DynamicStorageAllocationInstance) :
    dynamicStorageAllocationDec (bitEncode i) = true ↔
      WellFormed i ∧ DynamicStorageAllocationFeasible i := by
  simp [dynamicStorageAllocationDec, bitDecode_bitEncode]

private theorem rejects_undecodable (bits : List Bool)
    (h : bitDecode (α := DynamicStorageAllocationInstance) bits = none) :
    dynamicStorageAllocationDec bits = false := by
  simp [dynamicStorageAllocationDec, h]

/-- A lone continuation bit is a truncated instance encoding. -/
example : dynamicStorageAllocationDec [true] = false :=
  rejects_undecodable [true] rfl

private theorem rejects_malformed (i : DynamicStorageAllocationInstance)
    (h : ¬ WellFormed i) :
    dynamicStorageAllocationDec (bitEncode i) = false := by
  simp [dynamicStorageAllocationDec, bitDecode_bitEncode, h]

/-- An allocation of size zero is outside the instance domain. -/
example :
    dynamicStorageAllocationDec
      (bitEncode (([(0, 0, 1)], 1) : DynamicStorageAllocationInstance)) =
        false := by
  apply rejects_malformed _
  unfold WellFormed
  decide

end MetaMathlibExt.Complexity.NPComplete.DynamicStorageAllocation
