/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.SubsetProductDefs

namespace MetaMathlibExt.Complexity.NPComplete.SubsetProduct

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : SubsetProductInstance) :
    subsetProductDec (bitEncode i) = true ↔ WellFormed i ∧ SubsetProductFeasible i := by
  simp [subsetProductDec, bitDecode_bitEncode]

private theorem rejects_undecodable (bits : List Bool)
    (h : bitDecode (α := SubsetProductInstance) bits = none) :
    subsetProductDec bits = false := by
  simp [subsetProductDec, h]

/-- A lone continuation bit is a truncated instance encoding. -/
example : subsetProductDec [true] = false :=
  rejects_undecodable [true] rfl

/-- Selecting `2` and `3`, while skipping `5`, reaches the target product `6`. -/
example : subsetProductDec (bitEncode (([2, 5, 3], 6) : SubsetProductInstance)) = true := by
  apply (accepts_encoding _).2
  refine ⟨?_, [2, 3], ?_, rfl⟩
  · unfold WellFormed
    decide
  · decide

/-- A zero entry is malformed, even when selecting it would reach the target. -/
example : subsetProductDec (bitEncode (([0, 2], 0) : SubsetProductInstance)) = false := by
  have h : ¬ WellFormed (([0, 2], 0) : SubsetProductInstance) := by
    unfold WellFormed
    decide
  simp [subsetProductDec, bitDecode_bitEncode, h]

end MetaMathlibExt.Complexity.NPComplete.SubsetProduct
