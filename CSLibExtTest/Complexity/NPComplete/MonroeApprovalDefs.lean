/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.MonroeApprovalDefs

namespace MetaMathlibExt.Complexity.NPComplete.MonroeApproval

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : MonroeApprovalInstance) :
    monroeApprovalDec (bitEncode i) = true ↔ WellFormed i ∧ MonroeApprovalFeasible i := by
  simp [monroeApprovalDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : monroeApprovalDec [true] = false := by
  have h : bitDecode (α := MonroeApprovalInstance) [true] = none := rfl
  simp [monroeApprovalDec, h]

/-- Two voters approving different candidates are each represented by their own candidate. -/
example :
    monroeApprovalDec
      (bitEncode ((2, [[true, false], [false, true]], 2, 0) : MonroeApprovalInstance)) =
        true := by
  apply (accepts_encoding _).2
  refine ⟨by unfold WellFormed; decide, Finset.univ, by decide, fun v => v, ?_⟩
  unfold assigned misrepresentation
  decide

/-- With a single representative, one of the two voters is represented by a candidate they do
not approve. -/
example :
    monroeApprovalDec
      (bitEncode ((2, [[true, false], [false, true]], 1, 0) : MonroeApprovalInstance)) =
        false := by
  rw [Bool.eq_false_iff]
  intro h
  have hf := ((accepts_encoding _).1 h).2
  revert hf
  unfold MonroeApprovalFeasible assigned misrepresentation
  decide

/-- An approval vector with the wrong number of entries is malformed. -/
example :
    monroeApprovalDec
      (bitEncode ((2, [[true]], 1, 1) : MonroeApprovalInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  have hw := ((accepts_encoding _).1 h).1
  revert hw
  unfold WellFormed
  decide

end MetaMathlibExt.Complexity.NPComplete.MonroeApproval
