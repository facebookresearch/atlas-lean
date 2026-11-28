/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.CommunicationComplexityDefs

namespace MetaMathlibExt.Complexity.NPComplete.CommunicationComplexity

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : CommunicationComplexityInstance) :
    communicationComplexityDec (bitEncode i) = true ↔
      WellFormed i ∧ CommunicationComplexityFeasible i := by
  simp [communicationComplexityDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : communicationComplexityDec [true] = false := by
  have h : bitDecode (α := CommunicationComplexityInstance) [true] = none := rfl
  simp [communicationComplexityDec, h]

/-- The matrix whose entry is `y = 0` is computed by the one-bit protocol in which the second
player announces whether `y = 0`. -/
example : communicationComplexityDec (bitEncode
    ((2, [[true, false], [true, false]], 1) : CommunicationComplexityInstance)) = true := by
  refine (accepts_encoding _).2 ⟨by unfold WellFormed; decide,
    .bob (fun y => decide (y.val = 0)) (.output false) (.output true), by decide, by decide⟩

/-- The `2 × 2` equality matrix depends on both inputs, so no protocol of depth `1` computes
it: one message from a single player leaves the other player's input unknown. -/
example : communicationComplexityDec (bitEncode
    ((2, [[true, false], [false, true]], 1) : CommunicationComplexityInstance)) = false := by
  rw [Bool.eq_false_iff, Ne, accepts_encoding]
  rintro ⟨-, P, hd, h⟩
  have h00 := h 0 0
  have h01 := h 0 1
  have h10 := h 1 0
  have h11 := h 1 1
  rcases P with b | ⟨s, p, q⟩ | ⟨s, p, q⟩
  · cases b <;> simp_all [Protocol.eval, entry]
  · rcases p with _ | _ | _ <;> rcases q with _ | _ | _ <;>
      simp only [Protocol.depth] at hd <;> try omega
    cases hs : s 0 <;> simp_all [Protocol.eval, entry]
  · rcases p with _ | _ | _ <;> rcases q with _ | _ | _ <;>
      simp only [Protocol.depth] at hd <;> try omega
    cases hs : s 0 <;> simp_all [Protocol.eval, entry]

end MetaMathlibExt.Complexity.NPComplete.CommunicationComplexity
