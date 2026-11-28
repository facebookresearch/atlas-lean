/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.RomanDominationDefs

namespace MetaMathlibExt.Complexity.NPComplete.RomanDomination

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : RomanDominationInstance) :
    romanDominationDec (bitEncode i) = true ↔ WellFormed i ∧ RomanDominationFeasible i := by
  simp [romanDominationDec, bitDecode_bitEncode]

private theorem rejects_undecodable (bits : List Bool)
    (h : bitDecode (α := RomanDominationInstance) bits = none) :
    romanDominationDec bits = false := by
  simp [romanDominationDec, h]

/-- A lone continuation bit is a truncated instance encoding. -/
example : romanDominationDec [true] = false :=
  rejects_undecodable [true] rfl

/-- Labeling the only vertex by one gives a Roman dominating labeling of weight one. -/
example :
    romanDominationDec (bitEncode ((1, [], 1) : RomanDominationInstance)) = true := by
  apply (accepts_encoding _).2
  refine ⟨?_, fun _ => 1, ?_, ?_, ?_⟩
  · unfold WellFormed
    decide
  · intro _
    exact Nat.le_succ 1
  · intro _ h
    exact (by decide : (1 : Nat) ≠ 0) h |>.elim
  · simp

end MetaMathlibExt.Complexity.NPComplete.RomanDomination
