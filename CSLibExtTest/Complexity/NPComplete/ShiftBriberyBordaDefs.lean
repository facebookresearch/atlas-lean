/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.ShiftBriberyBordaDefs
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

namespace MetaMathlibExt.Complexity.NPComplete.ShiftBriberyBorda

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open MetaMathlibExt.Complexity.NPComplete.BordaManipulationTwoManipulators (IsVote)

private theorem accepts_encoding (i : ShiftBriberyBordaInstance) :
    shiftBriberyBordaDec (bitEncode i) = true ↔ WellFormed i ∧ ShiftBriberyBordaFeasible i := by
  simp [shiftBriberyBordaDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : shiftBriberyBordaDec [true] = false := by
  have h : bitDecode (α := ShiftBriberyBordaInstance) [true] = none := rfl
  simp [shiftBriberyBordaDec, h]

/-- Shifting candidate `2` up one place in both votes, at price one each, ties all three
candidates at two Borda points. -/
example :
    shiftBriberyBordaDec
      (bitEncode ((3, 2, [([0, 1, 2], [1, 3]), ([1, 0, 2], [1, 3])], 2) :
        ShiftBriberyBordaInstance)) = true := by
  apply (accepts_encoding _).2
  refine ⟨by unfold WellFormed IsVote; decide, fun _ => 1, by decide, by decide, by decide⟩

/-- With budget one, at most one vote moves candidate `2` up one place, and then the
unbribed vote's top candidate still outscores it. -/
example :
    shiftBriberyBordaDec
      (bitEncode ((3, 2, [([0, 1, 2], [1, 3]), ([1, 0, 2], [1, 3])], 1) :
        ShiftBriberyBordaInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨k, hk, hcost, hwin⟩ := ((accepts_encoding _).1 h).2
  have hk' : k = ![k 0, k 1] := funext fun i => by fin_cases i <;> rfl
  have ha : k 0 ≤ 2 := hk 0
  have hb : k 1 ≤ 2 := hk 1
  generalize k 0 = a at hk' ha
  generalize k 1 = b at hk' hb
  subst hk'
  revert hcost hwin
  rcases (by omega : a = 0 ∨ a = 1 ∨ a = 2) with rfl | rfl | rfl <;>
  rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2) with rfl | rfl | rfl <;>
  decide

/-- Prices that decrease with the shift are malformed. -/
example :
    shiftBriberyBordaDec
      (bitEncode ((3, 2, [([0, 1, 2], [3, 1])], 5) : ShiftBriberyBordaInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  have hw := ((accepts_encoding _).1 h).1
  revert hw
  unfold WellFormed IsVote
  decide

end MetaMathlibExt.Complexity.NPComplete.ShiftBriberyBorda
