/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.ChamberlinCourantWinnerDeterminationDefs

namespace MetaMathlibExt.Complexity.NPComplete.ChamberlinCourantWinnerDetermination

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : ChamberlinCourantWinnerDeterminationInstance) :
    chamberlinCourantWinnerDeterminationDec (bitEncode i) = true ↔
      WellFormed i ∧ ChamberlinCourantWinnerDeterminationFeasible i := by
  simp [chamberlinCourantWinnerDeterminationDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : chamberlinCourantWinnerDeterminationDec [true] = false := by
  have h : bitDecode (α := ChamberlinCourantWinnerDeterminationInstance) [true] = none := rfl
  simp [chamberlinCourantWinnerDeterminationDec, h]

/-- Two opposite votes over three candidates. -/
private abbrev votes : List (List ℕ) := [[0, 1, 2], [2, 1, 0]]

/-- The committee `{0, 2}` gives each voter its top choice, with misrepresentation `0`. -/
example : chamberlinCourantWinnerDeterminationDec (bitEncode
    ((3, votes, 2, 0) : ChamberlinCourantWinnerDeterminationInstance)) = true := by
  refine (accepts_encoding _).2 ⟨by unfold WellFormed; decide, {0, 2}, by decide, ![0, 2],
    by decide, by decide⟩

private theorem single_rep_cost : ∀ r : Fin 2 → Fin 3, r 0 = r 1 →
    1 < ∑ j : Fin 2, votes[j].idxOf (r j : ℕ) := by
  decide

/-- With a single representative every candidate has total Borda misrepresentation `2` over
the two opposite votes, so the bound `1` is unattainable. -/
example : chamberlinCourantWinnerDeterminationDec (bitEncode
    ((3, votes, 1, 1) : ChamberlinCourantWinnerDeterminationInstance)) = false := by
  rw [Bool.eq_false_iff, Ne, accepts_encoding]
  rintro ⟨-, W, hW, r, hr, hB⟩
  have h01 : r 0 = r 1 := Finset.card_le_one.1 hW.le _ (hr 0) _ (hr 1)
  exact absurd hB (Nat.not_le.2 (single_rep_cost r h01))

end MetaMathlibExt.Complexity.NPComplete.ChamberlinCourantWinnerDetermination
