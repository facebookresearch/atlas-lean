/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.CombinatorialAuctionWinnerDeterminationDefs

namespace MetaMathlibExt.Complexity.NPComplete.CombinatorialAuctionWinnerDetermination

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : CombinatorialAuctionWinnerDeterminationInstance) :
    combinatorialAuctionWinnerDeterminationDec (bitEncode i) = true ↔
      WellFormed i ∧ CombinatorialAuctionWinnerDeterminationFeasible i := by
  simp [combinatorialAuctionWinnerDeterminationDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : combinatorialAuctionWinnerDeterminationDec [true] = false := by
  have h : bitDecode (α := CombinatorialAuctionWinnerDeterminationInstance) [true] = none := rfl
  simp [combinatorialAuctionWinnerDeterminationDec, h]

/-- The bid set used by both fixtures: three items, bids `{0, 1}` for `5`, `{1, 2}` for `4` and
`{2}` for `3`. -/
private abbrev bids : List (List ℕ × ℕ) := [([0, 1], 5), ([1, 2], 4), ([2], 3)]

/-- The disjoint bids `{0, 1}` and `{2}` raise `8`. -/
example : combinatorialAuctionWinnerDeterminationDec (bitEncode
    ((3, bids, 8) : CombinatorialAuctionWinnerDeterminationInstance)) = true := by
  refine (accepts_encoding _).2 ⟨by unfold WellFormed; decide, {0, 2}, ?_, by decide⟩
  intro a ha b hb hab
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> first | exact absurd rfl hab | decide

/-- No set of pairwise disjoint bids raises `9`: the best is `5 + 3 = 8`. -/
example : combinatorialAuctionWinnerDeterminationDec (bitEncode
    ((3, bids, 9) : CombinatorialAuctionWinnerDeterminationInstance)) = false := by
  rw [Bool.eq_false_iff, Ne, accepts_encoding]
  rintro ⟨-, W, hW, hK⟩
  have key : ∀ W : Finset (Fin 3),
      (∀ a ∈ W, ∀ b ∈ W, a ≠ b → Disjoint (bids.get a).1.toFinset (bids.get b).1.toFinset) →
        ∑ j ∈ W, (bids.get j).2 < 9 := by decide
  exact absurd hK (Nat.not_le.2 (key W fun a ha b hb hab => hW ha hb hab))

end MetaMathlibExt.Complexity.NPComplete.CombinatorialAuctionWinnerDetermination
