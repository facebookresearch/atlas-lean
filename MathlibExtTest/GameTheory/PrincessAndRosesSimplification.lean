/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GameTheory.PrincessAndRosesSimplification

open MetaMathlibExt MetaMathlibExt.SpragueGrundy

-- Shifting the empty board leaves no legal simplified move, for any shift.
example (n : ℕ) : simplifiedPrincessRosesMoves (n, n, n, 0) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  rintro ⟨a, b, c, d⟩ h
  obtain ⟨ha, hb, hc, hd, hba, hcb, _, hm⟩ := mem_simplifiedPrincessRosesMoves.mp h
  have hmask : ∀ m ∈ simplifiedPrincessRosesMoveList,
      m.2.2.2 = 0 → m.2.2.1 = 0 ∧ (m.1 = 1 ∨ m.2.1 = 1) := by decide
  have hzero : 0 - d = 0 := Nat.zero_sub d
  have := hmask _ hm hzero
  change n - c = 0 ∧ (n - a = 1 ∨ n - b = 1) at this
  omega

-- Ties at the bottom do not prevent shifting the three largest piles.
example : Equiv (princessRoses ![2, 1, 1, 1]) (simplifiedPrincessRoses (4, 3, 3, 1)) :=
  princessRoses_equiv_simplifiedPrincessRoses 2 1 1 1 2 (by decide) le_rfl le_rfl

-- Even with four distinct piles, the ordinary game has moves the simplified game forbids.
example : ![4, 3, 1, 1] ∈ (princessRoses ![4, 3, 2, 1]).moves ![4, 3, 2, 1] := by
  apply mem_slowANimGame_moves_one_two_iff.mpr
  decide

example : (4, 3, 1, 1) ∉ simplifiedPrincessRosesMoves (4, 3, 2, 1) := by
  decide

-- The simplified game permits taking from the third and fourth piles together.
example : (4, 3, 1, 0) ∈ simplifiedPrincessRosesMoves (4, 3, 2, 1) := by
  decide

example : Equiv (princessRoses ![4, 3, 2, 1]) (simplifiedPrincessRoses (5, 4, 3, 1)) :=
  princessRoses_equiv_simplifiedPrincessRoses 4 3 2 1 1 (by decide) (by decide) (by decide)
