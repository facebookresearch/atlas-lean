/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import MathlibExt.GameTheory.PenultsOfTak.LargestPenult
import MathlibExt.GameTheory.PenultsOfTak.VariableDiamond
import MathlibExt.GameTheory.PenultsOfTak.WeightedCrossBound

namespace MetaMathlibExt

-- On the smallest board in the theorem's range, the bound already excludes the empty board.
example : ¬ placementPenult takHasRoad (∅ : Finset (Fin 5 × Fin 5)) := by
  intro h
  have hbound := impartialTak_penult_card_ge_weightedCross (by decide) h
  simp at hbound

-- On a 13 × 13 board the rational lower bound rounds up to 22 tokens.
example {S : Finset (Fin 13 × Fin 13)} (hS : placementPenult takHasRoad S) : 22 ≤ S.card := by
  have hbound := impartialTak_penult_card_ge_weightedCross (by decide) hS
  omega

-- The same constant works both below the weighted bound's range and on a larger board.
example :
    ∃ C : ℝ,
      (∀ S : Finset (Fin 4 × Fin 4), placementPenult takHasRoad S →
        (4 : ℝ) ^ 2 / 4 - C * 4 ≤ S.card) ∧
      (∀ S : Finset (Fin 16 × Fin 16), placementPenult takHasRoad S →
        (16 : ℝ) ^ 2 / 4 - C * 16 ≤ S.card) := by
  obtain ⟨C, hC⟩ := impartialTak_penult_card_ge_quarter
  exact ⟨C, hC 4, hC 16⟩

private abbrev SixCell := Fin 6 × Fin 6

private abbrev inWindow (p : SixCell) : Prop :=
  1 ≤ p.1.val ∧ p.1.val < 1 + 5 ∧ 1 ≤ p.2.val ∧ p.2.val < 1 + 5

private def cost (p : SixCell) : ℕ := weightedCrossWeight (p.1.val - 1) (p.2.val - 1)

private def paid : Finset SixCell := Finset.univ.filter fun p => inWindow p ∧ 1 ≤ cost p

-- Check the lower bound independently on a nonempty class of penults: on a 6 × 6 board with
-- 24 tokens, at most 15 are outside the translated window or on its zero-weight corners.
example : ∃ S : Finset SixCell, placementPenult takHasRoad S ∧ S.card = 24 ∧
    9 ≤ ∑ p ∈ S.filter inWindow, cost p := by
  obtain ⟨S, hS, hcard⟩ := impartialTak_exists_penult_card (n := 6) (x := 24)
    (by decide) (by decide) (by decide)
  have hbad : (Finset.univ \ paid).card = 15 := by decide
  have hmiss : (S \ paid).card ≤ 15 := hbad ▸ Finset.card_le_card (fun p hp =>
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ p, (Finset.mem_sdiff.mp hp).2⟩)
  have hpartition := Finset.card_sdiff_add_card_inter S paid
  refine ⟨S, hS, hcard, (show 9 ≤ (S ∩ paid).card by omega).trans ?_⟩
  calc
    (S ∩ paid).card = ∑ _p ∈ S ∩ paid, (1 : ℕ) := by simp
    _ ≤ ∑ p ∈ S ∩ paid, cost p := Finset.sum_le_sum fun p hp =>
      ((Finset.mem_filter.mp (Finset.mem_inter.mp hp).2).2).2
    _ ≤ ∑ p ∈ S.filter inWindow, cost p := Finset.sum_le_sum_of_subset fun p hp =>
      Finset.mem_filter.mpr ⟨(Finset.mem_inter.mp hp).1,
        ((Finset.mem_filter.mp (Finset.mem_inter.mp hp).2).2).1⟩

-- As a client, apply the theorem on that same translated window.
example : ∃ S : Finset SixCell, placementPenult takHasRoad S ∧ S.card = 24 ∧
    7 ≤ ∑ p ∈ S.filter inWindow, cost p := by
  obtain ⟨S, hS, hcard⟩ := impartialTak_exists_penult_card (n := 6) (x := 24)
    (by decide) (by decide) (by decide)
  exact ⟨S, hS, hcard, impartialTak_penult_weightedCross (r := 1) (c := 1) hS
    (by decide) (by decide)⟩

private def cutSide : Finset SixCell := {(0, 3), (3, 0), (1, 1), (1, 5), (5, 1), (5, 5)}

private def sparse : Finset SixCell := cutSide ∪ {(2, 2), (2, 4), (4, 2), (4, 4), (3, 3)}

-- Weight six: outside tokens and corners contribute nothing. The centre token's component
-- is separated from the occupied board edge, and the hole at (2, 3) does not bridge the cut.
example : (∑ p ∈ sparse.filter inWindow, cost p) = 6 ∧ ¬ placementPenult takHasRoad sparse := by
  refine ⟨by decide, not_takPenult_of_cut (p := (2, 3)) (A := (cutSide : Set SixCell))
    (by decide) (by decide) ?_ ?_⟩
  · have h : ∀ x ∈ insert ((2, 3) : SixCell) sparse,
        x.1.val = 0 ∨ x.1.val + 1 = 6 ∨ x.2.val = 0 ∨ x.2.val + 1 = 6 → x ∈ cutSide := by decide
    exact h
  · simp only [takAdjacent_iff_dist_eq_one]
    have h : ∀ x ∈ cutSide, ∀ y ∈ insert ((2, 3) : SixCell) sparse,
        Nat.dist x.1.val y.1.val + Nat.dist x.2.val y.2.val = 1 → y ∈ cutSide := by decide
    exact h

-- Independently rule out a cut example on a 3 × 3 board: the four corners do not touch
-- the centre, and a penult on this board can have at most three tokens.
example : ¬ placementPenult takHasRoad
    ({(0, 0), (0, 2), (2, 0), (2, 2)} : Finset (Fin 3 × Fin 3)) := by
  intro h
  have hcard : 4 ∈ {k | ∃ S : Finset (Fin 3 × Fin 3), placementPenult takHasRoad S ∧ S.card = k} :=
    ⟨_, h, by decide⟩
  have hmax := impartialTak_isGreatest_penult_card (by decide : 2 ≤ 3)
  exact (by decide : ¬ (4 : ℕ) ≤ 3) (hmax.2 hcard)

end MetaMathlibExt
