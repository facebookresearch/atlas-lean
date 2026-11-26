/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GameTheory.PenultsOfTakImpartialTakNotFirstPlayerWinsOfEven

/-!
# Tests for Impartial Tak on even boards

The empty zero board is a P-position, and every first move on the `2 × 2` board leaves a winning
position for the next player.

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda,
*The Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Proposition 2.
-/

namespace MathlibExtTest.GameTheory.PenultsOfTakImpartialTakNotFirstPlayerWinsOfEven

open MetaMathlibExt

example : SpragueGrundy.IsP (placementGame (Fin 0 × Fin 0) takHasRoad) ∅ := by
  simpa only [placementFirstPlayerWins, not_not] using
    impartialTak_not_firstPlayerWins_of_even (n := 0) ⟨0, rfl⟩

example (p : Fin 2 × Fin 2) : placementFirstPlayerWins takHasRoad {p} := by
  by_contra h
  apply impartialTak_not_firstPlayerWins_of_even (n := 2) ⟨1, rfl⟩
  exact (placementFirstPlayerWins_iff takHasRoad ∅).mpr
    ⟨not_takHasRoad_empty, p, by simp, by simpa using h⟩

end MathlibExtTest.GameTheory.PenultsOfTakImpartialTakNotFirstPlayerWinsOfEven
