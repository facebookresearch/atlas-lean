/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

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

end MetaMathlibExt
