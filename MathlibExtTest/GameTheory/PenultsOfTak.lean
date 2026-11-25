/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GameTheory.PenultsOfTak

namespace MetaMathlibExt

-- The first row and column have just their common corner occupied. In the remaining
-- three-by-three square, occupy the six off-diagonal cells. This attains the bound.
example : ∃ S : Finset (Fin 4 × Fin 4),
    placementPenult (ticEnded 4) S ∧ (Finset.univ \ S).card = 9 := by
  refine ⟨{(0, 0), (1, 2), (1, 3), (2, 1), (2, 3), (3, 1), (3, 2)}, ?_, ?_⟩
  · let decTerminal (T : Finset (Fin 4 × Fin 4)) :
        Decidable (placementTerminal (ticEnded 4) T) := by
      unfold placementTerminal ticEnded
      infer_instance
    unfold placementPenult placementUlt
    decide
  · decide

-- A board with one fewer occupied cell cannot be a penult.
example (S : Finset (Fin 4 × Fin 4)) (h : S.card = 6) : ¬ placementPenult (ticEnded 4) S := by
  intro hS
  have hbound := impartialTic_dual_penult_card_le_of_four hS
  simp [Finset.card_sdiff_of_subset (Finset.subset_univ S), h] at hbound

end MetaMathlibExt
