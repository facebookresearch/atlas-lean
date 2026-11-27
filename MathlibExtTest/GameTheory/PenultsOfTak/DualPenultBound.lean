/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GameTheory.PenultsOfTak.DualPenultBound

namespace MetaMathlibExt

-- On the five-by-five board the bound is twelve empty cells: every penult
-- has at least thirteen tokens.
example (S : Finset (Fin 5 × Fin 5)) (hS : placementPenult (ticEnded 5) S) :
    13 ≤ S.card := by
  have hbound := impartialTic_dual_penult_card_le (n := 5) (le_refl 5) hS
  have hcard : (Finset.univ \ S).card = 25 - S.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ S)]
    simp
  omega

-- In general, a penult on an `n × n` board with `n ≥ 5` has at least
-- `n ^ 2 - 4 * (n - 2)` tokens.
example {n : ℕ} (hn : 5 ≤ n) (S : Finset (Fin n × Fin n))
    (hS : placementPenult (ticEnded n) S) : n ^ 2 - 4 * (n - 2) ≤ S.card := by
  have hbound := impartialTic_dual_penult_card_le hn hS
  have hcard : (Finset.univ \ S).card = n ^ 2 - S.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ S)]
    simp [sq]
  omega

end MetaMathlibExt
