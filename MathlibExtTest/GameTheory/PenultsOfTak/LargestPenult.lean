/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GameTheory.PenultsOfTak.LargestPenult

namespace MetaMathlibExt

-- At the lower endpoint the empty board is the unique penult.
example (S : Finset (Fin 2 × Fin 2)) : placementPenult takHasRoad S ↔ S = ∅ := by
  have h := impartialTak_isGreatest_penult_card (n := 2) (by decide)
  constructor
  · intro hS
    have bound := h.2 ⟨S, hS, rfl⟩
    exact Finset.card_eq_zero.mp (by omega)
  · rintro rfl
    obtain ⟨T, hT, hcard⟩ := h.1
    have := Finset.card_eq_zero.mp (show T.card = 0 from hcard)
    simpa [this] using hT

-- The first positive maximum is attained on the three-by-three board.
example : ∃ S : Finset (Fin 3 × Fin 3), placementPenult takHasRoad S ∧ S.card = 3 :=
  (impartialTak_isGreatest_penult_card (n := 3) (by decide)).1

end MetaMathlibExt
