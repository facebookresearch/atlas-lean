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

private def middleRow : Finset (Fin 3 × Fin 3) := {(1, 0), (1, 1), (1, 2)}

-- Check the road directly: both endpoints are occupied and the two steps stay on the row.
example : ∃ a ∈ middleRow, ∃ b ∈ middleRow, a.2.val = 0 ∧ b.2.val = 2 ∧
    Relation.ReflTransGen (fun x y => takAdjacent x y ∧ y ∈ middleRow) a b := by
  refine ⟨(1, 0), by decide, (1, 2), by decide, rfl, rfl, ?_⟩
  have firstStep : takAdjacent ((1, 0) : Fin 3 × Fin 3) (1, 1) :=
    takAdjacent_iff_dist_eq_one.mpr (by decide)
  have lastStep : takAdjacent ((1, 1) : Fin 3 × Fin 3) (1, 2) :=
    takAdjacent_iff_dist_eq_one.mpr (by decide)
  exact (Relation.ReflTransGen.single ⟨firstStep, by decide⟩).tail ⟨lastStep, by decide⟩

-- The same board is a client of the full-row API, re-exported by LargestPenult.
example : takHasRoad middleRow :=
  impartialTak_isGreatest_penult_card.road_of_full_row 1 (by decide)

end MetaMathlibExt
