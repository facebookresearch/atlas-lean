/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GameTheory.PenultsOfTak.CrossNonempty

namespace MetaMathlibExt

-- On the smallest board with an interior cell, if the center is empty,
-- a penult contains an orthogonal neighbor of the center.
example {S : Finset (Fin 3 × Fin 3)} (hS : placementPenult takHasRoad S)
    (hc : ((1, 1) : Fin 3 × Fin 3) ∉ S) : ∃ p ∈ S, takAdjacent p (1, 1) := by
  obtain ⟨p, hp, h⟩ := impartialTak_penult_cross_nonempty hS (1, 1)
    (by decide) (by decide) (by decide) (by decide)
  exact ⟨p, hp, h.resolve_left (fun e => hc (e ▸ hp))⟩

-- All four corners of a 3 × 3 board lie outside the center's Cross.
example : ¬ placementPenult takHasRoad ({(0, 0), (0, 2), (2, 0), (2, 2)} :
    Finset (Fin 3 × Fin 3)) := by
  intro hS
  obtain ⟨p, hp, h⟩ := impartialTak_penult_cross_nonempty hS (1, 1)
    (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> (revert h; unfold takAdjacent; decide)

end MetaMathlibExt
