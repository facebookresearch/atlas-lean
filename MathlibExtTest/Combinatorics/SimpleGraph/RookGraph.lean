/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SimpleGraph.RookGraph

namespace SimpleGraph

/-- Distinct cells in the same row are adjacent in the rook graph. -/
example : (rookGraph 2 2).Adj (0, 0) (0, 1) := by
  exact ⟨by decide, Or.inl rfl⟩

/-- Cells differing in both coordinates are not adjacent. -/
example : ¬(rookGraph 2 2).Adj (0, 0) (1, 1) := by
  rintro ⟨-, h | h⟩ <;> exact absurd h (by decide)

/-- The coordinate characterization of rook-graph domination. -/
example {n m : ℕ} {s : Finset (Fin n × Fin m)} :
    (rookGraph n m).IsDominating ↑s ↔
      ∀ i : Fin n, ∀ j : Fin m,
        (∃ j' : Fin m, (i, j') ∈ s) ∨ ∃ i' : Fin n, (i', j) ∈ s :=
  rookGraph_isDominating_iff

/-- A single full row dominates the rook graph. -/
example : (rookGraph 2 3).IsDominating
    ↑({(0, 0), (0, 1), (0, 2)} : Finset (Fin 2 × Fin 3)) :=
  rookGraph_isDominating_iff_or.2 (Or.inr (by decide))

/-- Two cells in one row of the `3 × 3` board meet neither every row nor
every column, so they do not dominate. -/
example : ¬(rookGraph 3 3).IsDominating
    ↑({(0, 0), (0, 1)} : Finset (Fin 3 × Fin 3)) := by
  rw [rookGraph_isDominating_iff_or]
  decide

end SimpleGraph
