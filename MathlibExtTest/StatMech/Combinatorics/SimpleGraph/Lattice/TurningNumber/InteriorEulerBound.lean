/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.InteriorEulerBound

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.CellEulerFaithful`

Non-vacuity of `eulerChar_le_one_of_skeleton_connected`: the 1-skeleton of a domino is proved
connected and the bound is compared with the computed `eulerChar = 1`. The walk-level bound
`eulerChar_interiorCells_le_one` is instantiated on the counterclockwise unit square walk
`![0, 1, 2, 3]` (`m = 1`), whose hypotheses are proved by `decide`.
-/

@[expose] public section

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.TurningNumber.CellEulerFaithful

open Finset _root_.SimpleGraph StatMech.CellEulerChar StatMech.Onsager.BaseCase StatMech.Onsager.CellEuler
  StatMech.Onsager.CellEulerFaithful

/-- A horizontal domino: two side-by-side cells. -/
abbrev domino : Finset (ℤ × ℤ) := {(0, 0), (1, 0)}

/-- The vertex `(a, b)` of the domino, as a vertex of its skeleton. -/
abbrev dv (a b : ℤ) (h : (a, b) ∈ regVerts domino := by decide) : {v // v ∈ regVerts domino} :=
  ⟨(a, b), h⟩

/-- The 1-skeleton of a domino is connected. -/
theorem domino_cellSkeleton_connected : (cellSkeleton domino).Connected := by
  have a1 : (cellSkeleton domino).Adj (dv 0 0) (dv 1 0) := by change s(_, _) ∈ _; decide
  have a2 : (cellSkeleton domino).Adj (dv 1 0) (dv 2 0) := by change s(_, _) ∈ _; decide
  have a3 : (cellSkeleton domino).Adj (dv 0 0) (dv 0 1) := by change s(_, _) ∈ _; decide
  have a4 : (cellSkeleton domino).Adj (dv 1 0) (dv 1 1) := by change s(_, _) ∈ _; decide
  have a5 : (cellSkeleton domino).Adj (dv 2 0) (dv 2 1) := by change s(_, _) ∈ _; decide
  have hv : ∀ v, (cellSkeleton domino).Reachable (dv 0 0) v := by
    rintro ⟨v, hv⟩
    have : v = (0, 0) ∨ v = (1, 0) ∨ v = (0, 1) ∨ v = (1, 1) ∨ v = (2, 0) ∨ v = (2, 1) := by
      have e : regVerts domino = {(0, 0), (1, 0), (0, 1), (1, 1), (2, 0), (2, 1)} := by decide
      rw [e] at hv
      simpa using hv
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl
    · rfl
    · exact a1.reachable
    · exact a3.reachable
    · exact a1.reachable.trans a4.reachable
    · exact a1.reachable.trans a2.reachable
    · exact (a1.reachable.trans a2.reachable).trans a5.reachable
  have : Nonempty {v // v ∈ regVerts domino} := ⟨dv 0 0⟩
  exact ⟨fun a b => (hv a).symm.trans (hv b)⟩

-- Non-vacuity of `eulerChar_le_one_of_skeleton_connected` on the domino.
example : eulerChar domino ≤ 1 :=
  eulerChar_le_one_of_skeleton_connected domino domino_cellSkeleton_connected

-- The computed value attains the bound.
example : eulerChar domino = 1 := by decide

/-- The counterclockwise unit square walk: east, north, west, south. -/
def square : Fin (1 + 3) → Fin 4 := ![0, 1, 2, 3]

theorem square_closed : ∑ i, stepOf (square i) = 0 := by decide

theorem square_simple : Function.Injective (pos square) := by decide

theorem square_reflexfree :
    ∀ i : Fin (1 + 3), square (i + 1) - square i = 0 ∨ square (i + 1) - square i = 1 := by
  decide

-- Non-vacuity of `eulerChar_interiorCells_le_one` on the unit square walk.
example :
    eulerChar (StatMech.Onsager.WalkCellRegion.interiorCells square square_closed square_simple
      square_reflexfree) ≤ 1 :=
  eulerChar_interiorCells_le_one square square_closed square_simple square_reflexfree

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.TurningNumber.CellEulerFaithful
