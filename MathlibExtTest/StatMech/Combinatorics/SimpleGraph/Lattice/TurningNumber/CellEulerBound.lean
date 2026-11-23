/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.CellEulerBound

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.CellEulerBound`

Non-vacuity of the Euler bound `eulerChar_le_one`: its connectivity hypothesis (the open-top
skeleton, the 1-skeleton without top edges, is connected) is proved for a domino, and the bound is
compared with the computed value `eulerChar = 1`. Also checks `eulerChar_eq_regChi` and
`card_topEdges` on the domino, and that the annulus of eight cells has `eulerChar = 0`.
-/

@[expose] public section

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.TurningNumber.CellEulerBound

open Finset _root_.SimpleGraph StatMech.CellEulerChar StatMech.Onsager.CellEuler
  StatMech.Onsager.CellEulerBound

/-- A horizontal domino: two side-by-side cells. -/
abbrev domino : Finset (ℤ × ℤ) := {(0, 0), (1, 0)}

/-- The vertex `(a, b)` of the domino, as a vertex of its open-top skeleton. -/
abbrev dv (a b : ℤ) (h : (a, b) ∈ regVerts domino := by decide) : {v // v ∈ regVerts domino} :=
  ⟨(a, b), h⟩

/-- The open-top skeleton of a domino is connected: its edges form the tree
  `(0,1) - (0,0) - (1,0) - (2,0) - (2,1)` with `(1,1)` attached to `(1,0)`. -/
theorem domino_openTopSkeleton_connected : (openTopSkeleton domino).Connected := by
  have a1 : (openTopSkeleton domino).Adj (dv 0 0) (dv 1 0) := by change s(_, _) ∈ _; decide
  have a2 : (openTopSkeleton domino).Adj (dv 1 0) (dv 2 0) := by change s(_, _) ∈ _; decide
  have a3 : (openTopSkeleton domino).Adj (dv 0 0) (dv 0 1) := by change s(_, _) ∈ _; decide
  have a4 : (openTopSkeleton domino).Adj (dv 1 0) (dv 1 1) := by change s(_, _) ∈ _; decide
  have a5 : (openTopSkeleton domino).Adj (dv 2 0) (dv 2 1) := by change s(_, _) ∈ _; decide
  have hv : ∀ v, (openTopSkeleton domino).Reachable (dv 0 0) v := by
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

-- Non-vacuity of `eulerChar_le_one` on the domino.
example : eulerChar domino ≤ 1 := eulerChar_le_one domino domino_openTopSkeleton_connected

-- The bound is attained: the domino has Euler characteristic exactly `1`.
example : eulerChar domino = 1 := by decide

-- `eulerChar` agrees with `regChi`, both computed.
example : regChi domino = 1 := by rw [← eulerChar_eq_regChi]; decide

-- Each cell contributes one top edge.
example : (topEdges domino).card = 2 := card_topEdges domino

-- The open-top skeleton has one edge fewer than vertices (it is a tree).
example : (regVerts domino).card = 6 ∧ (regEdges domino \ topEdges domino).card = 5 := by decide

-- An annulus has Euler characteristic `0 < 1`, so the bound is not an equality in general.
example : eulerChar ({(0, 0), (1, 0), (2, 0), (0, 1), (2, 1), (0, 2), (1, 2), (2, 2)} :
    Finset (ℤ × ℤ)) = 0 := by
  decide

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.TurningNumber.CellEulerBound
