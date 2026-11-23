/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.CellEuler

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.CellEuler`

Computes the corner defect `cornerDiff` and the Euler characteristic `eulerChar` on a domino, an
L-tromino and an annulus of eight cells, and instantiates `cornerDiff_singleton`,
`eulerChar_singleton` and the insertion formulas `eulerChar_insert` and `cornerDiff_insert`.
-/

@[expose] public section

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.TurningNumber.CellEuler

open StatMech.Onsager.CellCount StatMech.Onsager.CellEuler

/-- A horizontal domino: two side-by-side cells. -/
def domino : Finset (ℤ × ℤ) := {(0, 0), (1, 0)}

/-- Two cells touching only at the corner `(1, 1)`. -/
def diag : Finset (ℤ × ℤ) := {(0, 0), (1, 1)}

/-- An L-shaped tromino. -/
def tromino : Finset (ℤ × ℤ) := {(0, 0), (1, 0), (0, 1)}

/-- The eight cells around the centre cell `(1, 1)`: an annulus with one hole. -/
def ring8 : Finset (ℤ × ℤ) := {(0, 0), (1, 0), (2, 0), (0, 1), (2, 1), (0, 2), (1, 2), (2, 2)}

-- A single cell: corner defect `4`, Euler characteristic `1`.
example : cornerDiff {((3 : ℤ), (-2 : ℤ))} = 4 := cornerDiff_singleton _
example : eulerChar {((3 : ℤ), (-2 : ℤ))} = 1 := eulerChar_singleton _

-- A domino: `V - E + F = 6 - 7 + 2 = 1`, four convex corners.
example : (cellEdges domino).card = 7 ∧ eulerChar domino = 1 ∧ cornerDiff domino = 4 := by
  decide

-- The L-tromino: five convex corners and one reflex corner.
example : cornerDiff tromino = 4 ∧ eulerChar tromino = 1 := by decide

-- The annulus has Euler characteristic `0` and corner defect `0` (outer `+4`, hole `-4`).
example : eulerChar ring8 = 0 ∧ cornerDiff ring8 = 0 := by decide

-- `cornerWeight` at one, two and three incident cells.
example : cornerWeight 1 = 1 ∧ cornerWeight 2 = 0 ∧ cornerWeight 3 = -1 := by decide

-- `eulerChar_insert`: adding `(1, 0)` to `{(0, 0)}` adds two vertices and three edges.
example : eulerChar (insert (1, 0) {((0 : ℤ), (0 : ℤ))}) = 1 := by
  rw [eulerChar_insert _ _ (by decide), eulerChar_singleton]
  decide

-- `cornerDiff_insert` on the same step: the defect stays `4`.
example : cornerDiff (insert (1, 0) {((0 : ℤ), (0 : ℤ))}) = 4 := by
  rw [cornerDiff_insert _ _ (by decide), cornerDiff_singleton]
  decide

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.TurningNumber.CellEuler
