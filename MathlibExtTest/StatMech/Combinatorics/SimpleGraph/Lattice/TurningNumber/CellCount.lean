/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.CellCount

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.CellCount`

Computes `cornersOf`, `cornerCount` and `cellVerts` on a domino and an L-tromino, and instantiates
the double-counting identity `sum_cornerCount` and the bound `cornerCount_le_four` on them.
-/

@[expose] public section

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.TurningNumber.CellCount

open StatMech.Onsager.CellCount

/-- A horizontal domino: two side-by-side cells. -/
def domino : Finset (ℤ × ℤ) := {(0, 0), (1, 0)}

/-- Two cells touching only at the corner `(1, 1)`. -/
def diag : Finset (ℤ × ℤ) := {(0, 0), (1, 1)}

/-- An L-shaped tromino. -/
def tromino : Finset (ℤ × ℤ) := {(0, 0), (1, 0), (0, 1)}

/-- The eight cells around the centre cell `(1, 1)`: an annulus with one hole. -/
def ring8 : Finset (ℤ × ℤ) := {(0, 0), (1, 0), (2, 0), (0, 1), (2, 1), (0, 2), (1, 2), (2, 2)}

-- The corners of the cell at the origin.
example : cornersOf (0, 0) = {(0, 0), (1, 0), (0, 1), (1, 1)} := rfl

-- A domino has six vertices; the two middle ones are shared.
example : (cellVerts domino).card = 6 := by decide

-- Corner counts on a domino: `1` at an outer corner, `2` on the shared edge, `0` away from it.
example : cornerCount domino (0, 0) = 1 ∧ cornerCount domino (1, 0) = 2 ∧
    cornerCount domino (5, 5) = 0 := by
  decide

-- The reflex corner of the L-tromino has three incident cells.
example : cornerCount tromino (1, 1) = 3 := by decide

-- Double counting on the tromino: `∑ cornerCount = 4 * 3`, checked by computation.
example : ∑ v ∈ cellVerts tromino, cornerCount tromino v = 12 := by decide

-- The same via `sum_cornerCount`.
example : ∑ v ∈ cellVerts tromino, cornerCount tromino v = 4 * tromino.card :=
  sum_cornerCount tromino

-- The bound `cornerCount_le_four` is attained at the centre of a `2 × 2` block.
example : cornerCount {(0, 0), (1, 0), (0, 1), (1, 1)} (1, 1) = 4 := by decide

-- `cornerCount_le_four` on the annulus, where only three cells meet at `(1, 1)`.
example : cornerCount ring8 (1, 1) = 3 := by decide

example : cornerCount ring8 (1, 1) ≤ 4 := cornerCount_le_four ring8 (1, 1)

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.TurningNumber.CellCount
