/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.CellPinch

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.CellPinch`

Computes `pinchAt`, `pinchW` and `pinchCount` on a domino (no pinch point), two diagonally touching
cells (one pinch point, at `(1, 1)`), and the annulus of eight cells (none).
-/

@[expose] public section

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.TurningNumber.CellPinch

open StatMech.Onsager.CellPinch

/-- A horizontal domino: two side-by-side cells. -/
def domino : Finset (ℤ × ℤ) := {(0, 0), (1, 0)}

/-- Two cells touching only at the corner `(1, 1)`. -/
def diag : Finset (ℤ × ℤ) := {(0, 0), (1, 1)}

/-- An L-shaped tromino. -/
def tromino : Finset (ℤ × ℤ) := {(0, 0), (1, 0), (0, 1)}

/-- The eight cells around the centre cell `(1, 1)`: an annulus with one hole. -/
def ring8 : Finset (ℤ × ℤ) := {(0, 0), (1, 0), (2, 0), (0, 1), (2, 1), (0, 2), (1, 2), (2, 2)}

-- Two diagonally touching cells pinch at their common corner.
example : pinchAt diag (1, 1) := by decide
example : pinchW diag (1, 1) = 1 := by decide
example : pinchCount diag = 1 := by decide

-- The other diagonal orientation also pinches.
example : pinchCount {((1 : ℤ), (0 : ℤ)), (0, 1)} = 1 := by decide

-- A domino and the annulus have no pinch points.
example : pinchCount domino = 0 ∧ pinchCount ring8 = 0 := by decide

-- `pinchW` vanishes off the vertex set (`pinchW_zero_of_notMem`).
example : pinchW diag (7, 7) = 0 := pinchW_zero_of_notMem diag (7, 7) (by decide)

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.TurningNumber.CellPinch
