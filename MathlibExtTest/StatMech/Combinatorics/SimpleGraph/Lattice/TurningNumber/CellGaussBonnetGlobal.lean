/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.CellGaussBonnet

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.CellGaussBonnetGlobal`

Instantiates the cell Gauss–Bonnet formula `cornerDiff_eq`
(`cornerDiff S = 4 * eulerChar S + 2 * pinchCount S`) on two diagonally touching cells (where the
pinch term is needed: `6 = 4 * 1 + 2 * 1`), an L-tromino (`4 = 4 * 1 + 0`) and an annulus of eight
cells (`0 = 4 * 0 + 0`), and checks each side by direct computation.
-/

@[expose] public section

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.TurningNumber

namespace CellGaussBonnetGlobal

open StatMech.Onsager.CellCount StatMech.Onsager.CellEuler StatMech.Onsager.CellPinch
  StatMech.Onsager.CellGaussBonnetGlobal

/-- A horizontal domino: two side-by-side cells. -/
def domino : Finset (ℤ × ℤ) := {(0, 0), (1, 0)}

/-- Two cells touching only at the corner `(1, 1)`. -/
def diag : Finset (ℤ × ℤ) := {(0, 0), (1, 1)}

/-- An L-shaped tromino. -/
def tromino : Finset (ℤ × ℤ) := {(0, 0), (1, 0), (0, 1)}

/-- The eight cells around the centre cell `(1, 1)`: an annulus with one hole. -/
def ring8 : Finset (ℤ × ℤ) := {(0, 0), (1, 0), (2, 0), (0, 1), (2, 1), (0, 2), (1, 2), (2, 2)}

-- Direct computation on the diagonal pair: `6 = 4 * 1 + 2 * 1`.
example : cornerDiff diag = 6 ∧ eulerChar diag = 1 ∧ pinchCount diag = 1 := by decide

-- `cornerDiff_eq` on the diagonal pair, from which the pinch count is derived.
example : pinchCount diag = 1 := by
  have h := cornerDiff_eq diag
  have h1 : cornerDiff diag = 6 := by decide
  have h2 : eulerChar diag = 1 := by decide
  omega

-- `cornerDiff_eq` on the L-tromino and its direct check.
example : cornerDiff tromino = 4 * eulerChar tromino + 2 * pinchCount tromino :=
  cornerDiff_eq tromino
example : cornerDiff tromino = 4 ∧ eulerChar tromino = 1 ∧ pinchCount tromino = 0 := by decide

-- `cornerDiff_eq` on the annulus derives `eulerChar ring8 = 0` from the corner and pinch counts.
example : eulerChar ring8 = 0 := by
  have h := cornerDiff_eq ring8
  have h1 : cornerDiff ring8 = 0 := by decide
  have h2 : pinchCount ring8 = 0 := by decide
  omega

-- The empty complex.
example : cornerDiff ∅ = 4 * eulerChar ∅ + 2 * pinchCount ∅ := cornerDiff_eq ∅

end CellGaussBonnetGlobal

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.TurningNumber
