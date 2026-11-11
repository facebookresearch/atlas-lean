/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.LatticeUmlaufsatz

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.LatticeUmlaufsatz`

`turnSum_eq_four_or_neg_four` (lattice Umlaufsatz, right turns allowed) on three polygons, with
every hypothesis checked by `decide` and the turning sum also computed directly:
* the counterclockwise unit square (turning `+4`);
* the clockwise unit square (turning `-4`), excluded by the left-turn-only version in
  `TurningNumber` but covered here;
* a non-convex L-shaped octagon with one right turn (turning `+4`).
The simplicity hypothesis `hsimple` matters: the doubly traversed square has turning `8`
and is not simple.
-/

@[expose] public section

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.TurningNumber.LatticeUmlaufsatz

open _root_.StatMech.Onsager _root_.StatMech.Onsager.BaseCase
  _root_.StatMech.Onsager.GeneralUmlaufsatz

/-- The counterclockwise unit square: east, north, west, south. -/
def ccwSquare : Fin 4 → Fin 4 := ![0, 1, 2, 3]

/-- The clockwise unit square: east, south, west, north. -/
def cwSquare : Fin 4 → Fin 4 := ![0, 3, 2, 1]

/-- An L-shaped octagon with one reflex corner: E, E, N, W, N, W, S, S. -/
def lShape : Fin 8 → Fin 4 := ![0, 0, 1, 2, 1, 2, 3, 3]

/-- The unit square traversed twice. -/
def doubleSquare : Fin 8 → Fin 4 := ![0, 1, 2, 3, 0, 1, 2, 3]

-- The counterclockwise square: hypotheses, the theorem, and the direct value `4`.
example : (∑ i, ons_turnPow (ccwSquare i) (ccwSquare (i + 1))) = 4 ∨
    (∑ i, ons_turnPow (ccwSquare i) (ccwSquare (i + 1))) = -4 :=
  turnSum_eq_four_or_neg_four ccwSquare (by decide) (by decide) (by norm_num) (by decide)

example : (∑ i, ons_turnPow (ccwSquare i) (ccwSquare (i + 1))) = 4 := by decide

-- The clockwise square: the theorem applies and the turning is `-4`.
example : (∑ i, ons_turnPow (cwSquare i) (cwSquare (i + 1))) = 4 ∨
    (∑ i, ons_turnPow (cwSquare i) (cwSquare (i + 1))) = -4 :=
  turnSum_eq_four_or_neg_four cwSquare (by decide) (by decide) (by norm_num) (by decide)

example : (∑ i, ons_turnPow (cwSquare i) (cwSquare (i + 1))) = -4 := by decide

-- The L-shaped octagon has a right turn (north → west → north) and turning `+4`.
example : (∑ i, ons_turnPow (lShape i) (lShape (i + 1))) = 4 ∨
    (∑ i, ons_turnPow (lShape i) (lShape (i + 1))) = -4 :=
  turnSum_eq_four_or_neg_four lShape (by decide) (by decide) (by norm_num) (by decide)

example : ons_turnPow (lShape 3) (lShape 4) = -1 ∧
    (∑ i, ons_turnPow (lShape i) (lShape (i + 1))) = 4 := by decide

-- Simplicity is needed: the doubly traversed square is closed, has no U-turns, turns by `8`, and
-- is not simple.
example : ∑ i, stepOf (doubleSquare i) = 0 ∧ (∀ i, doubleSquare (i + 1) ≠ doubleSquare i + 2) ∧
    (∑ i, ons_turnPow (doubleSquare i) (doubleSquare (i + 1))) = 8 ∧
    ¬ Function.Injective (pos doubleSquare) := by decide

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.TurningNumber.LatticeUmlaufsatz
