/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.Umlaufsatz

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.UmlaufsatzFinal`

Non-vacuity of the discrete Umlaufsatz `cc_eq_four_of_no_right_turn`: its three hypotheses (closed,
simple, no right turns or reversals) are proved by `decide` for the counterclockwise unit square
`![0, 1, 2, 3]` (east, north, west, south; `n = 4`) and the counterclockwise `2 × 1` rectangle
`![0, 0, 1, 2, 2, 3]` (`n = 6`, with two straight steps), and the theorem yields `cc d = 4`, which
is also checked by direct computation. The definitions `stepOf`, `pos` and `cc` are evaluated at
small inputs, and a clockwise square (which has right turns) is shown to violate `hreflexfree`.
-/

@[expose] public section

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.TurningNumber.UmlaufsatzFinal

open StatMech.Onsager.BaseCase StatMech.Onsager.UmlaufsatzFinal

/-- The counterclockwise unit square: east, north, west, south. -/
def square : Fin 4 → Fin 4 := ![0, 1, 2, 3]

/-- The counterclockwise `2 × 1` rectangle: east, east, north, west, west, south. -/
def rect : Fin 6 → Fin 4 := ![0, 0, 1, 2, 2, 3]

-- `stepOf` evaluates to the four unit vectors.
example : stepOf 0 = (1, 0) ∧ stepOf 1 = (0, 1) ∧ stepOf 2 = (-1, 0) ∧ stepOf 3 = (0, -1) := by
  decide

-- The vertices of the unit square walk are `(0,0), (1,0), (1,1), (0,1)`.
example : pos square 0 = (0, 0) ∧ pos square 1 = (1, 0) ∧ pos square 2 = (1, 1) ∧
    pos square 3 = (0, 1) := by
  decide

-- The vertices of the rectangle walk.
example : pos rect 2 = (2, 0) ∧ pos rect 3 = (2, 1) ∧ pos rect 5 = (0, 1) := by decide

-- The unit square is closed.
theorem square_closed : ∑ i, stepOf (square i) = 0 := by decide

-- The unit square is simple.
theorem square_simple : Function.Injective (pos square) := by decide

-- Every turn of the unit square is a left turn (including the wrap-around turn `3 → 0`).
theorem square_reflexfree : ∀ i : Fin 4, square (i + 1) - square i = 0 ∨
    square (i + 1) - square i = 1 := by
  decide

-- Direct computation of `cc` on the unit square.
example : cc square = 4 := by decide

-- Non-vacuity of the headline on the unit square.
example : cc square = 4 :=
  cc_eq_four_of_no_right_turn square square_closed square_simple square_reflexfree

-- The rectangle is closed.
theorem rect_closed : ∑ i, stepOf (rect i) = 0 := by decide

-- The rectangle is simple.
theorem rect_simple : Function.Injective (pos rect) := by decide

-- Every turn of the rectangle is straight or left.
theorem rect_reflexfree : ∀ i : Fin 6, rect (i + 1) - rect i = 0 ∨ rect (i + 1) - rect i = 1 := by
  decide

-- Direct computation: the rectangle has four left turns and two straight steps.
example : cc rect = 4 := by decide

-- Non-vacuity of the headline on the rectangle, with straight steps present.
example : cc rect = 4 :=
  cc_eq_four_of_no_right_turn rect rect_closed rect_simple rect_reflexfree

-- The length bound `three_le_n` applies (and is tight up to one for the square).
example : 3 ≤ 4 := three_le_n square square_closed square_reflexfree

-- `hnodbl_discharged` gives `cc < 8` for the rectangle.
example : cc rect < 8 := hnodbl_discharged rect rect_closed rect_reflexfree rect_simple

-- The clockwise square (east, south, west, north) is closed and simple but has right turns, so it
-- is excluded by `hreflexfree`.
example : ¬ ∀ i : Fin 4, (![0, 3, 2, 1] : Fin 4 → Fin 4) (i + 1) - ![0, 3, 2, 1] i = 0 ∨
    (![0, 3, 2, 1] : Fin 4 → Fin 4) (i + 1) - ![0, 3, 2, 1] i = 1 := by
  decide

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.TurningNumber.UmlaufsatzFinal
