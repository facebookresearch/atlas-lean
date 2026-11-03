/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.DirectionWalk
public import Mathlib

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.BaseCase`

Evaluates `stepOf`, `pos` and `cc`, and instantiates `four_dvd_cc`, `four_le_cc` and
`base_cc_eq_four` on the counterclockwise unit square `![0, 1, 2, 3]` (all hypotheses by `decide`,
including `hnodbl`). The square traversed twice is closed and has no right turns but is not simple
and has `cc = 8`: `four_le_cc` applies to it, and it shows that simplicity cannot be dropped from
the Umlaufsatz.
-/

@[expose] public section

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.TurningNumber.BaseCase

open StatMech.Onsager.BaseCase

/-- The counterclockwise unit square: east, north, west, south. -/
def square : Fin 4 → Fin 4 := ![0, 1, 2, 3]

/-- The unit square traversed twice. -/
def square2 : Fin 8 → Fin 4 := ![0, 1, 2, 3, 0, 1, 2, 3]

-- `stepOf` is never zero, checked at direction `2`.
example : stepOf 2 = (-1, 0) := rfl

-- The last vertex of the unit square walk.
example : pos square 3 = (0, 1) := by decide

-- `cc` counts left turns: four for the square, eight for the doubled square, none for a
-- straight sequence.
example : cc square = 4 ∧ cc square2 = 8 ∧ cc (fun _ : Fin 3 => (0 : Fin 4)) = 0 := by decide

-- Non-vacuity of `base_cc_eq_four` on the square, with `hnodbl` discharged by computation.
example : cc square = 4 :=
  base_cc_eq_four square (by decide) (by decide) (by decide) (fun _ => by decide)

-- `four_dvd_cc` and `four_le_cc` on the doubled square.
example : 4 ∣ cc square2 := four_dvd_cc square2 (by decide)
example : 4 ≤ cc square2 := four_le_cc square2 (by decide) (by decide)

-- The doubled square is closed and has no right turns, but is not simple: dropping `hsimple`
-- from the Umlaufsatz would make it false.
example : ∑ i, stepOf (square2 i) = 0 ∧
    (∀ i : Fin 8, square2 (i + 1) - square2 i = 0 ∨ square2 (i + 1) - square2 i = 1) ∧
    ¬ Function.Injective (pos square2) ∧ cc square2 ≠ 4 := by
  decide

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.TurningNumber.BaseCase
