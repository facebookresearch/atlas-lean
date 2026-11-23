/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Distributed.ColeVishkin

/-!
# Tests for one Cole–Vishkin step

* The step computes: `decide` evaluates new colors, including the color `5`
  for `4, 0`, the largest value below the bound `2 * 3`, and two rounds on the
  path colored `5, 7, 2, 6`.
* `cvColor_proper` and `cvColor_lt` apply to concrete colors.
-/

@[expose] public section

namespace Cslib.Distributed.ColeVishkinTests

open Cslib.Distributed.ColeVishkin

/-! ### Computed colors -/

/-- `0 = 0b0` and `1 = 0b1` first differ at bit `0`, where `0` has a `0`. -/
example : cvColor 0 1 (by decide) = 0 := by decide

/-- `1 = 0b01` and `2 = 0b10` first differ at bit `0`, where `1` has a `1`. -/
example : cvColor 1 2 (by decide) = 1 := by decide

/-- `5 = 0b101` and `7 = 0b111` first differ at bit `1`, where `5` has a `0`. -/
example : lsbDiff 5 7 (by decide) = 1 ∧ cvColor 5 7 (by decide) = 2 := by decide

/-- Near the upper bound: `4 = 0b100` and `0` are below `2 ^ 3` and first
differ at bit `2`, where `4` has a `1`, so the new color is `5`, the largest
value below `2 * 3`. -/
example : cvColor 4 0 (by decide) = 5 := by decide

/-- The bound `cvColor_lt` for the near-bound example. -/
example : cvColor 4 0 (by decide) < 2 * 3 :=
  cvColor_lt 4 0 (by decide) (by decide) (by decide) (by decide)

/-- Two rounds on the path colored `5, 7, 2, 6` give `2, 1, 4` and then
`0, 1`, proper at each round. -/
example :
    (cvColor 5 7 (by decide), cvColor 7 2 (by decide), cvColor 2 6 (by decide)) =
      (2, 1, 4) ∧
    (cvColor 2 1 (by decide), cvColor 1 4 (by decide)) = (0, 1) := by
  decide

/-! ### Properness -/

/-- One CV step separates the first two nodes of the color path `0, 1, 2`. -/
example : cvColor 0 1 (by decide) ≠ cvColor 1 2 (by decide) :=
  cvColor_proper 0 1 2 (by decide) (by decide)

/-- Colors below `2 ^ 2` step to colors below `2 * 2`. -/
example : cvColor 2 3 (by decide) < 2 * 2 :=
  cvColor_lt 2 3 (by decide) (by decide) (by decide) (by decide)

end Cslib.Distributed.ColeVishkinTests
