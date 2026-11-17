/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Electronics.FiniteGainFeedback
import Mathlib.Tactic.NormNum

@[expose] public section

namespace PhyslibExtTest.Electronics.FiniteGainFeedback

open PhyslibExt.Electronics.FiniteGainFeedback

/-- Small loop gain: `A = beta = 1`, `vi = 1` gives `vo = 1/2`, and
the deficit is `1 - 1/2 = 1/2`. -/
example : (1 : ℝ) * 1 / (1 + 1 * 1) = 1 / 2 := by norm_num
example : (1 : ℝ) / 1 - 1 / (1 + 1 * 1) = 1 / (1 * (1 + 1 * 1)) := by norm_num

/-- Zero input gives zero output, through the closed-form theorem. -/
example {A beta : ℝ} (hA : 0 < A) (hbeta : 0 < beta) :
    A * 0 / (1 + A * beta) = A * (0 - beta * (A * 0 / (1 + A * beta))) :=
  closedForm_satisfies hA hbeta

/-- Large loop gain: with `A = 100`, `beta = 1`, the closed-loop gain
is `100/101`, within `1/101` of ideal, by the deficit identity. -/
example : (1 : ℝ) / 1 - 100 / (1 + 100 * 1) = 1 / 101 := by norm_num

/-- The deficit identity at that point, through the public theorem. -/
example : (1 : ℝ) / 1 - 100 / (1 + 100 * 1)
    = 1 / (1 * (1 + 100 * 1)) :=
  gain_deficit (by norm_num) (by norm_num)

end PhyslibExtTest.Electronics.FiniteGainFeedback
