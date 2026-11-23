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
example : (1 : ℝ) / 1 - closedLoopGain 1 1 = 1 / (1 * (1 + 1 * 1)) :=
  gain_deficit (by norm_num) (by norm_num)

/-- Any output satisfying the amplifier equation is the closed-loop
gain times the input: at `A = beta = 1`, `vi = 3`, that is `3/2`. -/
example {vo : ℝ} (h : vo = (1 : ℝ) * (3 - 1 * vo)) : vo = 3 / 2 := by
  have h2 := output_eq_closedLoopGain_mul (A := 1) (beta := 1) (vi := 3)
    (by norm_num) (by norm_num) h
  rw [h2]
  norm_num [closedLoopGain]

/-- Zero input gives zero output, through the closed-form lemma. -/
example {A beta : ℝ} (hA : 0 < A) (hbeta : 0 < beta) :
    A * 0 / (1 + A * beta) = A * (0 - beta * (A * 0 / (1 + A * beta))) :=
  closedForm_satisfies hA hbeta

/-- Large loop gain: with `A = 100`, `beta = 1`, the closed-loop gain
is `100/101`, within `1/101` of ideal, by the deficit identity. -/
example : (1 : ℝ) / 1 - closedLoopGain 100 1 = 1 / 101 := by
  have h := gain_deficit (A := 100) (beta := 1) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

end PhyslibExtTest.Electronics.FiniteGainFeedback
