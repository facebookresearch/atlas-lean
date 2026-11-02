/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.CorrelationInequalities.ReimerButterflyMonoRefute

/-!
# Tests for `MathlibExt.Probability.CorrelationInequalities.ReimerButterflyMonoRefute`

* `reimerSliceStep_one_false`: the slice-step hypothesis fails on two coordinates.
* `slice_recombination_gap` at concrete numbers, and `slice_cross_sign_can_be_positive`.
* `refuteW` is a probability weight.
-/

@[expose] public section

open StatMech Finset

namespace MathlibExtTest.StatMech.Probability.CorrelationInequalities.ReimerButterflyMonoRefute

example : ¬ ReimerSliceStep 1 := reimerSliceStep_one_false

example : ∀ i, refuteW i false + refuteW i true = 1 := refuteW_prob

/-- The recombination identity at `a = (1, 0)`, `b = (1, 0)`, `p = q = 1/2`. -/
example : ((1 / 2 : ℝ) * 1 + 1 / 2 * 0) * (1 / 2 * 1 + 1 / 2 * 0) -
    (1 / 2 * (1 * 1) + 1 / 2 * (0 * 0)) = -(1 / 2 * (1 / 2) * ((1 - 0) * (1 - 0))) :=
  slice_recombination_gap 1 0 1 0 (1 / 2) (1 / 2) (by norm_num)

example : ∃ (a0 a1 b0 b1 : ℝ), 0 < (a0 - a1) * (b0 - b1) := slice_cross_sign_can_be_positive

end MathlibExtTest.StatMech.Probability.CorrelationInequalities.ReimerButterflyMonoRefute
