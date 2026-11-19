/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Finance.ValueAtRisk
import Mathlib.Tactic.NormNum

/-! # Tests for `MathlibExt.Probability.Finance.ValueAtRisk`

* Exact cdf values: `0.96` for a single loss at `0`, `0.9216` and `0.9984` for the
  sum at `0` and `100`.
* The VaR values restated: single `0`, sum `100`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open MathlibExt.Probability.Finance.ExpectedShortfall
open MathlibExt.Probability.Finance.ValueAtRisk

namespace MathlibExtTest.Probability.Finance.ValueAtRisk

example : cdf (lossLaw prodWeights loss1) 0 = 0.96 := by
  rw [cdf_loss_single_eq, ite_eq_right (by norm_num), ite_eq_left (by norm_num)]

example : cdf (lossLaw prodWeights (loss1 + loss2)) 0 = 0.9216 := by
  rw [cdf_loss_sum_eq, ite_eq_right (by norm_num), ite_eq_left (by norm_num)]

example : cdf (lossLaw prodWeights (loss1 + loss2)) 100 = 0.9984 := by
  rw [cdf_loss_sum_eq, ite_eq_right (by norm_num), ite_eq_right (by norm_num),
    ite_eq_left (by norm_num)]

example : valueAtRisk (lossLaw prodWeights loss1) (95 / 100) = 0 ∧
    valueAtRisk (lossLaw prodWeights (loss1 + loss2)) (95 / 100) = 100 :=
  ⟨valueAtRisk_loss_single_eq_zero, valueAtRisk_loss_sum_eq⟩

end MathlibExtTest.Probability.Finance.ValueAtRisk
