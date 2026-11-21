/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.PACLearning.RiskBridge

/-!
# Risk bridge tests

The 0-1 risk of `not` under the point mass at `(true, true)` is `1`, read through CSLib's error;
and on a sample of two points where `not` errs once, its empirical 0-1 risk is `1/2`.
-/

namespace Cslib.MachineLearning.PACLearning

open MeasureTheory
open CSLibExt.MachineLearning.GeneralizationBounds (risk empiricalRisk)

example : risk zeroOneLoss (Measure.dirac ((true, true) : Bool × Bool)) not = 1 := by
  rw [risk_zeroOneLoss_eq_toReal_error _ _ MeasurableSet.of_discrete]
  simp [error]

example : empiricalRisk zeroOneLoss
    (![(true, true), (true, false)] : LabeledSample Bool Bool 2) not = 1 / 2 := by
  rw [empiricalRisk_zeroOneLoss_eq_miscount_div]
  norm_num [empiricalMiscount]
  decide

end Cslib.MachineLearning.PACLearning
