/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.MarginRademacher

/-!
# Tests for the margin costs of voting classifiers

Values of the ramp at `θ = 1`, and the complexity bound instantiated for two base classifiers
on a two-point sample with labels `+1, -1` and margin `θ = 1 / 4`.
-/

namespace Cslib.MachineLearning.Rademacher

example : ramp 1 0 = 1 := by norm_num [ramp]
example : ramp 1 (1 / 2) = 1 / 2 := by norm_num [ramp]
example : ramp 1 2 = 0 := by norm_num [ramp]
-- a negative margin costs `1`, as does the zero-one loss
example : (if (-1 : ℝ) ≤ 0 then (1 : ℝ) else 0) ≤ ramp (1 / 4) (-1) :=
  indicator_le_ramp (by norm_num) _

example : rademacherComplexity
      (marginCosts (ramp (1 / 4)) ![1, -1] (convexHull ℝ {![1, 1], ![1, -1]})) ≤
    rademacherComplexity ({![1, 1], ![1, -1]} : Set (Fin 2 → ℝ)) / (1 / 4) :=
  rademacherComplexity_rampCosts_convexHull_le (by simp)
    ((Set.toFinite _).isBounded) ![1, -1] (by intro i; fin_cases i <;> simp) (by norm_num)

#print axioms rademacherComplexity_marginCosts_convexHull_le
#print axioms rademacherComplexity_rampCosts_convexHull_le

end Cslib.MachineLearning.Rademacher
