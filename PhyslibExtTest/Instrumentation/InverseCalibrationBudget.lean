/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Instrumentation.InverseCalibrationBudget
import Mathlib.Tactic.NormNum

@[expose] public section

open PhyslibExt.Instrumentation.InverseCalibrationBudget

namespace PhyslibExtTest.Instrumentation.InverseCalibrationBudget

/-- Known parameters at concrete values: intercept `a = 1`, slope
`b = 2`, `x = 3`, `e = 1/2`, so `y = 2 * 3 + 1 + 1/2 = 15/2` and
the recovered input is `(15/2 - 1) / 2 = 13/4`, with error
`1/4 = E / |b|`: the bound is met with equality. -/
example : |Chemistry.Calibration.inversePrediction 1 2 (15 / 2 : ℝ) - 3|
    ≤ (1 / 2) / |(2 : ℝ)| :=
  inversePrediction_error_le_known_params 1 2 3 (1 / 2) (1 / 2) (15 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The deterministic bound behind it, evaluated. -/
example : Chemistry.Calibration.inversePrediction 1 2 (15 / 2 : ℝ) = 13 / 4 := by
  simp [Chemistry.Calibration.inversePrediction]
  norm_num

end PhyslibExtTest.Instrumentation.InverseCalibrationBudget
