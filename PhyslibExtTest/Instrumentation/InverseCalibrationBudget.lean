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

/-- The primary perturbed-parameter bound at concrete values:
intercept `1`, slope `2`, perturbations `da = db = 1/4`, residual
`e = 1/2`, so the bound is `(1/4 * 3 + 1/4 + 1/2) / (2 - 1/4)
= 6/7`. -/
example : |Chemistry.Calibration.inversePrediction (5 / 4 : ℝ)
    (9 / 4 : ℝ) (15 / 2 : ℝ) - 3| ≤ 6 / 7 := by
  have h := inversePrediction_error_le 1 2 3 3 (1 / 4) (1 / 4) (1 / 4)
    (1 / 4) (1 / 2) (1 / 2) (15 / 2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num at h
  exact h

/-- The measure corollary at concrete values: with zero residual on
a two-point space, the bad event is empty and the bound reads
`0 ≤ 0`. -/
example : (MeasureTheory.Measure.count : MeasureTheory.Measure (Fin 2))
      {ω | (1 / 2 : ℝ) / |(2 : ℝ)| <
        |Chemistry.Calibration.inversePrediction 1 2
          (2 * (fun _ => (3 : ℝ)) ω + 1 + (fun _ => (0 : ℝ)) ω)
          - (fun _ => (3 : ℝ)) ω|}
    ≤ ENNReal.ofReal 0 :=
  inversePrediction_error_event_measure_le MeasureTheory.Measure.count
    1 2 (1 / 2) 0 (by norm_num) (by norm_num) (fun _ => 3) (fun _ => 0)
    (by
      have hempty : {ω : Fin 2 | (1 / 2 : ℝ) < |(fun _ => (0 : ℝ)) ω|}
          = ∅ := by
        ext ω
        simp
      rw [hempty]
      simp)

end PhyslibExtTest.Instrumentation.InverseCalibrationBudget
