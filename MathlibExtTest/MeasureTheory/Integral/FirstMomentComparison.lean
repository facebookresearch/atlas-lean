/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.MeasureTheory.Integral.FirstMomentComparison
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory Set

-- No positivity of f is required, and the measure need not be Lebesgue measure.
example (c : ℝ) :
    (∫ y, y ∂Measure.dirac c) * (∫ y, y * (1 : ℝ) ∂Measure.dirac c) ≤
      (∫ y, y * y ∂Measure.dirac c) * (∫ _, (1 : ℝ) ∂Measure.dirac c) := by
  apply MathlibExt.MeasureTheory.firstMoment_mul_integral_le
  · exact integrable_dirac (by exact enorm_lt_top)
  · exact integrable_dirac (by exact enorm_lt_top)
  · exact integrable_dirac (by exact enorm_lt_top)
  · exact integrable_dirac (by exact enorm_lt_top)
  · intro y z
    nlinarith [sq_nonneg (y - z)]

example :
    (∫ y in Icc (-1 : ℝ) 1, y) * (∫ y in Icc (-1 : ℝ) 1, y * (1 : ℝ)) ≤
      (∫ y in Icc (-1 : ℝ) 1, y * y) * (∫ _ in Icc (-1 : ℝ) 1, (1 : ℝ)) := by
  apply MathlibExt.MeasureTheory.firstMoment_mul_integral_le
  · exact continuous_id.continuousOn.integrableOn_Icc
  · exact continuous_const.continuousOn.integrableOn_Icc
  · exact (continuous_id.mul continuous_id).continuousOn.integrableOn_Icc
  · exact (continuous_id.mul continuous_const).continuousOn.integrableOn_Icc
  · intro y z
    nlinarith [sq_nonneg (y - z)]
