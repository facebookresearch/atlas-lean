/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.MachineLearning.RandomFeatures

open MeasureTheory Real

namespace CSLibExt.MachineLearning.RandomFeatures

-- The zero frequency: the phase average of `2 cos² b` is `1`.
example (x y : ℝ) :
    (2 * π)⁻¹ * ∫ b in (0 : ℝ)..2 * π, fourierFeature (0 : ℝ) b x * fourierFeature 0 b y = 1 := by
  rw [phase_average_fourierFeature_mul]
  simp

-- Unbiasedness for the frequency law `δ₀`, whose characteristic function is `1`.
example (x y : ℝ) :
    ∫ q, fourierFeature q.1 q.2 x * fourierFeature q.1 q.2 y
      ∂((Measure.dirac (0 : ℝ)).prod phaseMeasure) = 1 := by
  rw [integral_fourierFeature_mul]
  simp [charFun_dirac]

-- Hoeffding's bound for `D = 100` features of any frequency law `p`.
example (p : Measure ℝ) [IsProbabilityMeasure p] (x y : ℝ) :
    (Measure.pi fun _ : Fin 100 => p.prod phaseMeasure).real
        {θ | (1 / 2 : ℝ) ≤ |(1 / (100 : ℕ) : ℝ) * ∑ j, fourierFeature (θ j).1 (θ j).2 x *
          fourierFeature (θ j).1 (θ j).2 y - (charFun p (x - y)).re|} ≤
      2 * Real.exp (-((100 : ℕ) * (1 / 2 : ℝ) ^ 2) / 8) :=
  measureReal_abs_avg_fourierFeature_mul_sub_ge_le p 100 (by norm_num) x y (by norm_num)

end CSLibExt.MachineLearning.RandomFeatures
