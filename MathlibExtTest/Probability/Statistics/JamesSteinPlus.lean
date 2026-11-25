/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Statistics.JamesSteinPlus

/-!
# Tests for the positive-part James–Stein risk comparison

In dimension three, clipping can increase the loss at a particular observation even though it
has no greater risk at the same mean vector.
-/

open MeasureTheory ProbabilityTheory

namespace MathlibExtTest.Probability.Statistics.JamesSteinPlus

private noncomputable def mean : Fin 3 → ℝ := ![-3 / 2, 0, 0]

-- The ordinary estimate equals the mean here, whereas its positive part is zero.
example : let x : Fin 3 → ℝ := ![1 / 2, 0, 0]
    ∑ i, (jamesStein x i - mean i) ^ 2 < ∑ i, (jamesSteinPlus x i - mean i) ^ 2 := by
  norm_num [mean, jamesStein, jamesSteinPlus, Fin.sum_univ_three]

-- At that same mean, clipping preserves strict risk improvement over the usual estimator.
example : ∫ x, ∑ i, (jamesSteinPlus x i - mean i) ^ 2
    ∂(Measure.pi fun i => gaussianReal (mean i) 1) < 3 := by
  have h := (integral_jamesSteinPlus_risk_le (le_refl 3) mean).2.trans_lt
    (integral_jamesStein_risk_lt (le_refl 3) mean)
  simpa only [integral_sum_sq_sub_pi_gaussianReal, Nat.cast_ofNat] using h

end MathlibExtTest.Probability.Statistics.JamesSteinPlus
