/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.GaussianRateDistortionValue
public import MathlibExt.InformationTheory.GaussianDistortionConverse

@[expose] public section

open MathlibExt.InformationTheory.GaussianDistortionFeasibility
  MathlibExt.InformationTheory.GaussianRateDistortionValue
open scoped ENNReal NNReal

namespace MathlibExtTest.InformationTheory.GaussianRateDistortionValue

/-- The converse discharges `hlower` directly; only the achievability bound remains. -/
example {σ2 : ℝ≥0} (hσ2 : 0 < σ2) {D : ℝ} (hD : 0 ≤ D)
    (hupper : ∀ d : ℝ≥0, (0 : ℝ) < (d : ℝ) → (d : ℝ) < (σ2 : ℝ) →
      rateDistortion σ2 (d : ℝ) ≤
        ENNReal.ofReal (Real.log ((σ2 : ℝ) / (d : ℝ)) / (2 * Real.log 2))) :
    rateDistortion σ2 D =
      if D = 0 then ⊤
      else if D < (σ2 : ℝ) then ENNReal.ofReal (Real.log ((σ2 : ℝ) / D) / (2 * Real.log 2))
      else 0 :=
  rateDistortion_eq_ite hσ2 hD
    (MathlibExt.InformationTheory.GaussianDistortionConverse.rateDistortion_ge_ofReal_log_div σ2)
    hupper

/-- Zero distortion of a nondegenerate source costs infinite rate. -/
example : rateDistortion 1 0 = ⊤ := rateDistortion_zero_eq_top one_pos

/-- At `D = σ2` the rate is zero. -/
example : rateDistortion 1 1 = 0 := rateDistortion_eq_zero_of_le 1 (by simp)

/-- Above `σ2` the rate is still zero. -/
example : rateDistortion 1 2 = 0 := rateDistortion_eq_zero_of_le 1 (by norm_num)

/-- For the degenerate source `N(0, 0)` zero distortion is free. -/
example : rateDistortion 0 0 = 0 := rateDistortion_zero_zero

/-- Exact reconstruction of a nondegenerate source carries infinite mutual information. -/
example : InformationTheory.measureMutualInformation (diagonalReconstruction 1) = ⊤ :=
  measureMutualInformation_diagonalReconstruction one_pos

end MathlibExtTest.InformationTheory.GaussianRateDistortionValue
