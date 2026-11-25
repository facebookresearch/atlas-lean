/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Process.ContinuousOptionalStopping

open MeasureTheory MathlibExt.Probability.ContinuousOptionalStoppingWanted.Martingale
open scoped NNReal

namespace MathlibExtTest.Probability.ContinuousOptionalStopping

-- Sampling at the coordinate of the unit interval tests a stopping time of uncountable range.
example {μ : Measure (Set.Iic (1 : ℝ≥0))} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Set.Iic (1 : ℝ≥0)))}
    {M : ℝ≥0 → Set.Iic (1 : ℝ≥0) → ℝ} (hM : Martingale M ℱ μ)
    (hcont : ∀ ω, Continuous fun t ↦ M t ω)
    (hτ : IsStoppingTime ℱ fun ω ↦ (ω.val : WithTop ℝ≥0)) :
    M 0 =ᵐ[μ] μ[fun ω ↦ M ω.val ω | ℱ 0] := by
  have hsample : (stoppedValue M fun ω ↦ (ω.val : WithTop ℝ≥0)) = (fun ω ↦ M ω.val ω) := by
    funext ω
    simp only [stoppedValue, WithTop.untopA, WithTop.untopD_coe]
  simpa only [stoppedValue_const, IsStoppingTime.measurableSpace_const, hsample] using
    stoppedValue_ae_eq_condExp_of_le_of_continuous
      hM hcont (isStoppingTime_const ℱ 0) hτ (fun ω ↦ WithTop.coe_le_coe.mpr bot_le)
      (fun ω ↦ WithTop.coe_le_coe.mpr ω.property)

end MathlibExtTest.Probability.ContinuousOptionalStopping
