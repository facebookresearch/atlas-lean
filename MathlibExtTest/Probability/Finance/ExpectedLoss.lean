/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Finance.ExpectedLoss

/-! # Tests for `MathlibExt.Probability.Finance.ExpectedLoss` -/

open MeasureTheory ProbabilityTheory MathlibExt.Probability.Finance.ExpectedLoss

namespace MathlibExtTest.ExpectedLoss

section Examples

theorem measure_real_univ_eq_one
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] :
    μ.real Set.univ = 1 := by
  rw [MeasureTheory.Measure.real_def, measure_univ, ENNReal.toReal_one]

theorem expectedLoss_univ
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (EAD LGD : Ω → ℝ)
    (hInt : IntegrableOn (fun ω => EAD ω * LGD ω) Set.univ μ) :
    expectedLoss μ Set.univ EAD LGD = ∫ ω, EAD ω * LGD ω ∂μ := by
  have hμU : μ Set.univ ≠ 0 := by rw [measure_univ]; exact one_ne_zero
  have hdecomp := expectedLoss_eq_defaultProbability_mul_conditionalExpectedLoss
    μ MeasurableSet.univ hμU hInt
  have hprob : defaultProbability μ Set.univ = 1 := by
    unfold defaultProbability
    exact measure_real_univ_eq_one μ
  have hcond : ProbabilityTheory.cond μ Set.univ = μ :=
    ProbabilityTheory.cond_univ μ
  unfold conditionalExpectedLoss at hdecomp
  rw [hcond, hprob, one_mul] at hdecomp
  exact hdecomp

theorem expectedLoss_const_univ
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] :
    expectedLoss μ Set.univ (fun _ => 100) (fun _ => 0.4) = 40 := by
  have hInt : IntegrableOn (fun ω : Ω => (100:ℝ) * 0.4) Set.univ μ :=
    (MeasureTheory.integrable_const ((100:ℝ) * 0.4)).integrableOn
  rw [expectedLoss_univ μ (fun _ => 100) (fun _ => 0.4) hInt]
  have hval : (∫ ω : Ω, (100:ℝ) * 0.4 ∂μ) = 40 := by
    rw [MeasureTheory.integral_const, measure_real_univ_eq_one μ, one_smul]
    norm_num
  exact hval

end Examples

end MathlibExtTest.ExpectedLoss
