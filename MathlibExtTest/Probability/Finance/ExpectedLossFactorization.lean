/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Finance.ExpectedLossFactorization

/-! # Tests for `MathlibExt.Probability.Finance.ExpectedLossFactorization` -/

open MeasureTheory ProbabilityTheory MathlibExt.Probability.Finance.ExpectedLossFactorization

namespace MathlibExtTest.ExpectedLossFactorization

section Examples

example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] :
    expectedLoss μ Set.univ (fun _ => (200 : ℝ)) (fun _ => (0.45 : ℝ)) = 90 := by
  have hμuniv : μ Set.univ ≠ 0 := by simp
  have hInt : IntegrableOn
      (fun ω => (fun _ => (200 : ℝ)) ω * (fun _ => (0.45 : ℝ)) ω) Set.univ μ := by
    rw [integrableOn_univ]
    show Integrable (fun _ => (200 : ℝ) * 0.45) μ
    exact integrable_const _
  have hIntLGD : IntegrableOn (fun _ => (0.45 : ℝ)) Set.univ μ := by
    rw [integrableOn_univ]
    exact integrable_const _
  have h := expectedLoss_eq_pd_mul_lgd_mul_ead (μ := μ) (D := Set.univ)
    (EAD := fun _ => (200 : ℝ)) (LGD := fun _ => (0.45 : ℝ))
    (ead := (200 : ℝ)) (lgd := (0.45 : ℝ))
    MeasurableSet.univ hμuniv (fun _ _ => rfl) (fun _ _ => rfl) hInt hIntLGD
  have hPD : defaultProbability μ Set.univ = 1 := by
    simp only [defaultProbability, Measure.real, IsProbabilityMeasure.measure_univ,
      ENNReal.toReal_one]
  rw [hPD] at h
  exact h.trans (show (1 : ℝ) * 0.45 * 200 = 90 by norm_num)

example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] :
    expectedLoss μ Set.univ (fun _ => (200 : ℝ)) (fun _ => (0.45 : ℝ))
      = 1 * (∫ ω, (0.45 : ℝ) ∂(ProbabilityTheory.cond μ Set.univ)) * 200 := by
  have hμuniv : μ Set.univ ≠ 0 := by simp
  have hInt : IntegrableOn
      (fun ω => (fun _ => (200 : ℝ)) ω * (fun _ => (0.45 : ℝ)) ω) Set.univ μ := by
    rw [integrableOn_univ]
    show Integrable (fun _ => (200 : ℝ) * 0.45) μ
    exact integrable_const _
  have hIntLGD : IntegrableOn (fun _ => (0.45 : ℝ)) Set.univ μ := by
    rw [integrableOn_univ]
    exact integrable_const _
  have h := expectedLoss_eq_defaultProbability_mul_condExpectedLGD_mul_ead
    (μ := μ) (D := Set.univ)
    (EAD := fun _ => (200 : ℝ)) (LGD := fun _ => (0.45 : ℝ)) (ead := (200 : ℝ))
    MeasurableSet.univ hμuniv (fun _ _ => rfl) hInt hIntLGD
  have hPD : defaultProbability μ Set.univ = 1 := by
    simp only [defaultProbability, Measure.real, IsProbabilityMeasure.measure_univ,
      ENNReal.toReal_one]
  rw [hPD] at h
  exact h

example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] :
    1 * (∫ ω, (0.45 : ℝ) ∂(ProbabilityTheory.cond μ Set.univ)) * 200 = 90 := by
  have hμuniv : μ Set.univ ≠ 0 := by simp
  have _hcondProb := ProbabilityTheory.cond_isProbabilityMeasure (μ := μ) (s := Set.univ) hμuniv
  rw [integral_const]
  have h1 : (ProbabilityTheory.cond μ Set.univ).real Set.univ = 1 := by
    simp only [Measure.real, IsProbabilityMeasure.measure_univ, ENNReal.toReal_one]
  rw [h1, one_smul]
  norm_num

end Examples

end MathlibExtTest.ExpectedLossFactorization
