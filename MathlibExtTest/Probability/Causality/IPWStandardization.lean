/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Causality.IPWStandardization
import MathlibExtTest.Probability.Causality.Standardization

open MeasureTheory ProbabilityTheory MathlibExt.Probability.Causality
open MathlibExtTest.Probability.Causality.Standardization

private noncomputable def fixtureY (w : Fin 8) : ℝ := observed testT (fun _ => 0) testY1 w

private theorem fixture_integrable (f : Fin 8 → ℝ) : Integrable f testMu :=
  integrableOn_univ.1 (IntegrableOn.of_finite (Set.toFinite _))

-- Two populated strata, unequal propensities, and an additional null stratum.
example : (∫ w, testT.indicator (fun w => fixtureY w / propensity testMu testT testX (testX w)) w
      ∂testMu) = 15 := by
  have hT : MeasurableSet testT := MeasurableSet.of_discrete
  have hX : Measurable testX := Measurable.of_discrete
  rw [(integral_ipw_eq_sum_standardized hT hX (fixture_integrable fixtureY)
    (fun w hw => (testOverlap w hw).1)).2]
  unfold fixtureY
  rw [← integral_eq_sum_standardized_treated (Y₀ := fun _ => 0) hT hX
    (Measurable.of_discrete : Measurable testY1) (fixture_integrable testY1) testSI1]
  exact testMu_Y1

-- A null stratum contributes zero for an arbitrary outcome, even with a zero propensity.
example (Y : Fin 8 → ℝ) : testMu.real (testX ⁻¹' {2}) *
    (∫ w, Y w ∂testMu[|testT ∩ testX ⁻¹' {2}]) = 0 := by
  rw [testMu_two, zero_mul]

-- A propensity of one is allowed: this cohort has only treated units and a null stratum.
example : (∑ x, testMu.real (testX ⁻¹' {x}) *
    (∫ w, testY1 w ∂testMu[|Set.univ ∩ testX ⁻¹' {x}])) = 15 := by
  have hX : Measurable testX := Measurable.of_discrete
  have hprop (x : Fin 3) (hx : testMu (testX ⁻¹' {x}) ≠ 0) :
      propensity testMu Set.univ testX x = 1 := by
    unfold propensity
    rw [Set.univ_inter, div_self ((measureReal_ne_zero_iff (measure_ne_top _ _)).2 hx)]
  rw [← (integral_ipw_eq_sum_standardized MeasurableSet.univ hX (fixture_integrable testY1)
    (fun x hx => (hprop x hx) ▸ zero_lt_one)).2]
  have hpoint (w : Fin 8) : testMu (testX ⁻¹' {testX w}) ≠ 0 := by
    have hsub : ({w} : Set (Fin 8)) ⊆ testX ⁻¹' {testX w} := by
      intro v hv
      simp [Set.mem_singleton_iff.mp hv]
    intro hz
    have hs := measure_mono_null hsub hz
    have hr := (measureReal_eq_zero_iff).2 hs
    rw [testMu_single] at hr
    norm_num at hr
  simpa only [Set.indicator_univ, hprop _ (hpoint _), div_one] using testMu_Y1
