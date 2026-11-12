/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Finance.TwoAssetMinVariance

/-! # Tests for `MathlibExt.Probability.Finance.TwoAssetMinVariance` -/

namespace MathlibExtTest.TwoAssetMinVariance

-- Test section: concrete two-point example.
open scoped ENNReal in
example : MathlibExt.Probability.Finance.TwoAssetMinVariance.twoAssetVariance
      ((1/2 : ℝ≥0∞) • MeasureTheory.Measure.count)
      (fun ω : Fin 2 => if ω = 0 then (0:ℝ) else 1) (0 : Fin 2 → ℝ)
      (MathlibExt.Probability.Finance.TwoAssetMinVariance.minVarianceWeight
        ((1/2 : ℝ≥0∞) • MeasureTheory.Measure.count)
        (fun ω : Fin 2 => if ω = 0 then (0:ℝ) else 1) (0 : Fin 2 → ℝ))
    ≤ MathlibExt.Probability.Finance.TwoAssetMinVariance.twoAssetVariance
      ((1/2 : ℝ≥0∞) • MeasureTheory.Measure.count)
      (fun ω : Fin 2 => if ω = 0 then (0:ℝ) else 1) (0 : Fin 2 → ℝ) 0 := by
  set R₁ : Fin 2 → ℝ := fun ω => if ω = 0 then (0:ℝ) else 1 with hR₁def
  set μ : MeasureTheory.Measure (Fin 2) := (1/2 : ℝ≥0∞) • MeasureTheory.Measure.count
    with hμdef
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  have hfin : MeasureTheory.IsFiniteMeasure μ := by
    rw [hμdef]
    exact MeasureTheory.Measure.smul_finite _ (by norm_num)
  have hR₁meas : Measurable R₁ := by
    rw [hR₁def]
    exact Measurable.ite
      (show MeasurableSet {a : Fin 2 | a = 0} from measurableSet_singleton 0)
      measurable_const measurable_const
  have hR₁bdd : ∀ᵐ ω ∂μ, ‖R₁ ω‖ ≤ 1 := by
    filter_upwards with ω
    by_cases h : ω = 0 <;> simp [hR₁def, h]
  have hR₁ : MeasureTheory.MemLp R₁ 2 μ :=
    MeasureTheory.MemLp.of_bound hR₁meas.aestronglyMeasurable 1 hR₁bdd
  have hR₂ : MeasureTheory.MemLp (0 : Fin 2 → ℝ) 2 μ :=
    MeasureTheory.memLp_const 0
  have hμreal : ∀ ω : Fin 2, μ.real {ω} = 1/2 := by
    intro ω
    simp [hμdef, MeasureTheory.Measure.smul_apply, MeasureTheory.Measure.real_def,
      smul_eq_mul]
  have hmean : ∫ ω, R₁ ω ∂μ = 1/2 := by
    rw [MeasureTheory.integral_fintype (hR₁.integrable one_le_two)]
    simp only [hμreal, Fin.sum_univ_two, hR₁def, h10, smul_eq_mul, ite_true,
      ite_false]
    norm_num
  have hsq : MeasureTheory.Integrable (fun ω : Fin 2 => (R₁ ω - 1/2)^2) μ := by
    refine MeasureTheory.Integrable.of_bound ?_ 1 ?_
    · exact ((hR₁meas.sub_const (1/2 : ℝ)).pow_const 2).aestronglyMeasurable
    · filter_upwards with ω
      by_cases h : ω = 0
      · simp only [hR₁def, h, ite_true]
        norm_num
      · simp only [hR₁def, h, ite_false]
        norm_num
  have hvar : ProbabilityTheory.variance R₁ μ = 1/4 := by
    rw [ProbabilityTheory.variance_eq_integral hR₁meas.aemeasurable, hmean,
      MeasureTheory.integral_fintype hsq]
    simp only [hμreal, Fin.sum_univ_two, hR₁def, h10, smul_eq_mul, ite_true,
      ite_false]
    norm_num
  have hfun : (fun ω : Fin 2 => R₁ ω - (0 : Fin 2 → ℝ) ω) = R₁ := by
    ext ω
    simp
  have hpos : 0 < ProbabilityTheory.variance
      (fun ω : Fin 2 => R₁ ω - (0 : Fin 2 → ℝ) ω) μ := by
    rw [hfun, hvar]
    norm_num
  exact MathlibExt.Probability.Finance.TwoAssetMinVariance.minVarianceWeight_isMinimizer
    hR₁ hR₂ hpos 0

end MathlibExtTest.TwoAssetMinVariance
