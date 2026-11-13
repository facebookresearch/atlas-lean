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

/-- Two equally likely states, for the anti-correlated example below. -/
noncomputable def μAnti : MeasureTheory.Measure (Fin 2) :=
  (1 / 2 : ENNReal) • MeasureTheory.Measure.count

/-- First asset: `0` in state `0`, `1` in state `1`. -/
def r₁Anti : Fin 2 → ℝ := fun ω => if ω = 0 then 0 else 1

/-- Second asset: `1` in state `0`, `0` in state `1` (perfectly anti-correlated
with `r₁Anti`). -/
def r₂Anti : Fin 2 → ℝ := fun ω => if ω = 0 then 1 else 0

/-- **Nontrivial minimum weight**: for the anti-correlated pair, the
minimum-variance weight is the interior value `1 / 2` (not an endpoint and
not `0`), and the portfolio at that weight beats the distinct weight `0`.
This detects sign, operand, and denominator errors in the formula, which the
degenerate `R₂ = 0` example above cannot. -/
example :
    MathlibExt.Probability.Finance.TwoAssetMinVariance.minVarianceWeight μAnti
        r₁Anti r₂Anti = 1 / 2 ∧
      MathlibExt.Probability.Finance.TwoAssetMinVariance.twoAssetVariance μAnti
          r₁Anti r₂Anti
          (MathlibExt.Probability.Finance.TwoAssetMinVariance.minVarianceWeight μAnti
            r₁Anti r₂Anti) ≤
        MathlibExt.Probability.Finance.TwoAssetMinVariance.twoAssetVariance μAnti
          r₁Anti r₂Anti 0 := by
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  have hfin : MeasureTheory.IsFiniteMeasure μAnti := by
    rw [μAnti]
    exact MeasureTheory.Measure.smul_finite _ (by norm_num)
  have hR₁meas : Measurable r₁Anti := by
    unfold r₁Anti
    exact Measurable.ite
      (show MeasurableSet {a : Fin 2 | a = 0} from measurableSet_singleton 0)
      measurable_const measurable_const
  have hR₂meas : Measurable r₂Anti := by
    unfold r₂Anti
    exact Measurable.ite
      (show MeasurableSet {a : Fin 2 | a = 0} from measurableSet_singleton 0)
      measurable_const measurable_const
  have hR₁bdd : ∀ᵐ ω ∂μAnti, ‖r₁Anti ω‖ ≤ 1 := by
    filter_upwards with ω
    by_cases h : ω = 0 <;> simp [r₁Anti, h]
  have hR₂bdd : ∀ᵐ ω ∂μAnti, ‖r₂Anti ω‖ ≤ 1 := by
    filter_upwards with ω
    by_cases h : ω = 0 <;> simp [r₂Anti, h]
  have hR₁ : MeasureTheory.MemLp r₁Anti 2 μAnti :=
    MeasureTheory.MemLp.of_bound hR₁meas.aestronglyMeasurable 1 hR₁bdd
  have hR₂ : MeasureTheory.MemLp r₂Anti 2 μAnti :=
    MeasureTheory.MemLp.of_bound hR₂meas.aestronglyMeasurable 1 hR₂bdd
  have hμreal : ∀ ω : Fin 2, μAnti.real {ω} = 1 / 2 := by
    intro ω
    simp [μAnti, MeasureTheory.Measure.smul_apply, MeasureTheory.Measure.real_def,
      smul_eq_mul]
  have hmean₁ : ∫ ω, r₁Anti ω ∂μAnti = 1 / 2 := by
    rw [MeasureTheory.integral_fintype (hR₁.integrable one_le_two)]
    simp only [hμreal, Fin.sum_univ_two, r₁Anti, h10, smul_eq_mul, ite_true,
      ite_false]
    norm_num
  have hmean₂ : ∫ ω, r₂Anti ω ∂μAnti = 1 / 2 := by
    rw [MeasureTheory.integral_fintype (hR₂.integrable one_le_two)]
    simp only [hμreal, Fin.sum_univ_two, r₂Anti, h10, smul_eq_mul, ite_true,
      ite_false]
    norm_num
  have hsq₁ : MeasureTheory.Integrable (fun ω : Fin 2 => (r₁Anti ω - 1 / 2) ^ 2)
      μAnti := by
    refine MeasureTheory.Integrable.of_bound ?_ 1 ?_
    · exact ((hR₁meas.sub_const (1 / 2 : ℝ)).pow_const 2).aestronglyMeasurable
    · filter_upwards with ω
      by_cases h : ω = 0
      · simp only [r₁Anti, h, ite_true]
        norm_num
      · simp only [r₁Anti, h, ite_false]
        norm_num
  have hsq₂ : MeasureTheory.Integrable (fun ω : Fin 2 => (r₂Anti ω - 1 / 2) ^ 2)
      μAnti := by
    refine MeasureTheory.Integrable.of_bound ?_ 1 ?_
    · exact ((hR₂meas.sub_const (1 / 2 : ℝ)).pow_const 2).aestronglyMeasurable
    · filter_upwards with ω
      by_cases h : ω = 0
      · simp only [r₂Anti, h, ite_true]
        norm_num
      · simp only [r₂Anti, h, ite_false]
        norm_num
  have hvar₁ : ProbabilityTheory.variance r₁Anti μAnti = 1 / 4 := by
    rw [ProbabilityTheory.variance_eq_integral hR₁meas.aemeasurable, hmean₁,
      MeasureTheory.integral_fintype hsq₁]
    simp only [hμreal, Fin.sum_univ_two, r₁Anti, h10, smul_eq_mul, ite_true,
      ite_false]
    norm_num
  have hvar₂ : ProbabilityTheory.variance r₂Anti μAnti = 1 / 4 := by
    rw [ProbabilityTheory.variance_eq_integral hR₂meas.aemeasurable, hmean₂,
      MeasureTheory.integral_fintype hsq₂]
    simp only [hμreal, Fin.sum_univ_two, r₂Anti, h10, smul_eq_mul, ite_true,
      ite_false]
    norm_num
  have hprod : ∫ ω, r₁Anti ω * r₂Anti ω ∂μAnti = 0 := by
    rw [MeasureTheory.integral_fintype MeasureTheory.Integrable.of_finite]
    simp only [hμreal, Fin.sum_univ_two, r₁Anti, r₂Anti, h10, smul_eq_mul,
      ite_true, ite_false]
    norm_num
  have hprob : MeasureTheory.IsProbabilityMeasure μAnti := ⟨by
    simp [μAnti, MeasureTheory.Measure.smul_apply, smul_eq_mul,
      ENNReal.inv_mul_cancel]⟩
  have hcov : ProbabilityTheory.covariance r₁Anti r₂Anti μAnti = -1 / 4 := by
    rw [ProbabilityTheory.covariance_eq_sub hR₁ hR₂, hmean₁, hmean₂]
    simp only [Pi.mul_apply]
    rw [hprod]
    norm_num
  have hvarDiff : ProbabilityTheory.variance (fun ω : Fin 2 => r₁Anti ω - r₂Anti ω)
      μAnti = 1 := by
    have hfun : (fun ω : Fin 2 => r₁Anti ω - r₂Anti ω) = r₁Anti - r₂Anti := rfl
    rw [hfun, ProbabilityTheory.variance_sub hR₁ hR₂, hvar₁, hcov, hvar₂]
    norm_num
  have hpos : 0 < ProbabilityTheory.variance
      (fun ω : Fin 2 => r₁Anti ω - r₂Anti ω) μAnti := by
    rw [hvarDiff]
    norm_num
  have hweight : MathlibExt.Probability.Finance.TwoAssetMinVariance.minVarianceWeight
      μAnti r₁Anti r₂Anti = 1 / 2 := by
    unfold MathlibExt.Probability.Finance.TwoAssetMinVariance.minVarianceWeight
    rw [hvar₂, hcov, hvarDiff]
    norm_num
  refine ⟨hweight, ?_⟩
  have hmin :=
    MathlibExt.Probability.Finance.TwoAssetMinVariance.minVarianceWeight_isMinimizer
      hR₁ hR₂ hpos 0
  rw [hweight] at hmin
  rw [hweight]
  exact hmin

end MathlibExtTest.TwoAssetMinVariance
