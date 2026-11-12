/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Causality.MissingData.GaussianSelection
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.CDF
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.ConditionalProbability

/-! # Gaussian selection tests: boundary behavior of the Mills correction

Boundary checks for the Heckman Gaussian selection model: ignorability
without correlation, non-ignorability with correlation, endpoints of
the valid covariance region, positivity of selection, and the value at
zero.
-/

@[expose] public section

namespace MathlibExtTest.Probability.Causality.MissingData.GaussianSelection

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology
open MathlibExt.Probability.Causality.MissingData

/-- T1: with uncorrelated errors, selection is ignorable. -/
theorem T1_selected_mean_eq_mean {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {u η : Ω → ℝ}
    {c m σ₁₁ : ℝ} (hu : HasLaw u (gaussianReal 0 1) μ)
    (hη : HasLaw η (gaussianReal 0 1) μ)
    (hind : IndepFun u η μ) (hu_meas : Measurable u) :
    ∫ ω, m + (0 * u ω
      + Real.sqrt (σ₁₁ - 0 ^ 2) * η ω)
      ∂μ[|{ω | -c ≤ u ω}] = m := by
  have h := integral_cond_selected_outcome_eq (c := c) (m := m)
    (σ₁₁ := σ₁₁) (σ₁₂ := (0 : ℝ)) hu hη hind hu_meas
  simpa using h

/-- T2: with correlated errors, the selected mean differs from `m`. -/
theorem T2_selected_mean_ne_mean {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {u η : Ω → ℝ}
    {c m σ₁₁ σ₁₂ : ℝ} (hu : HasLaw u (gaussianReal 0 1) μ)
    (hη : HasLaw η (gaussianReal 0 1) μ)
    (hind : IndepFun u η μ) (hu_meas : Measurable u)
    (hne : σ₁₂ ≠ 0) :
    ∫ ω, m + (σ₁₂ * u ω
      + Real.sqrt (σ₁₁ - σ₁₂ ^ 2) * η ω)
      ∂μ[|{ω | -c ≤ u ω}] ≠ m := by
  have h_eq := integral_cond_selected_outcome_eq (c := c) (m := m)
    (σ₁₁ := σ₁₁) (σ₁₂ := σ₁₂) hu hη hind hu_meas
  rw [h_eq]
  have hlam : 0 < inverseMillsRatio c := inverseMillsRatio_pos c
  have hlamne : inverseMillsRatio c ≠ 0 := ne_of_gt hlam
  have hmul : σ₁₂ * inverseMillsRatio c ≠ 0 := by
    exact (mul_ne_zero_iff_right hlamne).mpr hne
  exact add_ne_left.mpr hmul

/-- T2: the selected mean exceeds `m` exactly for positive `σ₁₂`. -/
theorem T2_selected_mean_gt_iff {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {u η : Ω → ℝ}
    {c m σ₁₁ σ₁₂ : ℝ} (hu : HasLaw u (gaussianReal 0 1) μ)
    (hη : HasLaw η (gaussianReal 0 1) μ)
    (hind : IndepFun u η μ) (hu_meas : Measurable u) :
    (∫ ω, m + (σ₁₂ * u ω
      + Real.sqrt (σ₁₁ - σ₁₂ ^ 2) * η ω)
      ∂μ[|{ω | -c ≤ u ω}] > m) ↔ σ₁₂ > 0 := by
  have h_eq := integral_cond_selected_outcome_eq (c := c) (m := m)
    (σ₁₁ := σ₁₁) (σ₁₂ := σ₁₂) hu hη hind hu_meas
  rw [h_eq]
  have hlam : 0 < inverseMillsRatio c := inverseMillsRatio_pos c
  constructor
  · intro h
    have hX : 0 < σ₁₂ * inverseMillsRatio c := by
      exact (lt_add_iff_pos_right m).mp h
    exact (mul_pos_iff_of_pos_right hlam).mp hX
  · intro h
    have hX : 0 < σ₁₂ * inverseMillsRatio c := by
      exact Right.mul_pos h hlam
    exact (lt_add_iff_pos_right m).mpr hX

/-- T3: at correlation `+1`, the selected mean is `m + λ`. -/
theorem T3_mean_pos_corr {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {u η : Ω → ℝ}
    {c m : ℝ} (hu : HasLaw u (gaussianReal 0 1) μ)
    (hη : HasLaw η (gaussianReal 0 1) μ)
    (hind : IndepFun u η μ) (hu_meas : Measurable u) :
    ∫ ω, m + (1 * u ω
      + Real.sqrt (1 - 1 ^ 2) * η ω)
      ∂μ[|{ω | -c ≤ u ω}]
      = m + inverseMillsRatio c := by
  have h := integral_cond_selected_outcome_eq (c := c) (m := m)
    (σ₁₁ := (1 : ℝ)) (σ₁₂ := (1 : ℝ)) hu hη hind hu_meas
  simpa using h

/-- T3: at correlation `-1`, the selected mean is `m - λ`. -/
theorem T3_mean_neg_corr {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {u η : Ω → ℝ}
    {c m : ℝ} (hu : HasLaw u (gaussianReal 0 1) μ)
    (hη : HasLaw η (gaussianReal 0 1) μ)
    (hind : IndepFun u η μ) (hu_meas : Measurable u) :
    ∫ ω, m + ((-1) * u ω
      + Real.sqrt (1 - (-1) ^ 2) * η ω)
      ∂μ[|{ω | -c ≤ u ω}]
      = m - inverseMillsRatio c := by
  have h := integral_cond_selected_outcome_eq (c := c) (m := m)
    (σ₁₁ := (1 : ℝ)) (σ₁₂ := ((-1 : ℝ))) hu hη hind hu_meas
  rw [h]
  ring

/-- T3: at correlation `+1`, the outcome variance is one. -/
theorem T3_var_pos_corr {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {u η : Ω → ℝ}
    (hu : HasLaw u (gaussianReal 0 1) μ)
    (hη : HasLaw η (gaussianReal 0 1) μ)
    (hind : IndepFun u η μ) :
    Var[fun ω => 1 * u ω
      + Real.sqrt (1 - 1 ^ 2) * η ω; μ] = 1 := by
  have hv : (1 : ℝ) ^ 2 ≤ (1 : ℝ) := by simp
  exact variance_outcomeError hu hη hind hv

/-- T3: at correlation `-1`, the outcome variance is one. -/
theorem T3_var_neg_corr {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {u η : Ω → ℝ}
    (hu : HasLaw u (gaussianReal 0 1) μ)
    (hη : HasLaw η (gaussianReal 0 1) μ)
    (hind : IndepFun u η μ) :
    Var[fun ω => (-1) * u ω
      + Real.sqrt (1 - (-1) ^ 2) * η ω; μ] = 1 := by
  have hv : ((-1 : ℝ)) ^ 2 ≤ (1 : ℝ) := by norm_num
  exact variance_outcomeError hu hη hind hv

/-- T4: selection never makes the outcome missing with probability one. -/
theorem T4_selection_pos {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {u : Ω → ℝ} {c : ℝ}
    (hu : HasLaw u (gaussianReal 0 1) μ) :
    0 < μ.real {ω | -c ≤ u ω} := by
  rw [measureReal_selection_eq_cdf hu]
  have hlam : 0 < inverseMillsRatio c := inverseMillsRatio_pos c
  have h1 : (1 : ℝ≥0) ≠ 0 := one_ne_zero
  have hpdf : 0 < gaussianPDFReal 0 1 c := by
    exact gaussianPDFReal_pos 0 1 c h1
  unfold inverseMillsRatio at hlam
  exact (div_pos_iff_of_pos_left hpdf).mp hlam

/-- T5: the standard normal cdf at zero equals one half. -/
theorem T5_cdf_zero_eq_half :
    cdf (gaussianReal 0 1) 0 = 1 / 2 := by
  have hIic : MeasurableSet (Set.Iic (0 : ℝ)) := by simp
  have hIoi : MeasurableSet (Set.Ioi (0 : ℝ)) := by simp
  have hIio : MeasurableSet (Set.Iio (0 : ℝ)) := by simp
  have hdisj : Disjoint (Set.Iic (0 : ℝ)) (Set.Ioi (0 : ℝ)) := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    simp only [Set.mem_Iic, Set.mem_Ioi] at hx1 hx2
    linarith
  have hunion : Set.Iic (0 : ℝ) ∪ Set.Ioi (0 : ℝ) = Set.univ := by
    ext x
    simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ioi,
      Set.mem_univ]
    exact iff_true_intro (le_or_gt x 0)
  have huniv : (gaussianReal 0 1) Set.univ = 1 := by
    exact measure_univ
  have hsplit : (gaussianReal 0 1) Set.univ
      = (gaussianReal 0 1) (Set.Iic 0)
        + (gaussianReal 0 1) (Set.Ioi 0) := by
    rw [← hunion]
    exact measure_union hdisj hIoi
  have hneg : AEMeasurable (fun x : ℝ => -x)
      (gaussianReal 0 1) := by measurability
  have hpre : (fun x : ℝ => -x) ⁻¹' Set.Ioi (0 : ℝ)
      = Set.Iio (0 : ℝ) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_Iio]
    constructor
    · intro h
      linarith
    · intro h
      linarith
  have hmap : Measure.map (fun x : ℝ => -x)
        (gaussianReal 0 1) (Set.Ioi 0)
      = (gaussianReal 0 1) ((fun x : ℝ => -x) ⁻¹' Set.Ioi 0) :=
    MeasureTheory.Measure.map_apply_of_aemeasurable hneg hIoi
  rw [hpre] at hmap
  have hsym : Measure.map (fun x : ℝ => -x)
        (gaussianReal 0 1) = gaussianReal (-0) 1 :=
    gaussianReal_map_neg
  simp only [neg_zero] at hsym
  rw [hsym] at hmap
  have hIio_eq : (gaussianReal 0 1) (Set.Iio (0 : ℝ))
      = (gaussianReal 0 1) (Set.Ioi (0 : ℝ)) := hmap.symm
  have hvol0 : volume ({0} : Set ℝ) = 0 := by simp
  have habs := gaussianReal_absolutelyContinuous
    (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) one_ne_zero
  have hnull : gaussianReal 0 1 {0} = 0 := habs hvol0
  have hdecomp : Set.Iic (0 : ℝ)
      = Set.Iio (0 : ℝ) ∪ {0} := by
    ext x
    simp only [Set.mem_Iic, Set.mem_union, Set.mem_Iio,
      Set.mem_singleton_iff]
    constructor
    · intro h
      by_cases heq : x = 0
      · exact Or.inr heq
      · exact Or.inl (lt_of_le_of_ne h heq)
    · intro h
      cases h with
      | inl hlt => exact le_of_lt hlt
      | inr heq => rw [heq]
  have hdisj2 : Disjoint (Set.Iio (0 : ℝ)) ({0} : Set ℝ) := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    simp only [Set.mem_Iio, Set.mem_singleton_iff] at hx1 hx2
    linarith
  have hsing : MeasurableSet ({0} : Set ℝ) := by simp
  have hIic_eq : (gaussianReal 0 1) (Set.Iic (0 : ℝ))
      = (gaussianReal 0 1) (Set.Iio (0 : ℝ)) := by
    rw [hdecomp]
    have h2 : (gaussianReal 0 1) (Set.Iio 0 ∪ {0})
        = (gaussianReal 0 1) (Set.Iio 0)
          + (gaussianReal 0 1) ({0} : Set ℝ) := by
      exact measure_union hdisj2 hsing
    rw [h2, hnull, add_zero]
  have hcdf : cdf (gaussianReal 0 1) 0
      = (gaussianReal 0 1).real (Set.Iic 0) :=
    cdf_eq_real (gaussianReal 0 1) 0
  rw [hcdf]
  rw [huniv] at hsplit
  have hfin1 : (gaussianReal 0 1) (Set.Iic 0) ≠ ∞ := by
    exact measure_ne_top _ _
  have hfin2 : (gaussianReal 0 1) (Set.Ioi 0) ≠ ∞ := by
    exact measure_ne_top _ _
  have hreal_add : ((1 : ℝ≥0∞)).toReal
      = ((gaussianReal 0 1) (Set.Iic 0)
        + (gaussianReal 0 1) (Set.Ioi 0)).toReal := by
    rw [← hsplit]
  rw [ENNReal.toReal_add hfin1 hfin2] at hreal_add
  simp only [ENNReal.toReal_one] at hreal_add
  have h_eq_real : (gaussianReal 0 1).real (Set.Ioi 0)
      = (gaussianReal 0 1).real (Set.Iic 0) := by
    have h3 : (gaussianReal 0 1) (Set.Ioi 0)
        = (gaussianReal 0 1) (Set.Iic 0) := by
      rw [← hIio_eq, ← hIic_eq]
    exact congrArg ENNReal.toReal h3
  simp only [← MeasureTheory.measureReal_def] at hreal_add
  rw [h_eq_real] at hreal_add
  have h2eq : (1 : ℝ)
      = (gaussianReal 0 1).real (Set.Iic 0)
        + (gaussianReal 0 1).real (Set.Iic 0) := hreal_add
  have hhalf : (gaussianReal 0 1).real (Set.Iic 0) = 1 / 2 := by
    linarith
  exact hhalf

/-- T5: the Mills ratio at zero equals twice the density at zero. -/
theorem T5_mills_zero_eq :
    inverseMillsRatio 0
      = 2 * gaussianPDFReal 0 1 0 := by
  unfold inverseMillsRatio
  rw [T5_cdf_zero_eq_half]
  have hinv : ((1 : ℝ) / 2)⁻¹ = (2 : ℝ) := by norm_num
  rw [div_eq_mul_inv, hinv, mul_comm]

end MathlibExtTest.Probability.Causality.MissingData.GaussianSelection

end
