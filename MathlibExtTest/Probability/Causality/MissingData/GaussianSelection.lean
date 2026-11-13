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
import MathlibExt.Probability.Distributions.GaussianCdf

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
  exact cdf_gaussianReal_zero

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
