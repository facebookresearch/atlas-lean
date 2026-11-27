/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
public import Mathlib.MeasureTheory.Measure.Tilted

/-!
# Normalized KL test bound

For probability measures `μ, ν` and a measurable score `f`
normalized by `∫ exp f dν = 1`, the Donsker-Varadhan form
`ofReal (∫ f dμ) ≤ klDiv μ ν` holds. The proof tilts `ν` by
`exp f` and uses KL nonnegativity; a nonnormalized constant score
shows the normalization cannot be dropped.

-/

@[expose] public section

open MeasureTheory Real
open scoped ENNReal
namespace MathlibExt.InformationTheory.NormalizedKLTestBound

open _root_.InformationTheory

private lemma ennreal_two_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by
  intro h
  have h2 := congrArg ENNReal.toReal h
  simp only [ENNReal.toReal_ofNat, ENNReal.toReal_zero] at h2
  norm_num at h2

private lemma inv_two_ne_top : (2⁻¹ : ℝ≥0∞) ≠ ∞ :=
  ENNReal.inv_ne_top.mpr ennreal_two_ne_zero

private lemma toReal_inv_two : (2⁻¹ : ℝ≥0∞).toReal = 2⁻¹ := by simp

private lemma measurable_bool (g : Bool → ℝ) : Measurable g := measurable_from_top

private lemma integrable_bool_finite (μ : Measure Bool) [IsFiniteMeasure μ]
    (g : Bool → ℝ) (hg : Measurable g) : Integrable g μ := by
  refine Integrable.of_bound hg.aestronglyMeasurable (‖g true‖ + ‖g false‖) ?_
  filter_upwards with b
  cases b
  · exact le_add_of_nonneg_left (norm_nonneg _)
  · exact le_add_of_nonneg_right (norm_nonneg _)

/-! ### Proof-facing lemmas -/

/-- Absolute continuity passes to the exponential tilt: with `exp ∘ f` integrable, `ν ≪ ν.tilted f`,
so `μ ≪ ν` gives `μ ≪ ν.tilted f`. -/
theorem absolutelyContinuous_tilted_of_absolutelyContinuous {α : Type*} [MeasurableSpace α]
    {μ ν : Measure α} {f : α → ℝ} (hμν : μ ≪ ν) (hfν : Integrable (fun x ↦ Real.exp (f x)) ν) :
    μ ≪ ν.tilted f := by
  exact hμν.trans (absolutelyContinuous_tilted hfν)

/-- Finite-KL branch: for `μ ≪ ν` with integrable log-likelihood ratio and a normalized score `f`,
`∫ f dμ ≤ ∫ llr μ ν dμ` (Gibbs' inequality against the probability `ν.tilted f`). -/
theorem integral_le_integral_llr {α : Type*} [MeasurableSpace α] (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {f : α → ℝ}
    (hfμ : Integrable f μ) (hfν : Integrable (fun x ↦ Real.exp (f x)) ν)
    (hnorm : ∫ x, Real.exp (f x) ∂ν = 1) (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) :
    ∫ x, f x ∂μ ≤ ∫ x, llr μ ν x ∂μ := by
  have := isProbabilityMeasure_tilted hfν
  have hμt : μ ≪ ν.tilted f :=
    absolutelyContinuous_tilted_of_absolutelyContinuous hμν hfν
  have h_int' : Integrable (llr μ (ν.tilted f)) μ :=
    integrable_llr_tilted_right hμν hfμ h_int hfν
  have hgibbs := integral_llr_add_sub_measure_univ_nonneg hμt h_int'
  have heq := integral_llr_tilted_right hμν hfμ hfν h_int
  rw [hnorm, Real.log_one, add_zero] at heq
  have hT : (ν.tilted f).real Set.univ = 1 := probReal_univ
  have hM : μ.real Set.univ = 1 := probReal_univ
  linarith

/-! ### Headline -/

/-- **Normalized KL test bound.** For probability measures `μ`, `ν` and a measurable real score `f`
with `f` integrable for `μ`, `exp ∘ f` integrable for `ν` and `∫ exp f dν = 1`,
`KL(μ ‖ ν) ≥ ofReal (∫ f dμ)` in `ℝ≥0∞` (KL in nats). -/
theorem ofReal_integral_le_klDiv {α : Type*} [MeasurableSpace α] (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {f : α → ℝ} (hf : Measurable f)
    (hfμ : Integrable f μ) (hfν : Integrable (fun x ↦ Real.exp (f x)) ν)
    (hnorm : ∫ x, Real.exp (f x) ∂ν = 1) :
    ENNReal.ofReal (∫ x, f x ∂μ) ≤ klDiv μ ν := by
  by_cases hμν : μ ≪ ν
  · by_cases h_int : Integrable (llr μ ν) μ
    · rw [klDiv_of_ac_of_integrable hμν h_int]
      have h := integral_le_integral_llr μ ν hfμ hfν hnorm hμν h_int
      have hT : ν.real Set.univ = 1 := probReal_univ
      have hM : μ.real Set.univ = 1 := probReal_univ
      rw [hT, hM, add_sub_cancel_right]
      exact ENNReal.ofReal_le_ofReal h
    · rw [klDiv_of_not_integrable h_int]
      exact le_top
  · rw [klDiv_of_not_ac hμν]
    exact le_top

/-! ### Validation -/

/-- Validation, `f = 0`: the zero score is normalized for every probability `ν`, and the bound reads
`ofReal 0 ≤ KL(μ ‖ ν)`. -/
theorem integral_exp_zero_eq_one_and_ofReal_integral_zero_le_klDiv {α : Type*}
    [MeasurableSpace α] (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ∫ x, Real.exp ((0 : α → ℝ) x) ∂ν = 1 ∧
      ENNReal.ofReal (∫ x, (0 : α → ℝ) x ∂μ) ≤ klDiv μ ν := by
  have h1 : ∫ x, Real.exp ((0 : α → ℝ) x) ∂ν = 1 := by
    simp only [Pi.zero_apply, Real.exp_zero, integral_const, probReal_univ, one_smul]
  refine ⟨h1, ofReal_integral_le_klDiv μ ν measurable_zero (integrable_zero _ _ μ) ?_ h1⟩
  simp

/-- The uniform law on `Bool`. -/
noncomputable def uniformBool : Measure Bool :=
  (2⁻¹ : ℝ≥0∞) • Measure.dirac true + (2⁻¹ : ℝ≥0∞) • Measure.dirac false

/-- A normalized two-point score: `log (3/2)` at `true`, `log (1/2)` at `false`. -/
noncomputable def twoPointScore (b : Bool) : ℝ :=
  if b then Real.log (3 / 2) else Real.log (1 / 2)

private lemma twoPointScore_true : twoPointScore true = Real.log (3 / 2) := rfl

private lemma twoPointScore_false : twoPointScore false = Real.log (1 / 2) := rfl

private lemma integral_uniformBool (g : Bool → ℝ) :
    ∫ b, g b ∂uniformBool
      = (2⁻¹ : ℝ≥0∞).toReal * g true + (2⁻¹ : ℝ≥0∞).toReal * g false := by
  have h1 : Integrable g ((2⁻¹ : ℝ≥0∞) • Measure.dirac true) :=
    (integrable_dirac (by simp)).smul_measure inv_two_ne_top
  have h2 : Integrable g ((2⁻¹ : ℝ≥0∞) • Measure.dirac false) :=
    (integrable_dirac (by simp)).smul_measure inv_two_ne_top
  unfold uniformBool
  rw [integral_add_measure h1 h2]
  simp only [integral_smul_measure, integral_dirac, smul_eq_mul]

private lemma isProbabilityMeasure_uniformBool : IsProbabilityMeasure uniformBool := by
  refine ⟨?_⟩
  unfold uniformBool
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul,
    Measure.dirac_apply_of_mem (Set.mem_univ true),
    Measure.dirac_apply_of_mem (Set.mem_univ false), mul_one]
  exact ENNReal.inv_two_add_inv_two

private lemma integrable_exp_twoPointScore :
    Integrable (fun b ↦ Real.exp (twoPointScore b)) uniformBool := by
  have := isProbabilityMeasure_uniformBool
  exact integrable_bool_finite _ _ (measurable_bool _)

/-- Validation, two-point law: the score is normalized against the uniform law,
`½ · 3/2 + ½ · 1/2 = 1`. -/
theorem integral_exp_twoPointScore :
    ∫ b, Real.exp (twoPointScore b) ∂uniformBool = 1 := by
  rw [integral_uniformBool]
  simp only [toReal_inv_two, twoPointScore_true, twoPointScore_false,
    Real.exp_log (show (0:ℝ) < 3 / 2 by norm_num),
    Real.exp_log (show (0:ℝ) < 1 / 2 by norm_num)]
  norm_num

/-- Validation, two-point law: under the tilted law `(3/4, 1/4)` the score has mean
`3/4 log (3/2) + 1/4 log (1/2)` (about `0.1308`). -/
theorem integral_twoPointScore_tilted :
    ∫ b, twoPointScore b ∂(uniformBool.tilted twoPointScore) =
      3 / 4 * Real.log (3 / 2) + 1 / 4 * Real.log (1 / 2) := by
  rw [integral_tilted, integral_exp_twoPointScore]
  simp only [div_one, smul_eq_mul]
  rw [integral_uniformBool]
  simp only [toReal_inv_two, twoPointScore_true, twoPointScore_false,
    Real.exp_log (show (0:ℝ) < 3 / 2 by norm_num),
    Real.exp_log (show (0:ℝ) < 1 / 2 by norm_num)]
  ring

/-- Validation, two-point law: for `μ = ν.tilted f` the normalized bound is attained,
`KL(μ ‖ ν) = ofReal (∫ f dμ)`. -/
theorem klDiv_tilted_twoPointScore :
    klDiv (uniformBool.tilted twoPointScore) uniformBool =
      ENNReal.ofReal (∫ b, twoPointScore b ∂(uniformBool.tilted twoPointScore)) := by
  have := isProbabilityMeasure_uniformBool
  have := isProbabilityMeasure_tilted integrable_exp_twoPointScore
  have h_int : Integrable (llr (uniformBool.tilted twoPointScore) uniformBool)
      (uniformBool.tilted twoPointScore) :=
    integrable_bool_finite _ _ (measurable_llr _ _)
  rw [klDiv_of_ac_of_integrable (tilted_absolutelyContinuous uniformBool twoPointScore) h_int,
    probReal_univ, probReal_univ, add_sub_cancel_right]
  congr 1
  have hae : llr (uniformBool.tilted twoPointScore) uniformBool
      =ᵐ[uniformBool.tilted twoPointScore] twoPointScore := by
    have h := Measure.AbsolutelyContinuous.ae_eq
      (tilted_absolutelyContinuous uniformBool twoPointScore)
      (log_rnDeriv_tilted_left_self (μ := uniformBool) (f := twoPointScore)
        integrable_exp_twoPointScore)
    rw [integral_exp_twoPointScore, Real.log_one] at h
    simp only [sub_zero] at h
    exact h
  exact integral_congr_ae hae

/-- Violated premise (normalization): a constant score `c > 0` has `∫ exp c dν = exp c ≠ 1`, and
the bound without its log-normalizer fails at `μ = ν`: `KL(ν ‖ ν) = 0 < ofReal c`. -/
theorem klDiv_self_lt_ofReal_integral_const {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] {c : ℝ} (hc : 0 < c) :
    ∫ _x, Real.exp c ∂ν ≠ 1 ∧ klDiv ν ν < ENNReal.ofReal (∫ _x, c ∂ν) := by
  refine ⟨?_, ?_⟩
  · rw [integral_const, probReal_univ, one_smul]
    exact ne_of_gt (Real.one_lt_exp_iff.mpr hc)
  · rw [klDiv_self, integral_const, probReal_univ, one_smul]
    exact ENNReal.ofReal_pos.mpr hc

end MathlibExt.InformationTheory.NormalizedKLTestBound
