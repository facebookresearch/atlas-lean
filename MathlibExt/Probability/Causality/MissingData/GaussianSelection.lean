/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.CDF
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Gaussian sample selection: the inverse Mills ratio correction

Heckman's Gaussian selection model with standardized selection error.
Covariates are fixed, giving a mean `m = X₁β₁` and a selection index
`c = X₂β₂`. Selection holds when `-c ≤ u` for a standard normal `u`,
so `Z = -c` and `λ = φ(c) / Φ(c)` with `φ` the standard normal density
and `Φ` its distribution function.

The outcome error is `σ₁₂ * u + √(σ₁₁ - σ₁₂ ^ 2) * η` for independent
standard normals `u` and `η`; the selection error is `u` itself with
unit variance. The covariance matrix with `Var U₁ = σ₁₁`,
`Cov(U₁, U₂) = σ₁₂`, `Var U₂ = 1` is valid exactly when
`σ₁₂ ^ 2 ≤ σ₁₁`. Selection probability is `Φ(c) > 0`, a consequence of
normality rather than an extra hypothesis. Identification comes from the
normal functional form; this is not a nonparametric identification
result.

## References

* J. J. Heckman, Sample Selection Bias as a Specification Error,
  Econometrica 47(1) (1979), 153-161.

## Not covered

Estimation (probit first stage, two-step estimator, standard errors),
random covariates, exclusion restrictions, nonnormal errors and
semiparametric selection models.
-/

@[expose] public section

namespace MathlibExt.Probability.Causality.MissingData

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

private theorem pdf_pos (x : ℝ) :
    0 < gaussianPDFReal 0 1 x := by
  have hdef := gaussianPDFReal_def (μ := (0 : ℝ)) (v := (1 : ℝ≥0))
  have h1 : gaussianPDFReal 0 1 x
      = (√(2 * Real.pi * (1 : ℝ)))⁻¹
        * Real.exp (-(x - 0) ^ 2 / (2 * (1 : ℝ))) := by
    have h2 := congrFun hdef x
    simpa using h2
  rw [h1]
  positivity

private theorem cdf_gaussian_pos (c : ℝ) :
    0 < cdf (gaussianReal 0 1) c := by
  rw [cdf_eq_real (gaussianReal 0 1) c]
  have hIoo : MeasurableSet (Set.Ioo (c - 1) c) := by simp
  have hsub : Set.Ioo (c - 1) c ⊆ Set.Iic c := by
    intro x hx
    simp only [Set.mem_Ioo, Set.mem_Iic] at hx ⊢
    exact le_of_lt hx.2
  have hvol : 0 < volume (Set.Ioo (c - 1) c) := by
    have hlt : c - 1 < c := by linarith
    exact (Measure.measure_Ioo_pos _).mpr hlt
  have hcont : Continuous (gaussianPDFReal 0 1) := by
    have hdef := gaussianPDFReal_def (μ := (0 : ℝ)) (v := (1 : ℝ≥0))
    rw [hdef]
    continuity
  have hcompact : IsCompact (Set.Icc (c - 1) c) := isCompact_Icc
  have hcontOn : ContinuousOn (gaussianPDFReal 0 1)
      (Set.Icc (c - 1) c) :=
    hcont.continuousOn
  have hint_Icc : IntegrableOn (gaussianPDFReal 0 1)
      (Set.Icc (c - 1) c) volume := by
    exact ContinuousOn.integrableOn_Icc hcontOn
  have hsub2 : Set.Ioo (c - 1) c ⊆ Set.Icc (c - 1) c := by
    intro x hx
    simp only [Set.mem_Ioo, Set.mem_Icc] at hx ⊢
    exact ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  have hint_Ioo : IntegrableOn (gaussianPDFReal 0 1)
      (Set.Ioo (c - 1) c) volume := by
    exact IntegrableOn.mono_set hint_Icc hsub2
  have hpos_mem : ∀ x ∈ Set.Ioo (c - 1) c,
      0 < gaussianPDFReal 0 1 x := by
    intro x _
    exact pdf_pos x
  have hvol_ne : volume (Set.Ioo (c - 1) c) ≠ 0 :=
    ne_of_gt hvol
  have hint_pos : 0 < ∫ x in Set.Ioo (c - 1) c,
      gaussianPDFReal 0 1 x ∂volume := by
    have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioo (c - 1) c)]
        (gaussianPDFReal 0 1) := by
      filter_upwards with x
      exact le_of_lt (pdf_pos x)
    have hiff := MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae
      hnn hint_Ioo
    have hsupp : Function.support (gaussianPDFReal 0 1)
        = Set.univ := by
      ext x
      simp only [Function.mem_support, Set.mem_univ, iff_true]
      exact ne_of_gt (pdf_pos x)
    rw [hsupp, Set.univ_inter] at hiff
    exact hiff.mpr hvol
  have hreal_eq : (gaussianReal 0 1).real (Set.Ioo (c - 1) c)
      = ∫ x in Set.Ioo (c - 1) c, (1 : ℝ) ∂gaussianReal 0 1 := by
    have h1 : ∫ x, (Set.Ioo (c - 1) c).indicator
        (fun _ => (1 : ℝ)) x ∂gaussianReal 0 1
        = (gaussianReal 0 1).real (Set.Ioo (c - 1) c) := by
      rw [integral_indicator hIoo, integral_const,
        MeasureTheory.measureReal_restrict_apply_univ, smul_eq_mul,
        mul_one]
    rw [integral_indicator hIoo] at h1
    exact h1.symm
  have hdens : ∫ x in Set.Ioo (c - 1) c, (1 : ℝ) ∂gaussianReal 0 1
      = ∫ x in Set.Ioo (c - 1) c,
        gaussianPDFReal 0 1 x ∂volume := by
    rw [← integral_indicator hIoo]
    have hv : (1 : ℝ≥0) ≠ 0 := one_ne_zero
    have heq : ∫ x, (Set.Ioo (c - 1) c).indicator
        (fun _ => (1 : ℝ)) x ∂gaussianReal 0 1
        = ∫ x, gaussianPDFReal 0 1 x •
          (Set.Ioo (c - 1) c).indicator (fun _ => (1 : ℝ)) x
          ∂volume :=
      integral_gaussianReal_eq_integral_smul hv
    rw [heq]
    have hfun : (fun x : ℝ => gaussianPDFReal 0 1 x •
        (Set.Ioo (c - 1) c).indicator (fun _ => (1 : ℝ)) x)
        = (Set.Ioo (c - 1) c).indicator (gaussianPDFReal 0 1) := by
      funext x
      by_cases hx : x ∈ Set.Ioo (c - 1) c
      · simp [hx, smul_eq_mul]
      · simp [hx]
    rw [hfun, integral_indicator hIoo]
  have hIoo_pos : 0 < (gaussianReal 0 1).real
      (Set.Ioo (c - 1) c) := by
    rw [hreal_eq, hdens]
    exact hint_pos
  have hle : (gaussianReal 0 1).real (Set.Ioo (c - 1) c)
      ≤ (gaussianReal 0 1).real (Set.Iic c) := by
    have hmono : (gaussianReal 0 1) (Set.Ioo (c - 1) c)
        ≤ (gaussianReal 0 1) (Set.Iic c) :=
      measure_mono hsub
    have hfin : (gaussianReal 0 1) (Set.Iic c) ≠ ∞ :=
      measure_ne_top _ _
    exact ENNReal.toReal_mono hfin hmono
  exact lt_of_lt_of_le hIoo_pos hle

private theorem pdf_even (c : ℝ) :
    gaussianPDFReal 0 1 (-c) = gaussianPDFReal 0 1 c := by
  have hdef := gaussianPDFReal_def (μ := (0 : ℝ)) (v := (1 : ℝ≥0))
  have h1 : gaussianPDFReal 0 1 (-c)
      = (√(2 * Real.pi * (1 : ℝ)))⁻¹
        * Real.exp (-(-c - 0) ^ 2 / (2 * (1 : ℝ))) := by
    have h2 := congrFun hdef (-c)
    simpa using h2
  have h2 : gaussianPDFReal 0 1 c
      = (√(2 * Real.pi * (1 : ℝ)))⁻¹
        * Real.exp (-(c - 0) ^ 2 / (2 * (1 : ℝ))) := by
    have h3 := congrFun hdef c
    simpa using h3
  rw [h1, h2]
  have hsq : (-c - 0) ^ 2 = (c - 0) ^ 2 := by ring
  rw [hsq]

private theorem integral_Ioi_mul_pdf (c : ℝ) :
    ∫ x in Set.Ioi (-c), x * gaussianPDFReal 0 1 x ∂volume
      = gaussianPDFReal 0 1 c := by
  have hdef := gaussianPDFReal_def (μ := (0 : ℝ)) (v := (1 : ℝ≥0))
  have hcont : Continuous (gaussianPDFReal 0 1) := by
    rw [hdef]
    continuity
  have hfcont : Continuous
      (fun x : ℝ => -gaussianPDFReal 0 1 x) :=
    hcont.neg
  have hwithin : ContinuousWithinAt
      (fun x : ℝ => -gaussianPDFReal 0 1 x)
      (Set.Ici (-c)) (-c) :=
    hfcont.continuousWithinAt
  have hderiv : ∀ x ∈ Set.Ioi (-c), HasDerivAt
      (fun x : ℝ => -gaussianPDFReal 0 1 x)
      (x * gaussianPDFReal 0 1 x) x := by
    intro x _
    simp only [hdef]
    have hid : HasDerivAt (fun x : ℝ => x) 1 x :=
      hasDerivAt_id x
    have hsub : HasDerivAt (fun x : ℝ => x - 0) 1 x :=
      hid.sub_const 0
    have hpow : HasDerivAt (fun x : ℝ => (x - 0) ^ 2)
        (2 * (x - 0)) x := by
      simpa using hasDerivAt_pow 2 x
    have hneg : HasDerivAt (fun x : ℝ => -((x - 0) ^ 2))
        (-(2 * (x - 0))) x :=
      hpow.neg
    have hdiv : HasDerivAt
        (fun x : ℝ => -((x - 0) ^ 2) / (2 * (1 : ℝ)))
        (-(2 * (x - 0)) / (2 * (1 : ℝ))) x :=
      hneg.div_const (2 * (1 : ℝ))
    have heq1 : -(2 * (x - 0)) / (2 * (1 : ℝ)) = -x := by
      ring
    have hdiv2 : HasDerivAt
        (fun x : ℝ => -((x - 0) ^ 2) / (2 * (1 : ℝ))) (-x) x :=
      heq1 ▸ hdiv
    have hexp : HasDerivAt
        (fun x : ℝ => Real.exp (-((x - 0) ^ 2) / (2 * (1 : ℝ))))
        (Real.exp (-((x - 0) ^ 2) / (2 * (1 : ℝ))) * (-x)) x :=
      hdiv2.exp
    have hmul : HasDerivAt
        (fun x : ℝ => (√(2 * Real.pi * (1 : ℝ)))⁻¹
          * Real.exp (-((x - 0) ^ 2) / (2 * (1 : ℝ))))
        ((√(2 * Real.pi * (1 : ℝ)))⁻¹
          * (Real.exp (-((x - 0) ^ 2) / (2 * (1 : ℝ))) * (-x))) x :=
      hexp.const_mul _
    have hneg2 : HasDerivAt
        (fun x : ℝ => -((√(2 * Real.pi * (1 : ℝ)))⁻¹
          * Real.exp (-((x - 0) ^ 2) / (2 * (1 : ℝ)))))
        (-((√(2 * Real.pi * (1 : ℝ)))⁻¹
          * (Real.exp (-((x - 0) ^ 2) / (2 * (1 : ℝ)))
            * (-x)))) x :=
      hmul.neg
    have heq2 : -((√(2 * Real.pi * (1 : ℝ)))⁻¹
          * (Real.exp (-((x - 0) ^ 2) / (2 * (1 : ℝ))) * (-x)))
        = x * ((√(2 * Real.pi * (1 : ℝ)))⁻¹
          * Real.exp (-((x - 0) ^ 2) / (2 * (1 : ℝ)))) := by
      ring
    exact heq2 ▸ hneg2
  have hint : IntegrableOn
      (fun x : ℝ => x * gaussianPDFReal 0 1 x)
      (Set.Ioi (-c)) volume := by
    have hmem : MemLp id (2 : ℝ≥0∞) (gaussianReal 0 1) :=
      memLp_id_gaussianReal 2
    have h1 : MemLp id (1 : ℝ≥0∞) (gaussianReal 0 1) := by
      exact hmem.mono_exponent one_le_two
    have hint_id : Integrable id (gaussianReal 0 1) := by
      exact memLp_one_iff_integrable.mp h1
    have hv : (1 : ℝ≥0) ≠ 0 := one_ne_zero
    have hgauss : gaussianReal (0 : ℝ) (1 : ℝ≥0)
        = volume.withDensity (gaussianPDF 0 1) :=
      gaussianReal_of_var_ne_zero 0 hv
    rw [hgauss] at hint_id
    have hmeas : Measurable (gaussianPDF (0 : ℝ) (1 : ℝ≥0)) := by
      measurability
    have hflt : ∀ᵐ x ∂volume, gaussianPDF 0 1 x < ⊤ :=
      Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top
    have htrans := (MeasureTheory.integrable_withDensity_iff_integrable_smul'
      hmeas hflt).mp hint_id
    have hfun : (fun x : ℝ => (gaussianPDF 0 1 x).toReal • id x)
        = (fun x : ℝ => x * gaussianPDFReal 0 1 x) := by
      funext x
      have hnn : 0 ≤ gaussianPDFReal 0 1 x := le_of_lt (pdf_pos x)
      have htr : (gaussianPDF 0 1 x).toReal
          = gaussianPDFReal 0 1 x :=
        ENNReal.toReal_ofReal hnn
      rw [htr, smul_eq_mul]
      exact mul_comm _ _
    rw [hfun] at htrans
    exact htrans.integrableOn
  have hlim : Filter.Tendsto
      (fun x : ℝ => -gaussianPDFReal 0 1 x) Filter.atTop (𝓝 0) := by
    have hexp : Filter.Tendsto (fun y : ℝ => Real.exp (-y))
        Filter.atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero
    have hpow : Filter.Tendsto (fun x : ℝ => x ^ 2 / 2)
        Filter.atTop Filter.atTop := by
      have hid : Filter.Tendsto (fun x : ℝ => x)
          Filter.atTop Filter.atTop :=
        Filter.tendsto_id
      have hsq : Filter.Tendsto (fun x : ℝ => x ^ 2)
          Filter.atTop Filter.atTop := by
        exact Filter.tendsto_pow_atTop two_ne_zero
      exact hsq.atTop_div_const two_pos
    have hcomp : Filter.Tendsto
        (fun x : ℝ => Real.exp (-(x ^ 2 / 2)))
        Filter.atTop (𝓝 0) :=
      hexp.comp hpow
    have hC : Filter.Tendsto (fun x : ℝ =>
        (√(2 * Real.pi * (1 : ℝ)))⁻¹ * Real.exp (-(x ^ 2 / 2)))
        Filter.atTop (𝓝 ((√(2 * Real.pi * (1 : ℝ)))⁻¹ * 0)) :=
      hcomp.const_mul _
    rw [mul_zero] at hC
    have hneg : Filter.Tendsto (fun x : ℝ =>
        -((√(2 * Real.pi * (1 : ℝ)))⁻¹ * Real.exp (-(x ^ 2 / 2))))
        Filter.atTop (𝓝 (-0)) :=
      hC.neg
    rw [neg_zero] at hneg
    have heq : ∀ x : ℝ,
        -((√(2 * Real.pi * (1 : ℝ)))⁻¹ * Real.exp (-(x ^ 2 / 2)))
        = -gaussianPDFReal 0 1 x := by
      intro x
      have hpx : gaussianPDFReal 0 1 x
          = (√(2 * Real.pi * (1 : ℝ)))⁻¹
            * Real.exp (-(x - 0) ^ 2 / (2 * (1 : ℝ))) := by
        have h4 := congrFun hdef x
        simpa using h4
      rw [hpx]
      congr 1
      congr 1
      congr 1
      simp only [sub_zero, mul_one, neg_div]
    exact hneg.congr heq
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto
    (f := fun x : ℝ => -gaussianPDFReal 0 1 x)
    (f' := fun x : ℝ => x * gaussianPDFReal 0 1 x)
    (a := -c) (m := (0 : ℝ))
    hwithin hderiv hint hlim
  have hev := pdf_even c
  calc ∫ x in Set.Ioi (-c), x * gaussianPDFReal 0 1 x ∂volume
      = 0 - -gaussianPDFReal 0 1 (-c) := hftc
    _ = gaussianPDFReal 0 1 (-c) := by ring
    _ = gaussianPDFReal 0 1 c := hev

private theorem memLp_of_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → ℝ}
    (hX : HasLaw X (gaussianReal 0 1) μ) : MemLp X 2 μ := by
  have hmem : MemLp id (2 : ℝ≥0∞) (gaussianReal 0 1) :=
    memLp_id_gaussianReal 2
  have h2 := hX.memLp hmem
  simpa using h2

private theorem variance_of_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → ℝ}
    (hX : HasLaw X (gaussianReal 0 1) μ) : Var[X; μ] = 1 := by
  have heq := hX.variance_eq
  have hid : Var[id; gaussianReal (0 : ℝ) (1 : ℝ≥0)] = 1 := by
    have h3 := variance_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0))
    rw [NNReal.coe_one] at h3
    exact h3
  rw [heq]
  exact hid

/-- Heckman's lambda at `Z = -c` with unit selection variance:
`φ(c) / Φ(c)` for the standard normal density `φ` and cdf `Φ`. -/
noncomputable def inverseMillsRatio (c : ℝ) : ℝ :=
  gaussianPDFReal 0 1 c / cdf (gaussianReal 0 1) c

/-- The inverse Mills ratio is strictly positive for every `c`. -/
theorem inverseMillsRatio_pos (c : ℝ) :
    0 < inverseMillsRatio c := by
  unfold inverseMillsRatio
  apply div_pos (pdf_pos c)
  exact cdf_gaussian_pos c

/-- The probit selection probability equals the Gaussian cdf. -/
theorem measureReal_selection_eq_cdf {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {u : Ω → ℝ} {c : ℝ}
    (hu : HasLaw u (gaussianReal 0 1) μ) :
    μ.real {ω | -c ≤ u ω} = cdf (gaussianReal 0 1) c := by
  have hIci : MeasurableSet (Set.Ici (-c)) := by simp
  have hIic : MeasurableSet (Set.Iic c) := by simp
  have hmap : μ (u ⁻¹' Set.Ici (-c))
      = Measure.map u μ (Set.Ici (-c)) :=
    (MeasureTheory.Measure.map_apply_of_aemeasurable
      hu.aemeasurable hIci).symm
  have hmeq : Measure.map u μ = gaussianReal 0 1 := hu.2
  have h1 : μ (u ⁻¹' Set.Ici (-c))
      = (gaussianReal 0 1) (Set.Ici (-c)) := by
    rw [hmap, hmeq]
  have hr1 : μ.real (u ⁻¹' Set.Ici (-c))
      = (gaussianReal 0 1).real (Set.Ici (-c)) :=
    congrArg ENNReal.toReal h1
  have hneg : AEMeasurable (fun x : ℝ => -x)
      (gaussianReal 0 1) := by measurability
  have hpre : (fun x : ℝ => -x) ⁻¹' Set.Iic c
      = Set.Ici (-c) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_Ici]
    constructor
    · intro h
      linarith
    · intro h
      linarith
  have hmapneg : Measure.map (fun x : ℝ => -x)
        (gaussianReal 0 1) (Set.Iic c)
      = (gaussianReal 0 1) ((fun x : ℝ => -x) ⁻¹' Set.Iic c) :=
    MeasureTheory.Measure.map_apply_of_aemeasurable hneg hIic
  rw [hpre] at hmapneg
  have hnegeq : Measure.map (fun x : ℝ => -x)
        (gaussianReal 0 1) = gaussianReal (-0) 1 :=
    gaussianReal_map_neg
  simp only [neg_zero] at hnegeq
  rw [hnegeq] at hmapneg
  have h2 : (gaussianReal 0 1) (Set.Ici (-c))
      = (gaussianReal 0 1) (Set.Iic c) :=
    hmapneg.symm
  have hr2 : (gaussianReal 0 1).real (Set.Ici (-c))
      = (gaussianReal 0 1).real (Set.Iic c) :=
    congrArg ENNReal.toReal h2
  have hcdf : cdf (gaussianReal 0 1) c
      = (gaussianReal 0 1).real (Set.Iic c) :=
    cdf_eq_real (gaussianReal 0 1) c
  calc μ.real {ω | -c ≤ u ω}
      = μ.real (u ⁻¹' Set.Ici (-c)) := rfl
    _ = (gaussianReal 0 1).real (Set.Ici (-c)) := hr1
    _ = (gaussianReal 0 1).real (Set.Iic c) := hr2
    _ = cdf (gaussianReal 0 1) c := hcdf.symm

/-- Heckman's second display with unit selection variance: the
truncated mean of the selection error equals the Mills ratio. -/
theorem integral_cond_selectionError_eq {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {u : Ω → ℝ} {c : ℝ}
    (hu : HasLaw u (gaussianReal 0 1) μ)
    (hu_meas : Measurable u) :
    ∫ ω, u ω ∂μ[|{ω | -c ≤ u ω}] = inverseMillsRatio c := by
  have hIci : MeasurableSet (Set.Ici (-c)) := by simp
  have hs : MeasurableSet {ω | -c ≤ u ω} := hu_meas hIci
  have hpos : 0 < μ.real {ω | -c ≤ u ω} := by
    rw [measureReal_selection_eq_cdf hu]
    exact cdf_gaussian_pos c
  have hcond : μ[|{ω | -c ≤ u ω}]
      = (μ {ω | -c ≤ u ω})⁻¹ • μ.restrict {ω | -c ≤ u ω} := rfl
  rw [hcond, integral_smul_measure]
  have hrestr_eq : ∫ ω, u ω ∂μ.restrict {ω | -c ≤ u ω}
      = ∫ ω, (Set.Ici (-c)).indicator id (u ω) ∂μ := by
    have hfun : ({ω | -c ≤ u ω}.indicator u)
        = (fun ω => (Set.Ici (-c)).indicator id (u ω)) := by
      funext ω
      by_cases hx : ω ∈ {ω | -c ≤ u ω}
      · simp only [Set.indicator_of_mem hx]
        have hx2 : u ω ∈ Set.Ici (-c) := hx
        simp [hx2]
      · simp only [Set.indicator_of_notMem hx]
        have hx2 : u ω ∉ Set.Ici (-c) := hx
        simp [hx2]
    rw [← integral_indicator hs, hfun]
  have hmeas : AEStronglyMeasurable
      ((Set.Ici (-c)).indicator id) (gaussianReal 0 1) := by
    measurability
  have htrans : ∫ ω, (Set.Ici (-c)).indicator id (u ω) ∂μ
      = ∫ x, (Set.Ici (-c)).indicator id x ∂gaussianReal 0 1 :=
    hu.integral_comp hmeas
  have hIci_int : ∫ x, (Set.Ici (-c)).indicator id x
      ∂gaussianReal 0 1
      = ∫ x in Set.Ici (-c), x ∂gaussianReal 0 1 := by
    rw [integral_indicator hIci]
    simp
  have hIoi_eq : ∫ x in Set.Ici (-c), x ∂gaussianReal 0 1
      = ∫ x in Set.Ioi (-c), x ∂gaussianReal 0 1 := by
    have hvol0 : volume ({-c} : Set ℝ) = 0 := by simp
    have habs := gaussianReal_absolutelyContinuous
      (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) one_ne_zero
    have hnull : gaussianReal 0 1 {-c} = 0 := habs hvol0
    have hIoiM : MeasurableSet (Set.Ioi (-c)) := by simp
    exact integral_Ici_eq_integral_Ioi' (habs hvol0)
  have hdens : ∫ x in Set.Ioi (-c), x ∂gaussianReal 0 1
      = ∫ x in Set.Ioi (-c), x * gaussianPDFReal 0 1 x ∂volume := by
    have hIoi : MeasurableSet (Set.Ioi (-c)) := by simp
    rw [← integral_indicator hIoi]
    have hv : (1 : ℝ≥0) ≠ 0 := one_ne_zero
    have heq : ∫ x, (Set.Ioi (-c)).indicator
        (fun x => x) x ∂gaussianReal 0 1
        = ∫ x, gaussianPDFReal 0 1 x •
          (Set.Ioi (-c)).indicator (fun x => x) x ∂volume :=
      integral_gaussianReal_eq_integral_smul hv
    rw [heq]
    have hfun : (fun x : ℝ => gaussianPDFReal 0 1 x •
        (Set.Ioi (-c)).indicator (fun x => x) x)
        = (Set.Ioi (-c)).indicator
          (fun x => x * gaussianPDFReal 0 1 x) := by
      funext x
      by_cases hx : x ∈ Set.Ioi (-c)
      · simp [hx, smul_eq_mul, mul_comm]
      · simp [hx]
    rw [hfun, integral_indicator hIoi]
  have htrunc : ∫ ω, u ω ∂μ.restrict {ω | -c ≤ u ω}
      = gaussianPDFReal 0 1 c := by
    rw [hrestr_eq, htrans, hIci_int, hIoi_eq, hdens]
    exact integral_Ioi_mul_pdf c
  have hreal : μ.real {ω | -c ≤ u ω}
      = cdf (gaussianReal 0 1) c :=
    measureReal_selection_eq_cdf hu
  have hsmul : ((μ {ω | -c ≤ u ω})⁻¹.toReal : ℝ)
      • ∫ ω, u ω ∂μ.restrict {ω | -c ≤ u ω}
      = (μ.real {ω | -c ≤ u ω})⁻¹
        * gaussianPDFReal 0 1 c := by
    rw [htrunc, ENNReal.toReal_inv, Measure.real_def, smul_eq_mul]
  rw [hsmul, hreal]
  unfold inverseMillsRatio
  rw [div_eq_inv_mul]

/-- The covariance of outcome and selection errors is `σ₁₂`. -/
theorem covariance_outcomeError_selectionError {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {u η : Ω → ℝ} {σ₁₁ σ₁₂ : ℝ}
    (hu : HasLaw u (gaussianReal 0 1) μ)
    (hη : HasLaw η (gaussianReal 0 1) μ)
    (hind : IndepFun u η μ) :
    cov[fun ω => σ₁₂ * u ω
      + Real.sqrt (σ₁₁ - σ₁₂ ^ 2) * η ω, u; μ] = σ₁₂ := by
  have hu_mem : MemLp u 2 μ := memLp_of_hasLaw hu
  have hη_mem : MemLp η 2 μ := memLp_of_hasLaw hη
  have hU_eq : (fun ω => σ₁₂ * u ω
      + Real.sqrt (σ₁₁ - σ₁₂ ^ 2) * η ω)
      = (σ₁₂ • u + Real.sqrt (σ₁₁ - σ₁₂ ^ 2) • η) := rfl
  rw [hU_eq]
  have h1_mem : MemLp (σ₁₂ • u) 2 μ := by
    exact MemLp.const_smul hu_mem σ₁₂
  have h2_mem : MemLp (Real.sqrt (σ₁₁ - σ₁₂ ^ 2) • η) 2 μ := by
    exact MemLp.const_smul hη_mem √(σ₁₁ - σ₁₂ ^ 2)
  have hadd : cov[σ₁₂ • u + Real.sqrt (σ₁₁ - σ₁₂ ^ 2) • η, u; μ]
      = cov[σ₁₂ • u, u; μ]
        + cov[Real.sqrt (σ₁₁ - σ₁₂ ^ 2) • η, u; μ] := by
    exact covariance_add_left h1_mem h2_mem hu_mem
  rw [hadd]
  have hcov1 : cov[σ₁₂ • u, u; μ] = σ₁₂ * cov[u, u; μ] := by
    exact covariance_smul_left σ₁₂
  have hcov2 : cov[Real.sqrt (σ₁₁ - σ₁₂ ^ 2) • η, u; μ]
      = Real.sqrt (σ₁₁ - σ₁₂ ^ 2) * cov[η, u; μ] := by
    exact covariance_smul_left √(σ₁₁ - σ₁₂ ^ 2)
  rw [hcov1, hcov2]
  have hself : cov[u, u; μ] = Var[u; μ] :=
    covariance_self hu.aemeasurable
  have hvar1 : Var[u; μ] = 1 := variance_of_hasLaw hu
  have hsymm : IndepFun η u μ := by
    exact (IndepFun_iff_Indep η u μ).mpr (id (IndepFun.symm hind))
  have hzero : cov[η, u; μ] = 0 := by
    exact IndepFun.covariance_eq_zero hsymm hη_mem hu_mem
  rw [hself, hvar1, hzero, mul_one, mul_zero, add_zero]

/-- The outcome-error variance is `σ₁₁` when the covariance
matrix is valid. -/
theorem variance_outcomeError {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {u η : Ω → ℝ}
    {σ₁₁ σ₁₂ : ℝ} (hu : HasLaw u (gaussianReal 0 1) μ)
    (hη : HasLaw η (gaussianReal 0 1) μ)
    (hind : IndepFun u η μ) (hvalid : σ₁₂ ^ 2 ≤ σ₁₁) :
    Var[fun ω => σ₁₂ * u ω
      + Real.sqrt (σ₁₁ - σ₁₂ ^ 2) * η ω; μ] = σ₁₁ := by
  have hu_mem : MemLp u 2 μ := memLp_of_hasLaw hu
  have hη_mem : MemLp η 2 μ := memLp_of_hasLaw hη
  have hU_eq : (fun ω => σ₁₂ * u ω
      + Real.sqrt (σ₁₁ - σ₁₂ ^ 2) * η ω)
      = (σ₁₂ • u + Real.sqrt (σ₁₁ - σ₁₂ ^ 2) • η) := rfl
  rw [hU_eq]
  have hφ : Measurable (fun x : ℝ => σ₁₂ * x) := by measurability
  have hψ : Measurable
      (fun x : ℝ => Real.sqrt (σ₁₁ - σ₁₂ ^ 2) * x) := by
    measurability
  have hindep : IndepFun (σ₁₂ • u)
      (Real.sqrt (σ₁₁ - σ₁₂ ^ 2) • η) μ :=
    hind.comp hφ hψ
  have h1_mem : MemLp (σ₁₂ • u) 2 μ := by
    exact MemLp.const_smul hu_mem σ₁₂
  have h2_mem : MemLp (Real.sqrt (σ₁₁ - σ₁₂ ^ 2) • η) 2 μ := by
    exact MemLp.const_smul hη_mem √(σ₁₁ - σ₁₂ ^ 2)
  have hadd : Var[σ₁₂ • u + Real.sqrt (σ₁₁ - σ₁₂ ^ 2) • η; μ]
      = Var[σ₁₂ • u; μ]
        + Var[Real.sqrt (σ₁₁ - σ₁₂ ^ 2) • η; μ] := by
    exact IndepFun.variance_add h1_mem h2_mem hindep
  rw [hadd]
  have hv1 : Var[σ₁₂ • u; μ] = σ₁₂ ^ 2 * Var[u; μ] := by
    exact variance_smul σ₁₂ u μ
  have hv2 : Var[Real.sqrt (σ₁₁ - σ₁₂ ^ 2) • η; μ]
      = (Real.sqrt (σ₁₁ - σ₁₂ ^ 2)) ^ 2 * Var[η; μ] := by
    exact variance_smul (√(σ₁₁ - σ₁₂ ^ 2)) η μ
  rw [hv1, hv2]
  have hvu : Var[u; μ] = 1 := variance_of_hasLaw hu
  have hvη : Var[η; μ] = 1 := variance_of_hasLaw hη
  rw [hvu, hvη, mul_one, mul_one]
  have hnn : 0 ≤ σ₁₁ - σ₁₂ ^ 2 := sub_nonneg.mpr hvalid
  have hsq : (Real.sqrt (σ₁₁ - σ₁₂ ^ 2)) ^ 2
      = σ₁₁ - σ₁₂ ^ 2 :=
    Real.sq_sqrt hnn
  rw [hsq]
  ring

/-- Heckman's equation (2) with the first display: the selected-sample
mean equals `m + σ₁₂ * λ(c)`. See `covariance_outcomeError` and
`variance_outcomeError` for the covariance interpretation of `σ₁₂`
and `σ₁₁`; no validity hypothesis is needed for this identity. -/
theorem integral_cond_selected_outcome_eq {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {u η : Ω → ℝ} {c m σ₁₁ σ₁₂ : ℝ}
    (hu : HasLaw u (gaussianReal 0 1) μ)
    (hη : HasLaw η (gaussianReal 0 1) μ)
    (hind : IndepFun u η μ) (hu_meas : Measurable u) :
    ∫ ω, m + (σ₁₂ * u ω
      + Real.sqrt (σ₁₁ - σ₁₂ ^ 2) * η ω)
      ∂μ[|{ω | -c ≤ u ω}]
      = m + σ₁₂ * inverseMillsRatio c := by
  have hIci : MeasurableSet (Set.Ici (-c)) := by simp
  have hs : MeasurableSet {ω | -c ≤ u ω} := hu_meas hIci
  have hpos : 0 < μ.real {ω | -c ≤ u ω} := by
    rw [measureReal_selection_eq_cdf hu]
    exact cdf_gaussian_pos c
  have hreal_ne : μ.real {ω | -c ≤ u ω} ≠ 0 := ne_of_gt hpos
  have hcond : μ[|{ω | -c ≤ u ω}]
      = (μ {ω | -c ≤ u ω})⁻¹ • μ.restrict {ω | -c ≤ u ω} := rfl
  have hu_int : Integrable u μ := by
    have h2 : MemLp u 2 μ := memLp_of_hasLaw hu
    have h1 : MemLp u 1 μ := by
      exact h2.mono_exponent one_le_two
    exact memLp_one_iff_integrable.mp h1
  have hη_int : Integrable η μ := by
    have h2 : MemLp η 2 μ := memLp_of_hasLaw hη
    have h1 : MemLp η 1 μ := by
      exact h2.mono_exponent one_le_two
    exact memLp_one_iff_integrable.mp h1
  have hu_restr : Integrable u (μ.restrict {ω | -c ≤ u ω}) := by
    exact Integrable.restrict hu_int
  have hη_restr : Integrable η (μ.restrict {ω | -c ≤ u ω}) := by
    exact Integrable.restrict hη_int
  have hconst_restr : Integrable (fun _ : Ω => m)
      (μ.restrict {ω | -c ≤ u ω}) := by
    exact integrable_const m
  have hU_restr : Integrable (fun ω => σ₁₂ * u ω
      + Real.sqrt (σ₁₁ - σ₁₂ ^ 2) * η ω)
      (μ.restrict {ω | -c ≤ u ω}) :=
    (hu_restr.const_mul _).add (hη_restr.const_mul _)
  have hsum_restr : Integrable (fun ω => m + (σ₁₂ * u ω
      + Real.sqrt (σ₁₁ - σ₁₂ ^ 2) * η ω))
      (μ.restrict {ω | -c ≤ u ω}) :=
    hconst_restr.add hU_restr
  rw [hcond, integral_smul_measure]
  have hsplit : ∫ ω, m + (σ₁₂ * u ω
      + Real.sqrt (σ₁₁ - σ₁₂ ^ 2) * η ω)
      ∂μ.restrict {ω | -c ≤ u ω}
      = (μ.restrict {ω | -c ≤ u ω}).real Set.univ * m
        + σ₁₂ * ∫ ω, u ω ∂μ.restrict {ω | -c ≤ u ω}
        + Real.sqrt (σ₁₁ - σ₁₂ ^ 2)
          * ∫ ω, η ω ∂μ.restrict {ω | -c ≤ u ω} := by
    have h_add1 : ∫ ω, m + (σ₁₂ * u ω
        + Real.sqrt (σ₁₁ - σ₁₂ ^ 2) * η ω)
        ∂μ.restrict {ω | -c ≤ u ω}
        = ∫ ω, m ∂μ.restrict {ω | -c ≤ u ω}
          + ∫ ω, (σ₁₂ * u ω
            + Real.sqrt (σ₁₁ - σ₁₂ ^ 2) * η ω)
            ∂μ.restrict {ω | -c ≤ u ω} :=
      integral_add hconst_restr hU_restr
    have h_add2 : ∫ ω, (σ₁₂ * u ω
        + Real.sqrt (σ₁₁ - σ₁₂ ^ 2) * η ω)
        ∂μ.restrict {ω | -c ≤ u ω}
        = ∫ ω, σ₁₂ * u ω ∂μ.restrict {ω | -c ≤ u ω}
          + ∫ ω, Real.sqrt (σ₁₁ - σ₁₂ ^ 2) * η ω
            ∂μ.restrict {ω | -c ≤ u ω} :=
      integral_add (hu_restr.const_mul _)
        (hη_restr.const_mul _)
    have h_const : ∫ ω, m ∂μ.restrict {ω | -c ≤ u ω}
        = (μ.restrict {ω | -c ≤ u ω}).real Set.univ * m := by
      rw [integral_const, Measure.real_def, smul_eq_mul]
    have h_mul1 : ∫ ω, σ₁₂ * u ω ∂μ.restrict {ω | -c ≤ u ω}
        = σ₁₂ * ∫ ω, u ω ∂μ.restrict {ω | -c ≤ u ω} := by
      simp only [← smul_eq_mul, MeasureTheory.integral_smul]
    have h_mul2 : ∫ ω, Real.sqrt (σ₁₁ - σ₁₂ ^ 2) * η ω
        ∂μ.restrict {ω | -c ≤ u ω}
        = Real.sqrt (σ₁₁ - σ₁₂ ^ 2)
          * ∫ ω, η ω ∂μ.restrict {ω | -c ≤ u ω} := by
      simp only [← smul_eq_mul, MeasureTheory.integral_smul]
    rw [h_add1, h_add2, h_const, h_mul1, h_mul2]
    ring
  have hreal_univ : (μ.restrict {ω | -c ≤ u ω}).real Set.univ
      = μ.real {ω | -c ≤ u ω} := by
    rw [Measure.real_def, Measure.real_def, MeasureTheory.Measure.restrict_apply_univ]
  have hint_u : ∫ ω, u ω ∂μ.restrict {ω | -c ≤ u ω}
      = gaussianPDFReal 0 1 c := by
    have hmain := integral_cond_selectionError_eq hu hu_meas (c := c)
    have hcond_u : ∫ ω, u ω ∂μ[|{ω | -c ≤ u ω}]
        = ((μ {ω | -c ≤ u ω})⁻¹.toReal : ℝ)
          • ∫ ω, u ω ∂μ.restrict {ω | -c ≤ u ω} := by
      rw [hcond, integral_smul_measure]
    rw [hmain] at hcond_u
    have hreal := measureReal_selection_eq_cdf (hu := hu) (c := c)
    have hsmul2 : ((μ {ω | -c ≤ u ω})⁻¹.toReal : ℝ)
        • ∫ ω, u ω ∂μ.restrict {ω | -c ≤ u ω}
        = (μ.real {ω | -c ≤ u ω})⁻¹
          * ∫ ω, u ω ∂μ.restrict {ω | -c ≤ u ω} := by
      rw [Measure.real_def, ENNReal.toReal_inv, smul_eq_mul]
    rw [hsmul2, hreal] at hcond_u
    have hΦne : cdf (gaussianReal 0 1) c ≠ 0 :=
      ne_of_gt (cdf_gaussian_pos c)
    unfold inverseMillsRatio at hcond_u
    have hmul : (cdf (gaussianReal 0 1) c)⁻¹
        * ∫ ω, u ω ∂μ.restrict {ω | -c ≤ u ω}
        = (cdf (gaussianReal 0 1) c)⁻¹ * gaussianPDFReal 0 1 c := by
      rw [div_eq_inv_mul] at hcond_u
      exact hcond_u.symm
    exact mul_left_cancel₀ (inv_ne_zero hΦne) hmul
  have hint_η : ∫ ω, η ω ∂μ.restrict {ω | -c ≤ u ω} = 0 := by
    have hg_meas : Measurable
        ((Set.Ici (-c)).indicator (fun _ : ℝ => (1 : ℝ))) := by
      measurability
    have hid_meas : AEStronglyMeasurable id
        (Measure.map η μ) := by measurability
    have hg_ae : AEStronglyMeasurable
        ((Set.Ici (-c)).indicator (fun _ : ℝ => (1 : ℝ)))
        (Measure.map u μ) := by measurability
    have hid_int : Integrable id (Measure.map η μ) := by
      have hmeq : Measure.map η μ = gaussianReal 0 1 := hη.2
      rw [hmeq]
      have hmem : MemLp id (1 : ℝ≥0∞) (gaussianReal 0 1) :=
        memLp_id_gaussianReal 1
      exact memLp_one_iff_integrable.mp hmem
    have hg_int : Integrable
        ((Set.Ici (-c)).indicator (fun _ : ℝ => (1 : ℝ)))
        (Measure.map u μ) :=
      (integrable_const (1 : ℝ)).indicator hIci
    have hXu : AEMeasurable u μ := hu.aemeasurable
    have hXη : AEMeasurable η μ := hη.aemeasurable
    have hfac0 : ∫ ω, (Set.Ici (-c)).indicator
        (fun _ : ℝ => (1 : ℝ)) (u ω) * id (η ω) ∂μ
        = (∫ ω, (Set.Ici (-c)).indicator
          (fun _ : ℝ => (1 : ℝ)) (u ω) ∂μ)
          * ∫ ω, id (η ω) ∂μ :=
      IndepFun.integral_fun_comp_mul_comp hind hXu hXη hg_ae hid_meas
    have hchg1 : ∫ ω, (Set.Ici (-c)).indicator
        (fun _ : ℝ => (1 : ℝ)) (u ω) ∂μ
        = ∫ x, (Set.Ici (-c)).indicator
          (fun _ : ℝ => (1 : ℝ)) x ∂Measure.map u μ :=
      (MeasureTheory.integral_map hXu hg_ae).symm
    have hchg2 : ∫ ω, id (η ω) ∂μ
        = ∫ y, id y ∂Measure.map η μ :=
      (MeasureTheory.integral_map hXη hid_meas).symm
    have hfac : ∫ ω, (Set.Ici (-c)).indicator
        (fun _ : ℝ => (1 : ℝ)) (u ω) * id (η ω) ∂μ
        = (∫ x, (Set.Ici (-c)).indicator
          (fun _ : ℝ => (1 : ℝ)) x ∂Measure.map u μ)
          * ∫ y, id y ∂Measure.map η μ := by
      rw [hfac0, hchg1, hchg2]
    have hLHS : ∫ ω, (Set.Ici (-c)).indicator
        (fun _ : ℝ => (1 : ℝ)) (u ω) * id (η ω) ∂μ
        = ∫ ω, η ω ∂μ.restrict {ω | -c ≤ u ω} := by
      have hfun : (fun ω => (Set.Ici (-c)).indicator
          (fun _ : ℝ => (1 : ℝ)) (u ω) * id (η ω))
          = {ω | -c ≤ u ω}.indicator η := by
        funext ω
        by_cases hx : ω ∈ {ω | -c ≤ u ω}
        · simp only [Set.indicator_of_mem hx, id]
          have hx2 : u ω ∈ Set.Ici (-c) := hx
          simp [hx2, mul_comm]
        · simp only [Set.indicator_of_notMem hx, id]
          have hx2 : u ω ∉ Set.Ici (-c) := hx
          simp [hx2]
      rw [hfun, integral_indicator hs]
    have hRHS : (∫ x, (Set.Ici (-c)).indicator
        (fun _ : ℝ => (1 : ℝ)) x ∂Measure.map u μ)
        * ∫ y, id y ∂Measure.map η μ = 0 := by
      have hmeq2 : Measure.map η μ = gaussianReal 0 1 := hη.2
      have hid0 : ∫ y, id y ∂Measure.map η μ = 0 := by
        rw [hmeq2]
        have h4 := integral_id_gaussianReal
          (μ := (0 : ℝ)) (v := (1 : ℝ≥0))
        simp
      rw [hid0, mul_zero]
    rw [hLHS] at hfac
    rw [hRHS] at hfac
    exact hfac
  rw [hsplit, hreal_univ, hint_u, hint_η, mul_zero, add_zero]
  have hreal := measureReal_selection_eq_cdf (hu := hu) (c := c)
  have hfinal : ((μ {ω | -c ≤ u ω})⁻¹.toReal : ℝ)
      • (μ.real {ω | -c ≤ u ω} * m
        + σ₁₂ * gaussianPDFReal 0 1 c)
      = m + σ₁₂ * inverseMillsRatio c := by
    have hΦ : (μ {ω | -c ≤ u ω}).toReal
        = cdf (gaussianReal 0 1) c := by
      rw [← Measure.real_def, hreal]
    have hΦne : (μ {ω | -c ≤ u ω}).toReal ≠ 0 := by
      rw [hΦ]
      exact ne_of_gt (cdf_gaussian_pos c)
    have hinv : ((μ {ω | -c ≤ u ω})⁻¹.toReal : ℝ)
        = ((μ {ω | -c ≤ u ω}).toReal)⁻¹ := ENNReal.toReal_inv _
    rw [hinv, smul_eq_mul]
    unfold inverseMillsRatio
    rw [div_eq_inv_mul, ← hΦ]
    field_simp
    rw [MeasureTheory.measureReal_def]
    try ring
  exact hfinal

end MathlibExt.Probability.Causality.MissingData

end
