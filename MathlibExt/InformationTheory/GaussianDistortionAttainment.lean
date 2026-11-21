/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.ConditionalEntropy
public import MathlibExt.InformationTheory.GaussianDistortionFeasibility
public import MathlibExt.InformationTheory.ReferenceOutputKL
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Kernel.Composition.WithDensity

/-!
# Gaussian rate-distortion: attainment by the backward Gaussian test channel

For a Gaussian source of variance `σ2` and a distortion level `0 < D < σ2`, take independent
`X̂ ~ N(0, σ2 - D)` and `Z ~ N(0, D)` and put `X = X̂ + Z`. Then `X ~ N(0, σ2)`, the expected
square error `E[(X - X̂)²]` equals `D`, and the mutual information of `(X, X̂)` is
`log (σ2 / D) / (2 * log 2)` bits. Since this joint law is distortion feasible, the Gaussian
rate-distortion function satisfies `R(D) ≤ log (σ2 / D) / (2 * log 2)`. Together with
`GaussianDistortionConverse.rateDistortion_ge_ofReal_log_div`, which has the same binders and the
same bound term, this pins `R(D)` by `le_antisymm`.

The mutual information is computed directly: after swapping coordinates, the law of `(X̂, X)` has
density `pdf_{N(x̂, D)}(x) / pdf_{N(0, σ2)}(x)` against `N(0, σ2 - D) ⊗ N(0, σ2)`, and the
log-likelihood ratio is a quadratic whose mean follows from the second moments `E[Z²] = D` and
`E[X²] = σ2`.

Conventions:
* variances and distortion levels are `ℝ≥0` (the variance type of Mathlib `gaussianReal`); the
  rate-distortion function takes the level as a real number `(D : ℝ)`;
* the joint law is ordered `(X, X̂)`: source first, reproduction second, as in
  `distortionFeasible`;
* mutual information is the information-theory library's `measureMutualInformation`, in bits,
  valued in `ℝ≥0∞`.

## Main results

* `backwardChannelLaw_mem_distortionFeasible`: the backward channel is feasible at level `D`.
* `measureMutualInformation_backwardChannelLaw`: its mutual information is
  `log (σ2 / D) / (2 * log 2)` bits.
* `rateDistortion_le_ofReal_log_div`: the Gaussian rate-distortion upper bound.
* `backwardChannel_attains`: all of the above for random variables on any probability space.

Validation:
* `D = σ2 / 2`: the backward channel carries exactly one half bit;
* the endpoint `D = σ2` is the independent constant reconstruction, with no density formula;
* violated premises: at `D = 0` the backward law is the diagonal law and its mutual information is
  `⊤`, not the value `0` that the zero-denominator logarithm gives; for `D > σ2` the truncated
  variance `σ2 - D = 0` gives the wrong source marginal, so the law is infeasible.

## References

* T. M. Cover and J. A. Thomas, *Elements of Information Theory*, 2nd ed., Wiley, 2006,
  Theorem 10.3.2 (rate-distortion function of a Gaussian source under squared-error distortion)
  and its achievability construction by the backward test channel.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MathlibExt.InformationTheory.GaussianDistortionAttainment

open _root_.InformationTheory
open MathlibExt.InformationTheory.GaussianDistortionFeasibility

/-! ### Definitions -/

/-- The joint law of a pair of real random variables `(X, Y)` on a probability space, as a
probability measure on `ℝ × ℝ`. -/
noncomputable def pairLaw {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X Y : Ω → ℝ) : ProbabilityMeasure (ℝ × ℝ) :=
  ⟨P.map (fun ω => (X ω, Y ω)), inferInstance⟩

/-- The backward Gaussian test channel: the law of `(X, X̂)` where `X̂ ~ N(0, σ2 - D)` and
`Z ~ N(0, D)` are independent and `X = X̂ + Z`, realized on the product of the two Gaussian
laws. The variance `σ2 - D` is truncated subtraction in `ℝ≥0`. -/
noncomputable def backwardChannelLaw (σ2 D : ℝ≥0) : ProbabilityMeasure (ℝ × ℝ) :=
  ⟨((gaussianReal 0 (σ2 - D)).prod (gaussianReal 0 D)).map (fun p => (p.1 + p.2, p.1)),
    inferInstance⟩

/-! ### Private helpers -/

private theorem measurable_backwardMap :
    Measurable (fun p : ℝ × ℝ => (p.1 + p.2, p.1)) := by
  fun_prop

private theorem measurable_shearMap :
    Measurable (fun p : ℝ × ℝ => (p.1, p.1 + p.2)) := by
  fun_prop

private theorem measurable_sq_error_ennreal' :
    Measurable (fun z : ℝ × ℝ => ENNReal.ofReal ((z.1 - z.2) ^ 2)) :=
  ((continuous_fst.sub continuous_snd).pow 2).measurable.ennreal_ofReal

private theorem integrable_sq_gaussianReal (v : ℝ≥0) :
    Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 v) :=
  (memLp_id_gaussianReal (μ := 0) (v := v) 2).integrable_sq

private theorem integral_sq_gaussianReal (v : ℝ≥0) :
    ∫ x, x ^ 2 ∂(gaussianReal 0 v) = (v : ℝ) := by
  have hmem : MemLp id 2 (gaussianReal 0 v) := memLp_id_gaussianReal 2
  have h := variance_eq_sub hmem
  have h1 : (∫ x, id x ∂(gaussianReal 0 v)) = 0 := integral_id_gaussianReal
  rw [variance_id_gaussianReal, h1] at h
  simp at h
  linarith

private theorem lintegral_sq_gaussianReal (v : ℝ≥0) :
    ∫⁻ x, ENNReal.ofReal (x ^ 2) ∂(gaussianReal 0 v) = ENNReal.ofReal (v : ℝ) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_sq_gaussianReal v)
    (Filter.Eventually.of_forall fun x => sq_nonneg x), integral_sq_gaussianReal]

/-- The two Gaussian components of the backward channel, as a product measure. -/
private theorem prod_map_snd (σ2 D : ℝ≥0) :
    ((gaussianReal 0 (σ2 - D)).prod (gaussianReal 0 D)).map Prod.snd = gaussianReal 0 D := by
  rw [Measure.map_snd_prod]
  simp

private theorem prod_map_fst (σ2 D : ℝ≥0) :
    ((gaussianReal 0 (σ2 - D)).prod (gaussianReal 0 D)).map Prod.fst =
      gaussianReal 0 (σ2 - D) := by
  rw [Measure.map_fst_prod]
  simp

private theorem prod_map_add (σ2 D : ℝ≥0) :
    ((gaussianReal 0 (σ2 - D)).prod (gaussianReal 0 D)).map (fun p => p.1 + p.2) =
      gaussianReal 0 (σ2 - D + D) := by
  have h : ((gaussianReal 0 (σ2 - D)).prod (gaussianReal 0 D)).map (fun p => p.1 + p.2) =
      (gaussianReal 0 (σ2 - D)) ∗ (gaussianReal 0 D) := rfl
  rw [h, gaussianReal_conv_gaussianReal, add_zero]

private theorem backwardChannelLaw_coe (σ2 D : ℝ≥0) :
    (backwardChannelLaw σ2 D : Measure (ℝ × ℝ)) =
      ((gaussianReal 0 (σ2 - D)).prod (gaussianReal 0 D)).map (fun p => (p.1 + p.2, p.1)) :=
  rfl

private theorem backwardChannelLaw_map_fst' (σ2 D : ℝ≥0) :
    (backwardChannelLaw σ2 D : Measure (ℝ × ℝ)).map Prod.fst = gaussianReal 0 (σ2 - D + D) := by
  rw [backwardChannelLaw_coe, Measure.map_map measurable_fst measurable_backwardMap]
  exact prod_map_add σ2 D

private theorem backwardChannelLaw_map_snd (σ2 D : ℝ≥0) :
    (backwardChannelLaw σ2 D : Measure (ℝ × ℝ)).map Prod.snd = gaussianReal 0 (σ2 - D) := by
  rw [backwardChannelLaw_coe, Measure.map_map measurable_snd measurable_backwardMap]
  exact prod_map_fst σ2 D

private theorem log_gaussianPDFReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    Real.log (gaussianPDFReal m v x) =
      -(Real.log (2 * Real.pi * v)) / 2 - (x - m) ^ 2 / (2 * v) := by
  have hv' : (0 : ℝ) < v := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  have h2 : (0 : ℝ) < 2 * Real.pi * v := by positivity
  rw [gaussianPDFReal_def]
  simp only
  rw [Real.log_mul (inv_ne_zero (Real.sqrt_pos.mpr h2).ne') (Real.exp_pos _).ne', Real.log_exp,
    Real.log_inv, Real.log_sqrt h2.le]
  ring

/-- The density ratio of `N(a, D)` against `N(0, σ2)`. -/
private noncomputable def ratioDensity (σ2 D : ℝ≥0) (a x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (gaussianPDFReal a D x / gaussianPDFReal 0 σ2 x)

private theorem measurable_ratioDensity (σ2 D : ℝ≥0) :
    Measurable (Function.uncurry (ratioDensity σ2 D)) := by
  have h1 : Measurable (fun p : ℝ × ℝ => gaussianPDFReal p.1 D p.2) :=
    measurable_uncurry_gaussianPDFReal.comp
      (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
  have h2 : Measurable (fun p : ℝ × ℝ => gaussianPDFReal 0 σ2 p.2) :=
    (measurable_gaussianPDFReal 0 σ2).comp measurable_snd
  exact (h1.div h2).ennreal_ofReal

private theorem withDensity_ratioDensity (σ2 D : ℝ≥0) (hσ : σ2 ≠ 0) (hD : D ≠ 0) (a : ℝ) :
    (gaussianReal 0 σ2).withDensity (ratioDensity σ2 D a) = gaussianReal a D := by
  have hmeas : Measurable (ratioDensity σ2 D a) := by
    unfold ratioDensity
    exact ((measurable_gaussianPDFReal a D).div (measurable_gaussianPDFReal 0 σ2)).ennreal_ofReal
  have hmul := withDensity_mul (volume : Measure ℝ) (measurable_gaussianPDF 0 σ2) hmeas
  rw [gaussianReal_of_var_ne_zero 0 hσ, ← hmul, gaussianReal_of_var_ne_zero a hD]
  congr 1
  funext x
  simp only [Pi.mul_apply, gaussianPDF, ratioDensity]
  rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _),
    mul_div_cancel₀ _ (gaussianPDFReal_pos _ _ _ hσ).ne']

/-- The swapped backward law `(X̂, X)` has density `ratioDensity` against `N(0, σ2 - D) ⊗ N(0, σ2)`.
-/
private theorem shear_eq_withDensity (σ2 D : ℝ≥0) (hσ : σ2 ≠ 0) (hD : D ≠ 0) :
    ((gaussianReal 0 (σ2 - D)).prod (gaussianReal 0 D)).map (fun p => (p.1, p.1 + p.2)) =
      ((gaussianReal 0 (σ2 - D)).prod (gaussianReal 0 σ2)).withDensity
        (fun p => ratioDensity σ2 D p.1 p.2) := by
  have hR : ((gaussianReal 0 (σ2 - D)).prod (gaussianReal 0 σ2)).withDensity
      (fun p => ratioDensity σ2 D p.1 p.2) =
      (gaussianReal 0 (σ2 - D)) ⊗ₘ
        ((Kernel.const ℝ (gaussianReal 0 σ2)).withDensity (ratioDensity σ2 D)) := by
    have : IsSFiniteKernel
        ((Kernel.const ℝ (gaussianReal 0 σ2)).withDensity (ratioDensity σ2 D)) :=
      Kernel.IsSFiniteKernel.withDensity _ (fun _ _ => ENNReal.ofReal_ne_top)
    rw [Measure.compProd_withDensity (measurable_ratioDensity σ2 D), Measure.compProd_const]
  have : IsSFiniteKernel ((Kernel.const ℝ (gaussianReal 0 σ2)).withDensity (ratioDensity σ2 D)) :=
    Kernel.IsSFiniteKernel.withDensity _ (fun _ _ => ENNReal.ofReal_ne_top)
  rw [hR]
  ext s hs
  rw [Measure.map_apply measurable_shearMap hs, Measure.prod_apply (measurable_shearMap hs),
    Measure.compProd_apply hs]
  refine lintegral_congr fun a => ?_
  rw [Kernel.withDensity_apply _ (measurable_ratioDensity σ2 D), Kernel.const_apply,
    withDensity_ratioDensity σ2 D hσ hD a]
  have hmap : (gaussianReal 0 D).map (fun z => a + z) = gaussianReal a D := by
    rw [gaussianReal_map_const_add, zero_add]
  rw [← hmap, Measure.map_apply (measurable_const_add a) (measurable_prodMk_left hs)]
  rfl

/-- The log-likelihood ratio along the shear map. -/
private theorem log_ratio_shear (σ2 D : ℝ≥0) (hσ : σ2 ≠ 0) (hD : D ≠ 0) (p : ℝ × ℝ) :
    Real.log (gaussianPDFReal p.1 D (p.1 + p.2) / gaussianPDFReal 0 σ2 (p.1 + p.2)) =
      (Real.log (2 * Real.pi * σ2) / 2 - Real.log (2 * Real.pi * D) / 2) -
        p.2 ^ 2 / (2 * D) + (p.1 + p.2) ^ 2 / (2 * σ2) := by
  rw [Real.log_div (gaussianPDFReal_pos _ _ _ hD).ne' (gaussianPDFReal_pos _ _ _ hσ).ne',
    log_gaussianPDFReal _ hD, log_gaussianPDFReal _ hσ]
  ring

/-- The core computation: the swapped backward law against the product of its marginals. -/
private theorem klDiv_shear (σ2 D : ℝ≥0) (hσ : σ2 ≠ 0) (hD : D ≠ 0) (hDσ2 : D ≤ σ2) :
    klDiv (((gaussianReal 0 (σ2 - D)).prod (gaussianReal 0 D)).map (fun p => (p.1, p.1 + p.2)))
      ((gaussianReal 0 (σ2 - D)).prod (gaussianReal 0 σ2)) =
      ENNReal.ofReal (Real.log ((σ2 : ℝ) / (D : ℝ)) / 2) := by
  set π0 := (gaussianReal 0 (σ2 - D)).prod (gaussianReal 0 D) with hπ0
  set π := (gaussianReal 0 (σ2 - D)).prod (gaussianReal 0 σ2) with hπ
  set ρ := π0.map (fun p => (p.1, p.1 + p.2)) with hρ
  set F : ℝ × ℝ → ℝ≥0∞ := fun p => ratioDensity σ2 D p.1 p.2 with hF
  have hFm : Measurable F := measurable_ratioDensity σ2 D
  have hρF : ρ = π.withDensity F := shear_eq_withDensity σ2 D hσ hD
  have hac : ρ ≪ π := by rw [hρF]; exact withDensity_absolutelyContinuous π F
  set L : ℝ × ℝ → ℝ := fun p => Real.log (gaussianPDFReal p.1 D p.2 / gaussianPDFReal 0 σ2 p.2)
    with hL
  have hLm : Measurable L := by
    have h1 : Measurable (fun p : ℝ × ℝ => gaussianPDFReal p.1 D p.2) :=
      measurable_uncurry_gaussianPDFReal.comp
        (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
    have h2 : Measurable (fun p : ℝ × ℝ => gaussianPDFReal 0 σ2 p.2) :=
      (measurable_gaussianPDFReal 0 σ2).comp measurable_snd
    exact Real.measurable_log.comp (h1.div h2)
  have hllr : llr ρ π =ᵐ[ρ] L := by
    have h : llr ρ π =ᵐ[π] L := by
      have hrn : ρ.rnDeriv π =ᵐ[π] F := by rw [hρF]; exact Measure.rnDeriv_withDensity π hFm
      filter_upwards [hrn] with p hp
      rw [llr_def]
      simp only
      rw [hp]
      simp only [hF, hL, ratioDensity]
      rw [ENNReal.toReal_ofReal
        (div_nonneg (gaussianPDFReal_nonneg _ _ _) (gaussianPDFReal_nonneg _ _ _))]
    exact hac.ae_le h
  -- `L` along the shear map is an explicit quadratic
  set c : ℝ := Real.log (2 * Real.pi * σ2) / 2 - Real.log (2 * Real.pi * D) / 2 with hc
  have hLg : (L ∘ fun p : ℝ × ℝ => (p.1, p.1 + p.2)) =
      fun p => c - p.2 ^ 2 / (2 * D) + (p.1 + p.2) ^ 2 / (2 * σ2) := by
    funext p
    exact log_ratio_shear σ2 D hσ hD p
  -- moments under `π0`
  have hint2 : Integrable (fun p : ℝ × ℝ => p.2 ^ 2) π0 := by
    have h : Integrable (fun x : ℝ => x ^ 2) (π0.map Prod.snd) := by
      rw [hπ0, prod_map_snd]; exact integrable_sq_gaussianReal D
    exact (integrable_map_measure (by fun_prop) measurable_snd.aemeasurable).1 h
  have hint3 : Integrable (fun p : ℝ × ℝ => (p.1 + p.2) ^ 2) π0 := by
    have h : Integrable (fun x : ℝ => x ^ 2) (π0.map (fun p => p.1 + p.2)) := by
      rw [hπ0, prod_map_add]; exact integrable_sq_gaussianReal _
    exact (integrable_map_measure (by fun_prop) (by fun_prop)).1 h
  have hval2 : ∫ p, p.2 ^ 2 ∂π0 = (D : ℝ) := by
    have h : ∫ x, x ^ 2 ∂(π0.map Prod.snd) = ∫ p, p.2 ^ 2 ∂π0 :=
      integral_map measurable_snd.aemeasurable (by fun_prop)
    rw [← h, hπ0, prod_map_snd, integral_sq_gaussianReal]
  have hval3 : ∫ p, (p.1 + p.2) ^ 2 ∂π0 = (σ2 : ℝ) := by
    have h : ∫ x, x ^ 2 ∂(π0.map (fun p => p.1 + p.2)) = ∫ p, (p.1 + p.2) ^ 2 ∂π0 :=
      integral_map (by fun_prop) (by fun_prop)
    rw [← h, hπ0, prod_map_add, integral_sq_gaussianReal, tsub_add_cancel_of_le hDσ2]
  have hintLg : Integrable (L ∘ fun p : ℝ × ℝ => (p.1, p.1 + p.2)) π0 := by
    rw [hLg]
    exact ((integrable_const c).sub (hint2.div_const _)).add (hint3.div_const _)
  have hintL : Integrable L ρ :=
    (integrable_map_measure hLm.aestronglyMeasurable measurable_shearMap.aemeasurable).2 hintLg
  have hintllr : Integrable (llr ρ π) ρ := hintL.congr hllr.symm
  have hvalL : ∫ p, L p ∂ρ = c := by
    rw [hρ, integral_map measurable_shearMap.aemeasurable hLm.aestronglyMeasurable]
    have h : ∫ p, L (p.1, p.1 + p.2) ∂π0 =
        ∫ p, (c - p.2 ^ 2 / (2 * D) + (p.1 + p.2) ^ 2 / (2 * σ2)) ∂π0 :=
      congrArg (fun f => ∫ p, f p ∂π0) hLg
    have hA : Integrable (fun p : ℝ × ℝ => c - p.2 ^ 2 / (2 * D)) π0 :=
      (integrable_const c).sub (hint2.div_const _)
    have hB : Integrable (fun p : ℝ × ℝ => (p.1 + p.2) ^ 2 / (2 * σ2)) π0 := hint3.div_const _
    have hB2 : Integrable (fun p : ℝ × ℝ => p.2 ^ 2 / (2 * D)) π0 := hint2.div_const _
    rw [h, integral_add hA hB, integral_sub (integrable_const c) hB2, integral_const,
      integral_div, integral_div, hval2, hval3]
    have hD' : (D : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hD
    have hσ' : (σ2 : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hσ
    simp only [probReal_univ, one_smul]
    field_simp
    ring
  have hρprob : IsProbabilityMeasure ρ := by rw [hρ]; infer_instance
  rw [klDiv_of_ac_of_integrable hac hintllr, integral_congr_ae hllr, hvalL]
  simp only [probReal_univ, add_sub_cancel_right]
  congr 1
  have hD' : (0 : ℝ) < D := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hD)
  have hσ' : (0 : ℝ) < σ2 := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hσ)
  rw [hc, Real.log_div hσ'.ne' hD'.ne', Real.log_mul (by positivity) hσ'.ne',
    Real.log_mul (by positivity) hD'.ne']
  ring

/-! ### Source marginal and distortion -/

/-- For `D ≤ σ2`, the source `X = X̂ + Z` of the backward channel is `N(0, σ2)`. -/
theorem backwardChannelLaw_map_fst (σ2 D : ℝ≥0) (hDσ2 : (D : ℝ) ≤ (σ2 : ℝ)) :
    (backwardChannelLaw σ2 D : Measure (ℝ × ℝ)).map Prod.fst = gaussianReal 0 σ2 := by
  rw [backwardChannelLaw_map_fst', tsub_add_cancel_of_le (by exact_mod_cast hDσ2)]

/-- The square-error lower integral of the backward channel is exactly `ofReal D`. -/
theorem lintegral_sq_error_backwardChannelLaw (σ2 D : ℝ≥0) :
    ∫⁻ z, ENNReal.ofReal ((z.1 - z.2) ^ 2) ∂(backwardChannelLaw σ2 D : Measure (ℝ × ℝ)) =
      ENNReal.ofReal (D : ℝ) := by
  rw [backwardChannelLaw_coe, lintegral_map measurable_sq_error_ennreal' measurable_backwardMap]
  simp only [add_sub_cancel_left]
  have h : (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (p.2 ^ 2)
      ∂((gaussianReal 0 (σ2 - D)).prod (gaussianReal 0 D))) =
      ∫⁻ x, ENNReal.ofReal (x ^ 2)
        ∂(((gaussianReal 0 (σ2 - D)).prod (gaussianReal 0 D)).map Prod.snd) :=
    (lintegral_map (measurable_id.pow_const 2).ennreal_ofReal measurable_snd).symm
  rw [h, prod_map_snd, lintegral_sq_gaussianReal]

/-- The expected square error of the backward channel is exactly `D`. -/
theorem integral_sq_error_backwardChannelLaw (σ2 D : ℝ≥0) :
    ∫ z, (z.1 - z.2) ^ 2 ∂(backwardChannelLaw σ2 D : Measure (ℝ × ℝ)) = (D : ℝ) := by
  rw [backwardChannelLaw_coe, integral_map measurable_backwardMap.aemeasurable (by fun_prop)]
  simp only [add_sub_cancel_left]
  have h : (∫ p : ℝ × ℝ, p.2 ^ 2 ∂((gaussianReal 0 (σ2 - D)).prod (gaussianReal 0 D))) =
      ∫ x, x ^ 2 ∂(((gaussianReal 0 (σ2 - D)).prod (gaussianReal 0 D)).map Prod.snd) :=
    (integral_map measurable_snd.aemeasurable (continuous_pow 2).aestronglyMeasurable).symm
  rw [h, prod_map_snd, integral_sq_gaussianReal]

/-- For `D ≤ σ2`, the backward channel is distortion feasible at level `D`. -/
theorem backwardChannelLaw_mem_distortionFeasible (σ2 D : ℝ≥0)
    (hDσ2 : (D : ℝ) ≤ (σ2 : ℝ)) :
    backwardChannelLaw σ2 D ∈ distortionFeasible σ2 (D : ℝ) := by
  exact ⟨D.coe_nonneg, backwardChannelLaw_map_fst σ2 D hDσ2,
    (lintegral_sq_error_backwardChannelLaw σ2 D).le⟩

/-! ### Mutual information and the rate-distortion upper bound -/

/-- For `0 < D < σ2`, the mutual information of `(X, X̂)` under the backward channel is
`log (σ2 / D) / (2 * log 2)` bits. -/
theorem measureMutualInformation_backwardChannelLaw (σ2 D : ℝ≥0)
    (hD : (0 : ℝ) < (D : ℝ)) (hDσ2 : (D : ℝ) < (σ2 : ℝ)) :
    measureMutualInformation (backwardChannelLaw σ2 D) =
      ENNReal.ofReal (Real.log ((σ2 : ℝ) / (D : ℝ)) / (2 * Real.log 2)) := by
  have hD0 : D ≠ 0 := by
    intro h
    rw [h, NNReal.coe_zero] at hD
    exact lt_irrefl 0 hD
  have hσ0 : σ2 ≠ 0 := by
    intro h
    rw [h, NNReal.coe_zero] at hDσ2
    exact absurd hDσ2 (not_lt.mpr D.coe_nonneg)
  have hle : D ≤ σ2 := by exact_mod_cast hDσ2.le
  unfold measureMutualInformation
  rw [backwardChannelLaw_map_fst σ2 D hDσ2.le, backwardChannelLaw_map_snd]
  have hswap := ReferenceOutputKL.klDiv_map_swap (backwardChannelLaw σ2 D : Measure (ℝ × ℝ))
    ((gaussianReal 0 σ2).prod (gaussianReal 0 (σ2 - D)))
  rw [Measure.prod_swap, backwardChannelLaw_coe,
    Measure.map_map measurable_swap measurable_backwardMap] at hswap
  have hcomp : (Prod.swap ∘ fun p : ℝ × ℝ => (p.1 + p.2, p.1)) = fun p => (p.1, p.1 + p.2) := rfl
  rw [hcomp, klDiv_shear σ2 D hσ0 hD0 hle] at hswap
  rw [backwardChannelLaw_coe, ← hswap,
    ← ENNReal.ofReal_div_of_pos (Real.log_pos one_lt_two)]
  congr 1
  ring

/-- **Gaussian rate-distortion upper bound.** For `0 < D < σ2`, the Gaussian rate-distortion
function at `D`, in bits, is at most `log (σ2 / D) / (2 * log 2)`. -/
theorem rateDistortion_le_ofReal_log_div (σ2 D : ℝ≥0)
    (hD : (0 : ℝ) < (D : ℝ)) (hDσ2 : (D : ℝ) < (σ2 : ℝ)) :
    rateDistortion σ2 (D : ℝ) ≤
      ENNReal.ofReal (Real.log ((σ2 : ℝ) / (D : ℝ)) / (2 * Real.log 2)) := by
  have hmem := backwardChannelLaw_mem_distortionFeasible σ2 D hDσ2.le
  calc rateDistortion σ2 (D : ℝ) ≤ measureMutualInformation (backwardChannelLaw σ2 D) :=
        iInf₂_le _ hmem
    _ = _ := measureMutualInformation_backwardChannelLaw σ2 D hD hDσ2

/-- **Attainment by the backward Gaussian test channel.** Let `0 < D < σ2`, let `X̂` and `Z` be
independent real random variables with `X̂ ~ N(0, σ2 - D)` and `Z ~ N(0, D)`, and let
`X = X̂ + Z`. Then the joint law of `(X, X̂)` has source marginal `N(0, σ2)`, square-error
distortion exactly `D` (as a lower integral), is distortion feasible at `D`, and has mutual
information `log (σ2 / D) / (2 * log 2)` bits; hence `R(D)` is at most that value. -/
theorem backwardChannel_attains (σ2 D : ℝ≥0)
    (hD : (0 : ℝ) < (D : ℝ)) (hDσ2 : (D : ℝ) < (σ2 : ℝ))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Xhat Z : Ω → ℝ) (hXhat : HasLaw Xhat (gaussianReal 0 (σ2 - D)) P)
    (hZ : HasLaw Z (gaussianReal 0 D) P) (hindep : IndepFun Xhat Z P)
    (hX : ∀ ω, X ω = Xhat ω + Z ω) :
    (pairLaw P X Xhat : Measure (ℝ × ℝ)).map Prod.fst = gaussianReal 0 σ2 ∧
      ∫⁻ z, ENNReal.ofReal ((z.1 - z.2) ^ 2) ∂(pairLaw P X Xhat : Measure (ℝ × ℝ)) =
        ENNReal.ofReal (D : ℝ) ∧
      pairLaw P X Xhat ∈ distortionFeasible σ2 (D : ℝ) ∧
      measureMutualInformation (pairLaw P X Xhat) =
        ENNReal.ofReal (Real.log ((σ2 : ℝ) / (D : ℝ)) / (2 * Real.log 2)) ∧
      rateDistortion σ2 (D : ℝ) ≤
        ENNReal.ofReal (Real.log ((σ2 : ℝ) / (D : ℝ)) / (2 * Real.log 2)) := by
  have hlaw : pairLaw P X Xhat = backwardChannelLaw σ2 D := by
    apply Subtype.ext
    change P.map (fun ω => (X ω, Xhat ω)) =
      ((gaussianReal 0 (σ2 - D)).prod (gaussianReal 0 D)).map (fun p => (p.1 + p.2, p.1))
    have hXfun : (fun ω => (X ω, Xhat ω)) =
        (fun p : ℝ × ℝ => (p.1 + p.2, p.1)) ∘ (fun ω => (Xhat ω, Z ω)) := by
      funext ω
      simp [hX ω]
    rw [hXfun, ← AEMeasurable.map_map_of_aemeasurable measurable_backwardMap.aemeasurable
      (hXhat.aemeasurable.prodMk hZ.aemeasurable),
      (indepFun_iff_map_prod_eq_prod_map_map hXhat.aemeasurable hZ.aemeasurable).1 hindep,
      hXhat.map_eq, hZ.map_eq]
  rw [hlaw]
  exact ⟨backwardChannelLaw_map_fst σ2 D hDσ2.le, lintegral_sq_error_backwardChannelLaw σ2 D,
    backwardChannelLaw_mem_distortionFeasible σ2 D hDσ2.le,
    measureMutualInformation_backwardChannelLaw σ2 D hD hDσ2,
    rateDistortion_le_ofReal_log_div σ2 D hD hDσ2⟩

/-! ### Validation: `D = σ2 / 2` -/

/-- At `D = σ2 / 2` the backward channel carries exactly one half bit. -/
theorem measureMutualInformation_backwardChannelLaw_half (σ2 : ℝ≥0) (hσ2 : (0 : ℝ) < (σ2 : ℝ)) :
    measureMutualInformation (backwardChannelLaw σ2 (σ2 / 2)) = ENNReal.ofReal (1 / 2) := by
  have hc : ((σ2 / 2 : ℝ≥0) : ℝ) = (σ2 : ℝ) / 2 := by push_cast; ring
  have hD : (0 : ℝ) < ((σ2 / 2 : ℝ≥0) : ℝ) := by rw [hc]; positivity
  have hDσ2 : ((σ2 / 2 : ℝ≥0) : ℝ) < (σ2 : ℝ) := by rw [hc]; linarith
  rw [measureMutualInformation_backwardChannelLaw σ2 (σ2 / 2) hD hDσ2, hc]
  congr 1
  have h2 : (σ2 : ℝ) / ((σ2 : ℝ) / 2) = 2 := by field_simp
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  rw [h2]
  field_simp

/-- Hence `R(σ2 / 2)` is at most one half bit. -/
theorem rateDistortion_half_le (σ2 : ℝ≥0) (hσ2 : (0 : ℝ) < (σ2 : ℝ)) :
    rateDistortion σ2 ((σ2 / 2 : ℝ≥0) : ℝ) ≤ ENNReal.ofReal (1 / 2) := by
  have hc : ((σ2 / 2 : ℝ≥0) : ℝ) = (σ2 : ℝ) / 2 := by push_cast; ring
  have hD : (0 : ℝ) < ((σ2 / 2 : ℝ≥0) : ℝ) := by rw [hc]; positivity
  have hDσ2 : ((σ2 / 2 : ℝ≥0) : ℝ) < (σ2 : ℝ) := by rw [hc]; linarith
  calc rateDistortion σ2 ((σ2 / 2 : ℝ≥0) : ℝ)
      ≤ measureMutualInformation (backwardChannelLaw σ2 (σ2 / 2)) :=
        iInf₂_le _ (backwardChannelLaw_mem_distortionFeasible σ2 (σ2 / 2) hDσ2.le)
    _ = ENNReal.ofReal (1 / 2) := measureMutualInformation_backwardChannelLaw_half σ2 hσ2

/-! ### Validation: the endpoint `D = σ2` is constant reconstruction -/

/-- At `D = σ2` the reproduction variance is `0`: the backward channel is the independent
constant reconstruction `N(0, σ2) ⊗ δ₀`. -/
theorem backwardChannelLaw_self (σ2 : ℝ≥0) :
    backwardChannelLaw σ2 σ2 = constantReconstruction σ2 := by
  apply Subtype.ext
  change ((gaussianReal 0 (σ2 - σ2)).prod (gaussianReal 0 σ2)).map (fun p => (p.1 + p.2, p.1)) =
    (gaussianReal 0 σ2).prod (Measure.dirac 0)
  rw [tsub_self, gaussianReal_zero_var, Measure.dirac_prod,
    Measure.map_map measurable_backwardMap measurable_prodMk_left, Measure.prod_dirac]
  congr 1
  funext z
  simp

/-- The upper bound extends to the endpoint `D = σ2`, where `log (σ2 / σ2) = 0`; the proof goes
through constant reconstruction, not a zero-variance density formula. -/
theorem rateDistortion_self_le_ofReal_log_div (σ2 : ℝ≥0) :
    rateDistortion σ2 (σ2 : ℝ) ≤
      ENNReal.ofReal (Real.log ((σ2 : ℝ) / (σ2 : ℝ)) / (2 * Real.log 2)) := by
  have hmem := backwardChannelLaw_mem_distortionFeasible σ2 σ2 le_rfl
  have hMI : measureMutualInformation (backwardChannelLaw σ2 σ2) = 0 := by
    rw [backwardChannelLaw_self]
    exact measureMutualInformation_constantReconstruction σ2
  calc rateDistortion σ2 (σ2 : ℝ) ≤ measureMutualInformation (backwardChannelLaw σ2 σ2) :=
        iInf₂_le _ hmem
    _ = 0 := hMI
    _ ≤ _ := bot_le

/-! ### Validation: violated premises -/

/-- Violated premise `0 < D`: at `D = 0` the backward channel is the diagonal law `X̂ = X`, whose
mutual information is `⊤`, while the zero-denominator formula `log (σ2 / 0) / (2 * log 2)`
evaluates to `0` under Lean's conventions `x / 0 = 0` and `log 0 = 0`; it is not a valid rate. -/
theorem measureMutualInformation_backwardChannelLaw_zero (σ2 : ℝ≥0)
    (hσ2 : (0 : ℝ) < (σ2 : ℝ)) :
    measureMutualInformation (backwardChannelLaw σ2 0) = ⊤ ∧
      ENNReal.ofReal (Real.log ((σ2 : ℝ) / ((0 : ℝ≥0) : ℝ)) / (2 * Real.log 2)) = 0 := by
  have hσ0 : σ2 ≠ 0 := by
    intro h
    rw [h, NNReal.coe_zero] at hσ2
    exact lt_irrefl 0 hσ2
  have htop : measureMutualInformation (backwardChannelLaw σ2 0) = ⊤ := by
    unfold measureMutualInformation
    rw [backwardChannelLaw_map_fst σ2 0 (by simp), backwardChannelLaw_map_snd, tsub_zero]
    rw [klDiv_of_not_ac, ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top]
    intro hac
    have hΔ : MeasurableSet {p : ℝ × ℝ | p.1 = p.2} :=
      measurableSet_eq_fun measurable_fst measurable_snd
    have h0 : ((gaussianReal 0 σ2).prod (gaussianReal 0 σ2)) {p : ℝ × ℝ | p.1 = p.2} = 0 := by
      have := nullSingletonClass_gaussianReal (μ := 0) hσ0
      rw [Measure.prod_apply hΔ]
      have hsl : ∀ a : ℝ, Prod.mk a ⁻¹' {p : ℝ × ℝ | p.1 = p.2} = {a} := by
        intro a
        ext x
        simp [eq_comm]
      simp only [hsl, measure_singleton, lintegral_zero]
    have h1 := hac h0
    rw [backwardChannelLaw_coe, Measure.map_apply measurable_backwardMap hΔ] at h1
    have hpre : (fun p : ℝ × ℝ => (p.1 + p.2, p.1)) ⁻¹' {p : ℝ × ℝ | p.1 = p.2} =
        Prod.snd ⁻¹' {0} := by
      ext p
      simp
    rw [hpre, ← Measure.map_apply measurable_snd (measurableSet_singleton 0), prod_map_snd,
      gaussianReal_zero_var] at h1
    simp at h1
  refine ⟨htop, ?_⟩
  simp

/-- Violated premise `D < σ2`: for `D > σ2` the truncated reproduction variance is `0`, the
source marginal is `N(0, D)` rather than `N(0, σ2)`, and the backward law is infeasible. -/
theorem backwardChannelLaw_not_mem_distortionFeasible (σ2 D : ℝ≥0)
    (hσ2D : (σ2 : ℝ) < (D : ℝ)) :
    backwardChannelLaw σ2 D ∉ distortionFeasible σ2 (D : ℝ) := by
  rintro ⟨_, hmap, _⟩
  rw [backwardChannelLaw_map_fst'] at hmap
  have hle : σ2 ≤ D := by exact_mod_cast hσ2D.le
  rw [tsub_eq_zero_of_le hle, zero_add] at hmap
  have hDσ : D = σ2 := (gaussianReal_ext_iff.1 hmap).2
  rw [hDσ] at hσ2D
  exact lt_irrefl _ hσ2D

end MathlibExt.InformationTheory.GaussianDistortionAttainment
