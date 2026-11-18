/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.ConditionalEntropy
public import MathlibExt.InformationTheory.GaussianDistortionFeasibility
public import MathlibExt.InformationTheory.NormalizedKLTestBound
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Gaussian rate-distortion converse

For a Gaussian source of variance `sigma2` and a distortion level with
`0 < D < sigma2`, every joint law of a source and reproduction pair that
has the Gaussian source marginal and expected square error at most `D`
is tested by the normalized function
`f(x, xhat) = log (pdf_N(0,D) (x - xhat)) - log (pdf_N(0,sigma2) x)`,
where the logarithms and densities are the real Gaussian densities.
The exponential of this test integrates to one against the product of
the two marginals of the joint law, and the mean of the test under the
joint law is at least `log (sigma2 / D) / 2`, the two quadratic terms
contributing `1 / 2 - E[(X - Xhat)^2] / (2 * D)`. Hence the mutual
information of every such law, in bits, is at least
`log (sigma2 / D) / (2 * log 2)`, and so is its infimum, the Gaussian
rate-distortion function at `D`. The case `D = 0` is excluded from
this density test; a strictly smaller expected distortion than `D`
gives a strictly larger test mean.

Units: the test bound is in nats, and mutual information is reported in
bits, as the Kullback-Leibler divergence in nats divided by `log 2`; so
the nats bound `log (sigma2 / D) / 2` becomes the bits bound
`log (sigma2 / D) / (2 * log 2)`, that is `(1 / 2) log_2 (sigma2 / D)`.

Source: Cover and Thomas, Elements of Information Theory, 2nd ed. (2006),
Theorem 10.3.2 (rate-distortion function of a Gaussian source under
squared-error distortion, `R(D) = (1 / 2) log_2 (sigma2 / D)` for
`0 < D < sigma2`); this module proves the converse inequality
`R(D) ≥ (1 / 2) log_2 (sigma2 / D)` by the normalized density test above
rather than the entropy argument of that section.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MathlibExt.InformationTheory.GaussianDistortionConverse

open MathlibExt.InformationTheory.GaussianDistortionFeasibility

/-- The normalized Gaussian test function, on a source/reproduction pair:
the log density of the error under variance `D` minus the log density
of the source under variance `sigma2`. Both variances are nonnegative
reals; the density test is used only when they are positive. -/
noncomputable def gaussianTest (D σ2 : ℝ≥0) (z : ℝ × ℝ) : ℝ :=
  Real.log (gaussianPDFReal 0 D (z.1 - z.2)) - Real.log (gaussianPDFReal 0 σ2 z.1)

/-- The product of the two marginals of a joint law on pairs. -/
noncomputable def productMarginal (μ : ProbabilityMeasure (ℝ × ℝ)) : Measure (ℝ × ℝ) :=
  ((μ : Measure (ℝ × ℝ)).map Prod.fst).prod ((μ : Measure (ℝ × ℝ)).map Prod.snd)


private theorem log_gaussianPDFReal_of_ne_zero (v : ℝ≥0) (hv : v ≠ 0) (x : ℝ) :
    Real.log (gaussianPDFReal 0 v x)
      = -(Real.log (2 * Real.pi * (v : ℝ)) / 2) - x ^ 2 / (2 * (v : ℝ)) := by
  have hvR : 0 < (v : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  have h2pv : 0 < 2 * Real.pi * (v : ℝ) := by positivity
  have hpdf : gaussianPDFReal 0 v x
      = (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹
        * Real.exp (-(x - 0) ^ 2 / (2 * (v : ℝ))) :=
    congrFun (gaussianPDFReal_def 0 v) x
  rw [hpdf, Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_inv,
    Real.log_sqrt h2pv.le, Real.log_exp]
  simp only [sub_zero]
  ring

private theorem nnreal_ne_zero_of_coe_pos {v : ℝ≥0} (h : (0 : ℝ) < (v : ℝ)) : v ≠ 0 := by
  intro hv
  rw [hv] at h
  simp only [NNReal.coe_zero] at h
  exact (lt_irrefl 0) h

/-- The Gaussian test function is measurable. -/
theorem measurable_gaussianTest (D σ2 : ℝ≥0) :
    Measurable (gaussianTest D σ2) := by
  unfold gaussianTest
  exact (Real.measurable_log.comp
    ((measurable_gaussianPDFReal 0 D).comp (measurable_fst.sub measurable_snd))).sub
    (Real.measurable_log.comp ((measurable_gaussianPDFReal 0 σ2).comp measurable_fst))

/-- Pointwise form of the Gaussian test: the quadratic terms are the
normalized error energy and the normalized source energy. -/
theorem gaussianTest_eq (D σ2 : ℝ≥0) (hD : (0 : ℝ) < (D : ℝ))
    (hσ2 : (0 : ℝ) < (σ2 : ℝ)) (z : ℝ × ℝ) :
    gaussianTest D σ2 z = Real.log ((σ2 : ℝ) / (D : ℝ)) / 2
      - (z.1 - z.2) ^ 2 / (2 * (D : ℝ)) + z.1 ^ 2 / (2 * (σ2 : ℝ)) := by
  have hD0 : D ≠ 0 := nnreal_ne_zero_of_coe_pos hD
  have hσ0 : σ2 ≠ 0 := nnreal_ne_zero_of_coe_pos hσ2
  have hlog : Real.log (2 * Real.pi * (σ2 : ℝ)) - Real.log (2 * Real.pi * (D : ℝ))
      = Real.log ((σ2 : ℝ) / (D : ℝ)) := by
    have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
    rw [Real.log_div hσ2.ne' hD.ne', Real.log_mul h2pi.ne' hσ2.ne',
      Real.log_mul h2pi.ne' hD.ne']
    ring
  unfold gaussianTest
  rw [log_gaussianPDFReal_of_ne_zero D hD0 (z.1 - z.2),
    log_gaussianPDFReal_of_ne_zero σ2 hσ0 z.1]
  linarith [hlog]

/-- At the zero pair the Gaussian test takes its constant value. -/
theorem gaussianTest_zero_zero (D σ2 : ℝ≥0) (hD : (0 : ℝ) < (D : ℝ))
    (hσ2 : (0 : ℝ) < (σ2 : ℝ)) :
    gaussianTest D σ2 (0, 0) = Real.log ((σ2 : ℝ) / (D : ℝ)) / 2 := by
  rw [gaussianTest_eq D σ2 hD hσ2 (0, 0)]
  simp


private theorem integrable_sq_id_gaussian (v : ℝ≥0) :
    Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 v) :=
  (memLp_id_gaussianReal (μ := (0 : ℝ)) (v := v) 2).integrable_sq

private theorem integrable_sq_error_of_mem_distortionFeasible (σ2 : ℝ≥0) (D : ℝ≥0)
    (μ : ProbabilityMeasure (ℝ × ℝ)) (hμ : μ ∈ distortionFeasible σ2 (D : ℝ)) :
    Integrable (fun z : ℝ × ℝ => (z.1 - z.2) ^ 2) (μ : Measure (ℝ × ℝ)) :=
  ((mem_distortionFeasible_iff (NNReal.coe_nonneg D) μ).mp hμ).2.1

private theorem map_fst_of_mem_distortionFeasible (σ2 : ℝ≥0) (D : ℝ≥0)
    (μ : ProbabilityMeasure (ℝ × ℝ)) (hμ : μ ∈ distortionFeasible σ2 (D : ℝ)) :
    (μ : Measure (ℝ × ℝ)).map Prod.fst = gaussianReal 0 σ2 :=
  ((mem_distortionFeasible_iff (NNReal.coe_nonneg D) μ).mp hμ).1

private theorem integrable_sq_fst_of_mem_distortionFeasible (σ2 : ℝ≥0) (D : ℝ≥0)
    (μ : ProbabilityMeasure (ℝ × ℝ)) (hμ : μ ∈ distortionFeasible σ2 (D : ℝ)) :
    Integrable (fun z : ℝ × ℝ => z.1 ^ 2) (μ : Measure (ℝ × ℝ)) := by
  have hfst := map_fst_of_mem_distortionFeasible σ2 D μ hμ
  have key : Integrable (fun x : ℝ => x ^ 2)
      ((μ : Measure (ℝ × ℝ)).map Prod.fst) := hfst.symm ▸ integrable_sq_id_gaussian σ2
  have hcomp := key.comp_measurable measurable_fst
  exact hcomp

private theorem integral_sq_fst_of_mem_distortionFeasible (σ2 : ℝ≥0) (D : ℝ≥0)
    (μ : ProbabilityMeasure (ℝ × ℝ)) (hμ : μ ∈ distortionFeasible σ2 (D : ℝ)) :
    ∫ z : ℝ × ℝ, z.1 ^ 2 ∂(μ : Measure (ℝ × ℝ)) = (σ2 : ℝ) := by
  have hfst := map_fst_of_mem_distortionFeasible σ2 D μ hμ
  have hmap : ∫ z : ℝ × ℝ, z.1 ^ 2 ∂(μ : Measure (ℝ × ℝ))
      = ∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 σ2) := by
    rw [← hfst]
    rw [integral_map measurable_fst.aemeasurable (by fun_prop)]
  rw [hmap]
  have hvar := variance_id_gaussianReal (μ := (0 : ℝ)) (v := σ2)
  rw [variance_eq_sub (memLp_id_gaussianReal (μ := (0 : ℝ)) (v := σ2) 2)] at hvar
  simp only [integral_id_gaussianReal, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, sub_zero, Pi.pow_apply, id_eq] at hvar
  exact hvar

private theorem integral_sq_error_le_of_mem_distortionFeasible (σ2 : ℝ≥0) (D : ℝ≥0)
    (μ : ProbabilityMeasure (ℝ × ℝ)) (hμ : μ ∈ distortionFeasible σ2 (D : ℝ)) :
    ∫ z : ℝ × ℝ, (z.1 - z.2) ^ 2 ∂(μ : Measure (ℝ × ℝ)) ≤ (D : ℝ) :=
  ((mem_distortionFeasible_iff (NNReal.coe_nonneg D) μ).mp hμ).2.2

/-- Integrability of the Gaussian test under a distortion-feasible law,
derived from the source second moment and the square-error bound. -/
theorem integrable_gaussianTest_of_mem_distortionFeasible (σ2 : ℝ≥0) (D : ℝ≥0)
    (μ : ProbabilityMeasure (ℝ × ℝ)) (hμ : μ ∈ distortionFeasible σ2 (D : ℝ)) :
    Integrable (gaussianTest D σ2) (μ : Measure (ℝ × ℝ)) := by
  have herr := integrable_sq_error_of_mem_distortionFeasible σ2 D μ hμ
  have hsrc := integrable_sq_fst_of_mem_distortionFeasible σ2 D μ hμ
  by_cases hD0 : D = 0
  · by_cases hσ0 : σ2 = 0
    · have hfun : gaussianTest D σ2 = fun _ : ℝ × ℝ => (0 : ℝ) := by
        funext z
        unfold gaussianTest
        rw [hD0, hσ0]
        have e1 : gaussianPDFReal 0 (0 : ℝ≥0) (z.1 - z.2) = 0 :=
          congrFun (gaussianPDFReal_zero_var (0 : ℝ)) (z.1 - z.2)
        have e2 : gaussianPDFReal 0 (0 : ℝ≥0) z.1 = 0 :=
          congrFun (gaussianPDFReal_zero_var (0 : ℝ)) z.1
        rw [e1, e2, Real.log_zero, sub_self]
      rw [hfun]
      exact integrable_const (0 : ℝ)
    · have hfun : gaussianTest D σ2
          = fun z : ℝ × ℝ => Real.log (2 * Real.pi * (σ2 : ℝ)) / 2
            + z.1 ^ 2 / (2 * (σ2 : ℝ)) := by
        funext z
        unfold gaussianTest
        rw [hD0]
        have e1 : gaussianPDFReal 0 (0 : ℝ≥0) (z.1 - z.2) = 0 :=
          congrFun (gaussianPDFReal_zero_var (0 : ℝ)) (z.1 - z.2)
        rw [e1, Real.log_zero, zero_sub, log_gaussianPDFReal_of_ne_zero σ2 hσ0 z.1]
        ring
      rw [hfun]
      exact (integrable_const _).add (hsrc.div_const _)
  · by_cases hσ0 : σ2 = 0
    · have hfun : gaussianTest D σ2
          = fun z : ℝ × ℝ => -(Real.log (2 * Real.pi * (D : ℝ)) / 2)
            - (z.1 - z.2) ^ 2 / (2 * (D : ℝ)) := by
        funext z
        unfold gaussianTest
        rw [hσ0]
        have e2 : gaussianPDFReal 0 (0 : ℝ≥0) z.1 = 0 :=
          congrFun (gaussianPDFReal_zero_var (0 : ℝ)) z.1
        rw [e2, Real.log_zero, sub_zero, log_gaussianPDFReal_of_ne_zero D hD0 (z.1 - z.2)]
      rw [hfun]
      exact (integrable_const _).sub (herr.div_const _)
    · have hDpos : (0 : ℝ) < (D : ℝ) :=
        NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hD0)
      have hσpos : (0 : ℝ) < (σ2 : ℝ) :=
        NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hσ0)
      have hfun : gaussianTest D σ2
          = fun z : ℝ × ℝ => Real.log ((σ2 : ℝ) / (D : ℝ)) / 2
            - (z.1 - z.2) ^ 2 / (2 * (D : ℝ)) + z.1 ^ 2 / (2 * (σ2 : ℝ)) := by
        funext z
        exact gaussianTest_eq D σ2 hDpos hσpos z
      rw [hfun]
      exact ((integrable_const _).sub (herr.div_const _)).add (hsrc.div_const _)


private theorem isProbabilityMeasure_productMarginal
    (μ : ProbabilityMeasure (ℝ × ℝ)) : IsProbabilityMeasure (productMarginal μ) := by
  constructor
  unfold productMarginal
  rw [← Set.univ_prod_univ, MeasureTheory.Measure.prod_prod]
  simp

private theorem exp_gaussianTest_eq_div (D σ2 : ℝ≥0) (hD : D ≠ 0) (hσ : σ2 ≠ 0)
    (z : ℝ × ℝ) :
    Real.exp (gaussianTest D σ2 z)
      = gaussianPDFReal 0 D (z.1 - z.2) / gaussianPDFReal 0 σ2 z.1 := by
  unfold gaussianTest
  rw [Real.exp_sub, Real.exp_log (gaussianPDFReal_pos 0 D _ hD),
    Real.exp_log (gaussianPDFReal_pos 0 σ2 _ hσ)]

private theorem lintegral_exp_gaussianTest_productMarginal_eq_one (σ2 : ℝ≥0)
    (D : ℝ≥0) (hD : (0 : ℝ) < (D : ℝ)) (hσ2 : (0 : ℝ) < (σ2 : ℝ))
    (μ : ProbabilityMeasure (ℝ × ℝ)) (hμ : μ ∈ distortionFeasible σ2 (D : ℝ)) :
    ∫⁻ z, ENNReal.ofReal (Real.exp (gaussianTest D σ2 z))
        ∂(productMarginal μ) = 1 := by
  have hfst := map_fst_of_mem_distortionFeasible σ2 D μ hμ
  have hD0 : D ≠ 0 := nnreal_ne_zero_of_coe_pos hD
  have hσ0 : σ2 ≠ 0 := nnreal_ne_zero_of_coe_pos hσ2
  have hF : Measurable
      (fun z : ℝ × ℝ => ENNReal.ofReal (Real.exp (gaussianTest D σ2 z))) :=
    ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp (measurable_gaussianTest D σ2))
  have key : ∀ z : ℝ × ℝ, gaussianPDF 0 σ2 z.1
        * ENNReal.ofReal (Real.exp (gaussianTest D σ2 z))
      = ENNReal.ofReal (gaussianPDFReal 0 D (z.1 - z.2)) := by
    intro z
    rw [gaussianPDF, exp_gaussianTest_eq_div D σ2 hD0 hσ0 z,
      ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg 0 σ2 z.1)]
    congr 1
    have hpos : (0 : ℝ) < gaussianPDFReal 0 σ2 z.1 :=
      gaussianPDFReal_pos 0 σ2 z.1 hσ0
    field_simp
  calc ∫⁻ z, ENNReal.ofReal (Real.exp (gaussianTest D σ2 z))
          ∂(productMarginal μ)
      = ∫⁻ z, ENNReal.ofReal (Real.exp (gaussianTest D σ2 z))
          ∂((volume.withDensity (gaussianPDF 0 σ2)).prod
            ((μ : Measure (ℝ × ℝ)).map Prod.snd)) := by
        unfold productMarginal
        rw [hfst, gaussianReal_of_var_ne_zero 0 hσ0]
    _ = ∫⁻ z, ENNReal.ofReal (Real.exp (gaussianTest D σ2 z))
          ∂((volume.prod ((μ : Measure (ℝ × ℝ)).map Prod.snd)).withDensity
            (fun z : ℝ × ℝ => gaussianPDF 0 σ2 z.1)) := by
        rw [prod_withDensity_left (measurable_gaussianPDF 0 σ2)]
    _ = ∫⁻ z, gaussianPDF 0 σ2 z.1
          * ENNReal.ofReal (Real.exp (gaussianTest D σ2 z))
          ∂(volume.prod ((μ : Measure (ℝ × ℝ)).map Prod.snd)) :=
        lintegral_withDensity_eq_lintegral_mul _
          ((measurable_gaussianPDF 0 σ2).comp measurable_fst) hF
    _ = ∫⁻ z, ENNReal.ofReal (gaussianPDFReal 0 D (z.1 - z.2))
          ∂(volume.prod ((μ : Measure (ℝ × ℝ)).map Prod.snd)) :=
        lintegral_congr key
    _ = ∫⁻ y, ∫⁻ x, ENNReal.ofReal (gaussianPDFReal 0 D (x - y))
          ∂volume ∂((μ : Measure (ℝ × ℝ)).map Prod.snd) := by
        apply lintegral_prod_symm
        exact (ENNReal.measurable_ofReal.comp
          ((measurable_gaussianPDFReal 0 D).comp
            (measurable_fst.sub measurable_snd))).aemeasurable
    _ = ∫⁻ _y, (1 : ℝ≥0∞) ∂((μ : Measure (ℝ × ℝ)).map Prod.snd) := by
        apply lintegral_congr
        intro y
        calc ∫⁻ x, ENNReal.ofReal (gaussianPDFReal 0 D (x - y)) ∂volume
            = ∫⁻ x, ENNReal.ofReal (gaussianPDFReal y D x) ∂volume := by
              apply lintegral_congr
              intro x
              rw [gaussianPDFReal_sub x y]
              simp
          _ = 1 := lintegral_gaussianPDFReal_eq_one y hD0
    _ = 1 := by simp

/-- Integrability of the exponentiated Gaussian test against the product
of the marginals of a distortion-feasible law. -/
theorem integrable_exp_gaussianTest_productMarginal_of_mem_distortionFeasible
    (σ2 : ℝ≥0) (D : ℝ≥0) (hD : (0 : ℝ) < (D : ℝ)) (μ : ProbabilityMeasure (ℝ × ℝ))
    (hμ : μ ∈ distortionFeasible σ2 (D : ℝ)) :
    Integrable (fun z : ℝ × ℝ => Real.exp (gaussianTest D σ2 z)) (productMarginal μ) := by
  have hD0 : D ≠ 0 := nnreal_ne_zero_of_coe_pos hD
  have hmeas : AEStronglyMeasurable
      (fun z : ℝ × ℝ => Real.exp (gaussianTest D σ2 z)) (productMarginal μ) :=
    (Real.measurable_exp.comp (measurable_gaussianTest D σ2)).aestronglyMeasurable
  by_cases hσ0 : σ2 = 0
  · have := isProbabilityMeasure_productMarginal μ
    have hval : ∀ z : ℝ × ℝ, Real.exp (gaussianTest D σ2 z)
        = gaussianPDFReal 0 D (z.1 - z.2) := by
      intro z
      unfold gaussianTest
      rw [hσ0]
      have e2 : gaussianPDFReal 0 (0 : ℝ≥0) z.1 = 0 :=
        congrFun (gaussianPDFReal_zero_var (0 : ℝ)) z.1
      rw [e2, Real.log_zero, sub_zero,
        Real.exp_log (gaussianPDFReal_pos 0 D _ hD0)]
    have hbound : ∀ z : ℝ × ℝ, Real.exp (gaussianTest D σ2 z)
        ≤ (Real.sqrt (2 * Real.pi * (D : ℝ)))⁻¹ := by
      intro z
      rw [hval z]
      have hpdf : gaussianPDFReal 0 D (z.1 - z.2)
          = (Real.sqrt (2 * Real.pi * (D : ℝ)))⁻¹
            * Real.exp (-(z.1 - z.2) ^ 2 / (2 * (D : ℝ))) := by
        have h := congrFun (gaussianPDFReal_def 0 D) (z.1 - z.2)
        rw [h]
        simp only [sub_zero]
      rw [hpdf]
      have hexp : Real.exp (-(z.1 - z.2) ^ 2 / (2 * (D : ℝ))) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        apply div_nonpos_of_nonpos_of_nonneg
        · simp only [neg_nonpos]
          exact sq_nonneg _
        · positivity
      have hfac : (0 : ℝ) ≤ (Real.sqrt (2 * Real.pi * (D : ℝ)))⁻¹ := by positivity
      calc (Real.sqrt (2 * Real.pi * (D : ℝ)))⁻¹
              * Real.exp (-(z.1 - z.2) ^ 2 / (2 * (D : ℝ)))
          ≤ (Real.sqrt (2 * Real.pi * (D : ℝ)))⁻¹ * 1 :=
            mul_le_mul_of_nonneg_left hexp hfac
        _ = (Real.sqrt (2 * Real.pi * (D : ℝ)))⁻¹ := mul_one _
    refine Integrable.of_bound hmeas (Real.sqrt (2 * Real.pi * (D : ℝ)))⁻¹
      (ae_of_all _ (fun z => ?_))
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact hbound z
  · have hσpos : (0 : ℝ) < (σ2 : ℝ) :=
      NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hσ0)
    refine ⟨hmeas, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal
      (ae_of_all _ (fun z : ℝ × ℝ => Real.exp_nonneg _))]
    rw [lintegral_exp_gaussianTest_productMarginal_eq_one σ2 D hD hσpos μ hμ]
    exact ENNReal.one_lt_top

/-- **Normalization.** The exponentiated Gaussian test integrates to one
against the product of the marginals of a distortion-feasible law: the
source marginal density cancels the denominator of the test, and the
remaining error density integrates to one. -/
theorem integral_exp_gaussianTest_productMarginal_eq_one (σ2 : ℝ≥0) (D : ℝ≥0)
    (hD : (0 : ℝ) < (D : ℝ)) (hσ2 : (0 : ℝ) < (σ2 : ℝ)) (μ : ProbabilityMeasure (ℝ × ℝ))
    (hμ : μ ∈ distortionFeasible σ2 (D : ℝ)) :
    ∫ z : ℝ × ℝ, Real.exp (gaussianTest D σ2 z) ∂(productMarginal μ) = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ (fun z : ℝ × ℝ => Real.exp_nonneg _))
    (Real.measurable_exp.comp (measurable_gaussianTest D σ2)).aestronglyMeasurable,
    lintegral_exp_gaussianTest_productMarginal_eq_one σ2 D hD hσ2 μ hμ]
  rfl


private theorem integral_gaussianTest_formula (σ2 : ℝ≥0) (D : ℝ≥0)
    (hD : (0 : ℝ) < (D : ℝ)) (hσ2 : (0 : ℝ) < (σ2 : ℝ))
    (μ : ProbabilityMeasure (ℝ × ℝ)) (hμ : μ ∈ distortionFeasible σ2 (D : ℝ)) :
    ∫ z : ℝ × ℝ, gaussianTest D σ2 z ∂(μ : Measure (ℝ × ℝ))
      = Real.log ((σ2 : ℝ) / (D : ℝ)) / 2
        - (∫ z : ℝ × ℝ, (z.1 - z.2) ^ 2 ∂(μ : Measure (ℝ × ℝ))) / (2 * (D : ℝ))
        + (∫ z : ℝ × ℝ, z.1 ^ 2 ∂(μ : Measure (ℝ × ℝ))) / (2 * (σ2 : ℝ)) := by
  have herr := integrable_sq_error_of_mem_distortionFeasible σ2 D μ hμ
  have hsrc := integrable_sq_fst_of_mem_distortionFeasible σ2 D μ hμ
  calc ∫ z : ℝ × ℝ, gaussianTest D σ2 z ∂(μ : Measure (ℝ × ℝ))
      = ∫ z : ℝ × ℝ, (Real.log ((σ2 : ℝ) / (D : ℝ)) / 2
          - (z.1 - z.2) ^ 2 / (2 * (D : ℝ))
          + z.1 ^ 2 / (2 * (σ2 : ℝ))) ∂(μ : Measure (ℝ × ℝ)) := by
        apply integral_congr_ae
        exact ae_of_all _ (fun z => gaussianTest_eq D σ2 hD hσ2 z)
    _ = Real.log ((σ2 : ℝ) / (D : ℝ)) / 2
          - (∫ z : ℝ × ℝ, (z.1 - z.2) ^ 2 ∂(μ : Measure (ℝ × ℝ))) / (2 * (D : ℝ))
          + (∫ z : ℝ × ℝ, z.1 ^ 2 ∂(μ : Measure (ℝ × ℝ))) / (2 * (σ2 : ℝ)) := by
        have hA : Integrable (fun z : ℝ × ℝ => Real.log ((σ2 : ℝ) / (D : ℝ)) / 2
            - (z.1 - z.2) ^ 2 / (2 * (D : ℝ))) (μ : Measure (ℝ × ℝ)) :=
          (integrable_const _).sub (herr.div_const _)
        have hB : Integrable (fun z : ℝ × ℝ => z.1 ^ 2 / (2 * (σ2 : ℝ)))
            (μ : Measure (ℝ × ℝ)) := hsrc.div_const _
        have e1 := integral_add hA hB
        have e2 := integral_sub (integrable_const
          (Real.log ((σ2 : ℝ) / (D : ℝ)) / 2)) (herr.div_const (2 * (D : ℝ)))
        rw [e1, e2]
        simp only [integral_div]
        simp

/-- **Test mean.** Under a distortion-feasible law with `0 < D < sigma2`,
the mean of the Gaussian test is at least `log (sigma2 / D) / 2`. -/
theorem integral_gaussianTest_ge (σ2 : ℝ≥0) (D : ℝ≥0) (hD : (0 : ℝ) < (D : ℝ))
    (hDσ2 : (D : ℝ) < (σ2 : ℝ)) (μ : ProbabilityMeasure (ℝ × ℝ))
    (hμ : μ ∈ distortionFeasible σ2 (D : ℝ)) :
    Real.log ((σ2 : ℝ) / (D : ℝ)) / 2 ≤
      ∫ z : ℝ × ℝ, gaussianTest D σ2 z ∂(μ : Measure (ℝ × ℝ)) := by
  have hσ2 : (0 : ℝ) < (σ2 : ℝ) := lt_trans hD hDσ2
  rw [integral_gaussianTest_formula σ2 D hD hσ2 μ hμ,
    integral_sq_fst_of_mem_distortionFeasible σ2 D μ hμ]
  have herr_le := integral_sq_error_le_of_mem_distortionFeasible σ2 D μ hμ
  have hterm : (∫ z : ℝ × ℝ, (z.1 - z.2) ^ 2 ∂(μ : Measure (ℝ × ℝ)))
        / (2 * (D : ℝ)) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (D : ℝ))]
    linarith [herr_le]
  have hσeq : (σ2 : ℝ) / (2 * (σ2 : ℝ)) = 1 / 2 := by
    field_simp
  rw [hσeq]
  linarith

/-- With expected square error strictly below `D`, the test mean is
strictly above `log (sigma2 / D) / 2`. -/
theorem integral_gaussianTest_gt_of_integral_sq_error_lt (σ2 : ℝ≥0) (D : ℝ≥0)
    (hD : (0 : ℝ) < (D : ℝ)) (hDσ2 : (D : ℝ) < (σ2 : ℝ))
    (μ : ProbabilityMeasure (ℝ × ℝ)) (hμ : μ ∈ distortionFeasible σ2 (D : ℝ))
    (hlt : ∫ z : ℝ × ℝ, (z.1 - z.2) ^ 2 ∂(μ : Measure (ℝ × ℝ)) < (D : ℝ)) :
    Real.log ((σ2 : ℝ) / (D : ℝ)) / 2 <
      ∫ z : ℝ × ℝ, gaussianTest D σ2 z ∂(μ : Measure (ℝ × ℝ)) := by
  have hσ2 : (0 : ℝ) < (σ2 : ℝ) := lt_trans hD hDσ2
  rw [integral_gaussianTest_formula σ2 D hD hσ2 μ hμ,
    integral_sq_fst_of_mem_distortionFeasible σ2 D μ hμ]
  have hterm : (∫ z : ℝ × ℝ, (z.1 - z.2) ^ 2 ∂(μ : Measure (ℝ × ℝ)))
        / (2 * (D : ℝ)) < 1 / 2 := by
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (D : ℝ))]
    linarith [hlt]
  have hσeq : (σ2 : ℝ) / (2 * (σ2 : ℝ)) = 1 / 2 := by
    field_simp
  rw [hσeq]
  linarith

/-- The normalized test bound applied to a distortion-feasible law: the
Kullback-Leibler divergence from the joint law to the product of its
marginals is at least the real test mean. -/
theorem ofReal_integral_gaussianTest_le_klDiv_productMarginal (σ2 : ℝ≥0) (D : ℝ≥0)
    (hD : (0 : ℝ) < (D : ℝ)) (hσ2 : (0 : ℝ) < (σ2 : ℝ)) (μ : ProbabilityMeasure (ℝ × ℝ))
    (hμ : μ ∈ distortionFeasible σ2 (D : ℝ)) :
    ENNReal.ofReal (∫ z : ℝ × ℝ, gaussianTest D σ2 z ∂(μ : Measure (ℝ × ℝ))) ≤
      InformationTheory.klDiv (μ : Measure (ℝ × ℝ)) (productMarginal μ) := by
  haveI := isProbabilityMeasure_productMarginal μ
  exact NormalizedKLTestBound.ofReal_integral_le_klDiv (μ : Measure (ℝ × ℝ))
    (productMarginal μ) (measurable_gaussianTest D σ2)
    (integrable_gaussianTest_of_mem_distortionFeasible σ2 D μ hμ)
    (integrable_exp_gaussianTest_productMarginal_of_mem_distortionFeasible σ2 D hD μ hμ)
    (integral_exp_gaussianTest_productMarginal_eq_one σ2 D hD hσ2 μ hμ)

/-- Every distortion-feasible law has mutual information, in bits, at
least `log (sigma2 / D) / (2 * log 2)`. -/
theorem measureMutualInformation_ge_of_mem_distortionFeasible (σ2 : ℝ≥0) (D : ℝ≥0)
    (hD : (0 : ℝ) < (D : ℝ)) (hDσ2 : (D : ℝ) < (σ2 : ℝ))
    (μ : ProbabilityMeasure (ℝ × ℝ)) (hμ : μ ∈ distortionFeasible σ2 (D : ℝ)) :
    ENNReal.ofReal (Real.log ((σ2 : ℝ) / (D : ℝ)) / (2 * Real.log 2)) ≤
      InformationTheory.measureMutualInformation μ := by
  have hσpos : (0 : ℝ) < (σ2 : ℝ) := lt_trans hD hDσ2
  have hge := integral_gaussianTest_ge σ2 D hD hDσ2 μ hμ
  have hkl := ofReal_integral_gaussianTest_le_klDiv_productMarginal
    σ2 D hD hσpos μ hμ
  have hle : ENNReal.ofReal (Real.log ((σ2 : ℝ) / (D : ℝ)) / 2)
      ≤ InformationTheory.klDiv (μ : Measure (ℝ × ℝ)) (productMarginal μ) :=
    (ENNReal.ofReal_le_ofReal hge).trans hkl
  have harg : Real.log ((σ2 : ℝ) / (D : ℝ)) / (2 * Real.log 2)
      = (Real.log ((σ2 : ℝ) / (D : ℝ)) / 2) / Real.log 2 := by ring
  change ENNReal.ofReal (Real.log ((σ2 : ℝ) / (D : ℝ)) / (2 * Real.log 2))
    ≤ InformationTheory.klDiv (μ : Measure (ℝ × ℝ)) (productMarginal μ)
      / ENNReal.ofReal (Real.log 2)
  rw [harg, ENNReal.ofReal_div_of_pos (Real.log_pos (by norm_num))]
  exact ENNReal.div_le_div_right hle _

/-- **Gaussian rate-distortion converse.** For `0 < D < sigma2`, the
Gaussian rate-distortion function at `D`, in bits, is at least
`log (sigma2 / D) / (2 * log 2)`. -/
theorem rateDistortion_ge_ofReal_log_div (σ2 : ℝ≥0) (D : ℝ≥0)
    (hD : (0 : ℝ) < (D : ℝ)) (hDσ2 : (D : ℝ) < (σ2 : ℝ)) :
    ENNReal.ofReal (Real.log ((σ2 : ℝ) / (D : ℝ)) / (2 * Real.log 2)) ≤
      rateDistortion σ2 (D : ℝ) := by
  change ENNReal.ofReal (Real.log ((σ2 : ℝ) / (D : ℝ)) / (2 * Real.log 2))
    ≤ ⨅ μ ∈ distortionFeasible σ2 (D : ℝ),
      InformationTheory.measureMutualInformation μ
  apply le_iInf
  intro μ
  apply le_iInf
  intro hμ
  exact measureMutualInformation_ge_of_mem_distortionFeasible σ2 D hD hDσ2 μ hμ

end MathlibExt.InformationTheory.GaussianDistortionConverse
