/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Probability.Distributions.Cauchy
public import Mathlib.MeasureTheory.Integral.Pi
public import MathlibExt.Probability.KernelMeanEmbedding

/-!
# Characteristic translation-invariant kernels on `ℝ^d`

This module proves the characterization of characteristic translation-invariant kernels; its
main result is `isCharacteristic_iff_support_eq_univ`. A bounded continuous
translation-invariant kernel `k(x, y) = ψ(x - y)` on `ℝ^d` is the Fourier
transform of a finite nonnegative Borel measure `Λ` by Bochner's theorem,
`ψ(x) = ∫ exp(-i xᵀω) dΛ(ω)`. Sriperumbudur, Gretton, Fukumizu, Schölkopf and Lanckriet showed
that such a kernel is characteristic (its kernel mean embedding is injective on Borel probability
measures) exactly when `Λ` has full support. This covers the Gaussian, Laplacian and `B_{2n+1}`
spline kernels, whose spectra have full support, and excludes periodic kernels and the sinc
kernel, whose spectra do not. For sufficiency the proof writes the squared MMD as
`∫ |φ_P(ω) - φ_Q(ω)|² dΛ(ω)` in terms of the characteristic functions of `P` and `Q`
(Corollary 4(i)) and uses their uniqueness; for necessity it constructs `P ≠ Q` with equal
embeddings when `Λ` misses an open set (Lemma 16). Both steps are formalized below.

For a bounded continuous kernel every Borel probability measure has a Bochner integrable feature
map, so `KernelMeanEmbedding.IsCharacteristic` (injectivity on probability measures with
integrable feature map) is the paper's notion here. The dimension is `d ≥ 1`: on the one-point
space `ℝ^0` every kernel is characteristic, while the zero measure has empty support.

Reference: B. K. Sriperumbudur, A. Gretton, K. Fukumizu, B. Schölkopf and G. R. G. Lanckriet,
"Hilbert space embeddings and metrics on probability measures", *J. Mach. Learn. Res.* **11**
(2010), 1517–1561, Theorem 9 (with Assumption 1 and equation (11)).
-/

@[expose] public section

open MeasureTheory MathlibExt.Probability.KernelMeanEmbedding
open scoped InnerProductSpace FourierTransform

namespace MathlibExt.Probability.TranslationInvariantCharacteristicKernelWanted

section Helpers

variable {d : ℕ} {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [RKHS ℝ H (EuclideanSpace ℝ (Fin d)) ℝ]

private lemma kernelValue_eq_charFun (Λ : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure Λ]
    (hk : ∀ x y : EuclideanSpace ℝ (Fin d), (kernelValue H x y : ℂ) =
    ∫ ω, Complex.exp (-((⟪x - y, ω⟫_ℝ : ℝ) : ℂ) * Complex.I) ∂Λ) (x y : EuclideanSpace ℝ (Fin d)) :
    (kernelValue H x y : ℂ) = MeasureTheory.charFun Λ (-(x - y)) := by
  rw [hk x y]
  simp only [MeasureTheory.charFun_apply]
  congr 1
  ext ω
  rw [inner_neg_right, real_inner_comm ω (x - y)]
  simp

private lemma kernelValue_diag (Λ : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure Λ]
    (hk : ∀ x y : EuclideanSpace ℝ (Fin d), (kernelValue H x y : ℂ) =
    ∫ ω, Complex.exp (-((⟪x - y, ω⟫_ℝ : ℝ) : ℂ) * Complex.I) ∂Λ) (x : EuclideanSpace ℝ (Fin d)) :
    kernelValue H x x = Λ.real Set.univ := by
  have h := kernelValue_eq_charFun Λ hk x x
  rw [sub_self, neg_zero] at h
  have h2 : MeasureTheory.charFun Λ (0 : EuclideanSpace ℝ (Fin d)) = Λ.real Set.univ := by
    simp [MeasureTheory.charFun_apply]
  rw [h2] at h
  exact Complex.ofReal_injective h

private lemma continuous_kernelValue (Λ : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure Λ]
    (hk : ∀ x y : EuclideanSpace ℝ (Fin d), (kernelValue H x y : ℂ) =
    ∫ ω, Complex.exp (-((⟪x - y, ω⟫_ℝ : ℝ) : ℂ) * Complex.I) ∂Λ) :
    Continuous fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      kernelValue H p.1 p.2 := by
  have heq : (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      kernelValue H p.1 p.2) =
      fun p => (MeasureTheory.charFun Λ (-(p.1 - p.2))).re := by
    funext p
    have h := kernelValue_eq_charFun Λ hk p.1 p.2
    have := congrArg Complex.re h
    simpa using this
  rw [heq]
  exact Complex.continuous_re.comp (MeasureTheory.continuous_charFun.comp
    ((continuous_fst.sub continuous_snd).neg))

private lemma integrable_featureMap (Λ : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure Λ]
    (hk : ∀ x y : EuclideanSpace ℝ (Fin d), (kernelValue H x y : ℂ) =
    ∫ ω, Complex.exp (-((⟪x - y, ω⟫_ℝ : ℝ) : ℂ) * Complex.I) ∂Λ)
    (μ : Measure (EuclideanSpace ℝ (Fin d)))
    [IsFiniteMeasure μ] : Integrable (featureMap H) μ := by
  apply integrable_featureMap_of_integrable_sqrt
  · exact (continuous_featureMap_of_continuous_kernelValue
      (continuous_kernelValue Λ hk)).aestronglyMeasurable
  · have hdiag : (fun x => √(kernelValue H x x)) = fun _ => √(Λ.real Set.univ) := by
      funext x
      rw [kernelValue_diag Λ hk]
    rw [hdiag]
    exact integrable_const _

private lemma exp_norm (r : ℝ) : ‖Complex.exp ((r : ℂ) * Complex.I)‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I r

private lemma double_integral
    (Λ : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure Λ]
    (hk : ∀ x y : EuclideanSpace ℝ (Fin d), (kernelValue H x y : ℂ) =
      ∫ ω, Complex.exp (-((⟪x - y, ω⟫_ℝ : ℝ) : ℂ) * Complex.I) ∂Λ)
    (μ ν : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ((∫ z, kernelValue H z.1 z.2 ∂(μ.prod ν) : ℝ) : ℂ) =
      ∫ ω, MeasureTheory.charFun μ (-ω) * (starRingEnd ℂ) (MeasureTheory.charFun ν (-ω)) ∂Λ := by
  have hprod : ∀ ω : EuclideanSpace ℝ (Fin d),
      MeasureTheory.charFun μ (-ω) * (starRingEnd ℂ) (MeasureTheory.charFun ν (-ω)) =
        ∫ z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d),
          Complex.exp (-((⟪z.1, ω⟫_ℝ : ℝ) : ℂ) * Complex.I) *
          Complex.exp (((⟪z.2, ω⟫_ℝ : ℝ) : ℂ) * Complex.I) ∂(μ.prod ν) := by
    intro ω
    have hconj : (starRingEnd ℂ) (MeasureTheory.charFun ν (-ω)) =
        MeasureTheory.charFun ν ω := by
      rw [MeasureTheory.charFun_neg]
      simp
    rw [hconj, MeasureTheory.charFun_apply, MeasureTheory.charFun_apply,
      ← integral_prod_mul]
    apply integral_congr_ae
    filter_upwards with z
    congr 1
    rw [inner_neg_right]
    simp
  have hexp : ∀ ω : EuclideanSpace ℝ (Fin d),
      ∀ z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d),
      Complex.exp (-((⟪z.1, ω⟫_ℝ : ℝ) : ℂ) * Complex.I) *
        Complex.exp (((⟪z.2, ω⟫_ℝ : ℝ) : ℂ) * Complex.I) =
        Complex.exp (-((⟪z.1 - z.2, ω⟫_ℝ : ℝ) : ℂ) * Complex.I) := by
    intro ω z
    rw [← Complex.exp_add]
    congr 1
    rw [inner_sub_left]
    push_cast
    ring
  have hcont : Continuous (Function.uncurry fun (ω : EuclideanSpace ℝ (Fin d))
      (z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) =>
      Complex.exp (-((⟪z.1, ω⟫_ℝ : ℝ) : ℂ) * Complex.I) *
        Complex.exp (((⟪z.2, ω⟫_ℝ : ℝ) : ℂ) * Complex.I)) := by
    fun_prop
  have hint : Integrable (Function.uncurry fun (ω : EuclideanSpace ℝ (Fin d))
      (z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) =>
      Complex.exp (-((⟪z.1, ω⟫_ℝ : ℝ) : ℂ) * Complex.I) *
        Complex.exp (((⟪z.2, ω⟫_ℝ : ℝ) : ℂ) * Complex.I)) (Λ.prod (μ.prod ν)) := by
    have h1 : Integrable (fun _ : EuclideanSpace ℝ (Fin d) ×
        (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) => (1 : ℂ))
        (Λ.prod (μ.prod ν)) :=
      integrable_const _
    refine h1.mono hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    obtain ⟨ω, z⟩ := p
    have e1 : ‖Complex.exp (-(↑⟪z.1, ω⟫_ℝ * Complex.I))‖ = 1 := by
      rw [show -(↑⟪z.1, ω⟫_ℝ * Complex.I) =
        ((-⟪z.1, ω⟫_ℝ : ℝ) : ℂ) * Complex.I by push_cast; ring]
      exact exp_norm _
    simp only [Function.uncurry_apply_pair, norm_mul, neg_mul, e1, exp_norm, mul_one,
      norm_one, le_refl]
  rw [integral_congr_ae (Filter.Eventually.of_forall fun ω => hprod ω),
    integral_integral_swap hint]
  have hcast : ((∫ z, kernelValue H z.1 z.2 ∂(μ.prod ν) : ℝ) : ℂ) =
      ∫ z, ((kernelValue H z.1 z.2 : ℝ) : ℂ) ∂(μ.prod ν) := integral_ofReal.symm
  rw [hcast]
  apply integral_congr_ae
  filter_upwards with z
  rw [integral_congr_ae (Filter.Eventually.of_forall fun ω => hexp ω z)]
  exact hk z.1 z.2

private lemma norm_meanEmbedding_sub_sq
    (Λ : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure Λ]
    (hk : ∀ x y : EuclideanSpace ℝ (Fin d), (kernelValue H x y : ℂ) =
      ∫ ω, Complex.exp (-((⟪x - y, ω⟫_ℝ : ℝ) : ℂ) * Complex.I) ∂Λ)
    (μ ν : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ‖meanEmbedding H μ - meanEmbedding H ν‖ ^ 2 =
      ∫ ω, ‖MeasureTheory.charFun μ (-ω) - MeasureTheory.charFun ν (-ω)‖ ^ 2 ∂Λ := by
  have hintμ := integrable_featureMap Λ hk μ
  have hintν := integrable_featureMap Λ hk ν
  have h1 := inner_meanEmbedding_eq_integral_prod hintμ hintμ
  have h2 := inner_meanEmbedding_eq_integral_prod hintμ hintν
  have h3 := inner_meanEmbedding_eq_integral_prod hintν hintν
  have hc1 := double_integral Λ hk μ μ
  have hc2 := double_integral Λ hk μ ν
  have hc3 := double_integral Λ hk ν ν
  have hcont : ∀ (ρ σ : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure ρ]
      [IsFiniteMeasure σ],
      Continuous fun ω : EuclideanSpace ℝ (Fin d) =>
        MeasureTheory.charFun ρ (-ω) * (starRingEnd ℂ) (MeasureTheory.charFun σ (-ω)) := by
    intro ρ σ _ _
    fun_prop
  have hinte : ∀ (ρ σ : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure ρ]
      [IsFiniteMeasure σ],
      Integrable (fun ω : EuclideanSpace ℝ (Fin d) =>
        MeasureTheory.charFun ρ (-ω) * (starRingEnd ℂ) (MeasureTheory.charFun σ (-ω))) Λ := by
    intro ρ σ _ _
    have hbound : Integrable (fun _ : EuclideanSpace ℝ (Fin d) =>
        ρ.real Set.univ * σ.real Set.univ) Λ := integrable_const _
    refine hbound.mono' (hcont ρ σ).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    have hb : ∀ (τ : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure τ] (ω),
        ‖MeasureTheory.charFun τ ω‖ ≤ τ.real Set.univ :=
      fun τ _ ω => MeasureTheory.norm_charFun_le ω
    calc ‖MeasureTheory.charFun ρ (-ω) * (starRingEnd ℂ) (MeasureTheory.charFun σ (-ω))‖
        = ‖MeasureTheory.charFun ρ (-ω)‖ * ‖MeasureTheory.charFun σ (-ω)‖ := by
          rw [norm_mul, Complex.norm_conj]
      _ ≤ ρ.real Set.univ * σ.real Set.univ :=
          mul_le_mul (hb ρ (-ω)) (hb σ (-ω)) (norm_nonneg _)
            (MeasureTheory.measureReal_nonneg)
  have hcomplex : ((‖meanEmbedding H μ - meanEmbedding H ν‖ ^ 2 : ℝ) : ℂ) =
      ∫ ω, (MeasureTheory.charFun μ (-ω) - MeasureTheory.charFun ν (-ω)) *
        (starRingEnd ℂ) (MeasureTheory.charFun μ (-ω) - MeasureTheory.charFun ν (-ω)) ∂Λ := by
    have e : ‖meanEmbedding H μ - meanEmbedding H ν‖ ^ 2 =
        ⟪meanEmbedding H μ, meanEmbedding H μ⟫_ℝ -
          2 * ⟪meanEmbedding H μ, meanEmbedding H ν⟫_ℝ +
          ⟪meanEmbedding H ν, meanEmbedding H ν⟫_ℝ := by
      rw [norm_sub_sq_real, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    calc ((‖meanEmbedding H μ - meanEmbedding H ν‖ ^ 2 : ℝ) : ℂ)
        = ((⟪meanEmbedding H μ, meanEmbedding H μ⟫_ℝ : ℝ) : ℂ) -
            2 * ((⟪meanEmbedding H μ, meanEmbedding H ν⟫_ℝ : ℝ) : ℂ) +
            ((⟪meanEmbedding H ν, meanEmbedding H ν⟫_ℝ : ℝ) : ℂ) := by
          rw [e]; push_cast; ring
      _ = (∫ ω, MeasureTheory.charFun μ (-ω) *
            (starRingEnd ℂ) (MeasureTheory.charFun μ (-ω)) ∂Λ) -
            2 * (∫ ω, MeasureTheory.charFun μ (-ω) *
              (starRingEnd ℂ) (MeasureTheory.charFun ν (-ω)) ∂Λ) +
            (∫ ω, MeasureTheory.charFun ν (-ω) *
              (starRingEnd ℂ) (MeasureTheory.charFun ν (-ω)) ∂Λ) := by
          rw [← h1] at hc1; rw [← h2] at hc2; rw [← h3] at hc3
          rw [hc1, hc2, hc3]
      _ = ∫ ω, (MeasureTheory.charFun μ (-ω) *
            (starRingEnd ℂ) (MeasureTheory.charFun μ (-ω)) -
            MeasureTheory.charFun μ (-ω) *
              (starRingEnd ℂ) (MeasureTheory.charFun ν (-ω)) -
            MeasureTheory.charFun ν (-ω) *
              (starRingEnd ℂ) (MeasureTheory.charFun μ (-ω)) +
            MeasureTheory.charFun ν (-ω) *
              (starRingEnd ℂ) (MeasureTheory.charFun ν (-ω))) ∂Λ := by
          have hBA : (∫ ω, MeasureTheory.charFun ν (-ω) *
              (starRingEnd ℂ) (MeasureTheory.charFun μ (-ω)) ∂Λ) =
              ∫ ω, MeasureTheory.charFun μ (-ω) *
                (starRingEnd ℂ) (MeasureTheory.charFun ν (-ω)) ∂Λ := by
            have hstar : (∫ ω, MeasureTheory.charFun ν (-ω) *
                (starRingEnd ℂ) (MeasureTheory.charFun μ (-ω)) ∂Λ) =
                (starRingEnd ℂ) (∫ ω, MeasureTheory.charFun μ (-ω) *
                  (starRingEnd ℂ) (MeasureTheory.charFun ν (-ω)) ∂Λ) := by
              rw [← integral_conj]
              apply integral_congr_ae
              filter_upwards with ω
              simp only [map_mul, starRingEnd_apply, star_star]
              ring
            rw [hstar, ← hc2]
            simp
          have hf1 : Integrable (fun ω : EuclideanSpace ℝ (Fin d) =>
              MeasureTheory.charFun μ (-ω) *
                (starRingEnd ℂ) (MeasureTheory.charFun μ (-ω)) -
              MeasureTheory.charFun μ (-ω) *
                (starRingEnd ℂ) (MeasureTheory.charFun ν (-ω))) Λ :=
            (hinte μ μ).sub (hinte μ ν)
          have hf2 : Integrable (fun ω : EuclideanSpace ℝ (Fin d) =>
              MeasureTheory.charFun μ (-ω) *
                (starRingEnd ℂ) (MeasureTheory.charFun μ (-ω)) -
              MeasureTheory.charFun μ (-ω) *
                (starRingEnd ℂ) (MeasureTheory.charFun ν (-ω)) -
              MeasureTheory.charFun ν (-ω) *
                (starRingEnd ℂ) (MeasureTheory.charFun μ (-ω))) Λ :=
            hf1.sub (hinte ν μ)
          have hcomb : (∫ ω, MeasureTheory.charFun μ (-ω) *
                (starRingEnd ℂ) (MeasureTheory.charFun μ (-ω)) ∂Λ) -
              (∫ ω, MeasureTheory.charFun μ (-ω) *
                (starRingEnd ℂ) (MeasureTheory.charFun ν (-ω)) ∂Λ) -
              (∫ ω, MeasureTheory.charFun ν (-ω) *
                (starRingEnd ℂ) (MeasureTheory.charFun μ (-ω)) ∂Λ) +
              (∫ ω, MeasureTheory.charFun ν (-ω) *
                (starRingEnd ℂ) (MeasureTheory.charFun ν (-ω)) ∂Λ) =
              ∫ ω, (MeasureTheory.charFun μ (-ω) *
                (starRingEnd ℂ) (MeasureTheory.charFun μ (-ω)) -
                MeasureTheory.charFun μ (-ω) *
                  (starRingEnd ℂ) (MeasureTheory.charFun ν (-ω)) -
                MeasureTheory.charFun ν (-ω) *
                  (starRingEnd ℂ) (MeasureTheory.charFun μ (-ω)) +
                MeasureTheory.charFun ν (-ω) *
                  (starRingEnd ℂ) (MeasureTheory.charFun ν (-ω))) ∂Λ := by
            rw [← integral_sub (hinte μ μ) (hinte μ ν),
              ← integral_sub hf1 (hinte ν μ),
              ← integral_add hf2 (hinte ν ν)]
          rw [← hcomb, hBA]
          ring
      _ = ∫ ω, (MeasureTheory.charFun μ (-ω) - MeasureTheory.charFun ν (-ω)) *
            (starRingEnd ℂ) (MeasureTheory.charFun μ (-ω) -
              MeasureTheory.charFun ν (-ω)) ∂Λ := by
          apply integral_congr_ae
          filter_upwards with ω
          simp only [map_sub]
          ring
  have hD : ∀ ω : EuclideanSpace ℝ (Fin d),
      (MeasureTheory.charFun μ (-ω) - MeasureTheory.charFun ν (-ω)) *
        (starRingEnd ℂ) (MeasureTheory.charFun μ (-ω) - MeasureTheory.charFun ν (-ω)) =
        ((‖MeasureTheory.charFun μ (-ω) - MeasureTheory.charFun ν (-ω)‖ ^ 2 : ℝ) : ℂ) := by
    intro ω
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [integral_congr_ae (Filter.Eventually.of_forall fun ω => hD ω)] at hcomplex
  have hcast : (∫ ω, ((‖MeasureTheory.charFun μ (-ω) -
      MeasureTheory.charFun ν (-ω)‖ ^ 2 : ℝ) : ℂ) ∂Λ) =
      ((∫ ω, ‖MeasureTheory.charFun μ (-ω) - MeasureTheory.charFun ν (-ω)‖ ^ 2 ∂Λ : ℝ) : ℂ) :=
    integral_ofReal
  rw [hcast] at hcomplex
  exact Complex.ofReal_injective hcomplex

private lemma charFun_eq_of_support_eq_univ
    (Λ : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure Λ]
    (hk : ∀ x y : EuclideanSpace ℝ (Fin d), (kernelValue H x y : ℂ) =
      ∫ ω, Complex.exp (-((⟪x - y, ω⟫_ℝ : ℝ) : ℂ) * Complex.I) ∂Λ)
    (hsupp : Λ.support = Set.univ)
    (μ ν : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : meanEmbedding H μ = meanEmbedding H ν) :
    MeasureTheory.charFun μ = MeasureTheory.charFun ν := by
  have hcontD : Continuous fun ω : EuclideanSpace ℝ (Fin d) =>
      MeasureTheory.charFun μ (-ω) - MeasureTheory.charFun ν (-ω) := by
    exact (MeasureTheory.continuous_charFun.comp continuous_neg).sub
      (MeasureTheory.continuous_charFun.comp continuous_neg)
  have hcontf : Continuous fun ω : EuclideanSpace ℝ (Fin d) =>
      ‖MeasureTheory.charFun μ (-ω) - MeasureTheory.charFun ν (-ω)‖ ^ 2 :=
    hcontD.norm.pow 2
  have hfi : Integrable (fun ω : EuclideanSpace ℝ (Fin d) =>
      ‖MeasureTheory.charFun μ (-ω) - MeasureTheory.charFun ν (-ω)‖ ^ 2) Λ := by
    have hbound : Integrable (fun _ : EuclideanSpace ℝ (Fin d) => (4 : ℝ)) Λ :=
      integrable_const _
    refine hbound.mono' hcontf.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    have hb : ∀ (τ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure τ] (ω),
        ‖MeasureTheory.charFun τ ω‖ ≤ 1 :=
      fun τ _ ω => MeasureTheory.norm_charFun_le_one ω
    have h1 : ‖MeasureTheory.charFun μ (-ω) - MeasureTheory.charFun ν (-ω)‖ ≤ 2 := by
      calc ‖MeasureTheory.charFun μ (-ω) - MeasureTheory.charFun ν (-ω)‖
          ≤ ‖MeasureTheory.charFun μ (-ω)‖ + ‖MeasureTheory.charFun ν (-ω)‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := add_le_add (hb μ _) (hb ν _)
        _ = 2 := by norm_num
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_nonneg (‖MeasureTheory.charFun μ (-ω) - MeasureTheory.charFun ν (-ω)‖), h1,
      norm_nonneg (MeasureTheory.charFun μ (-ω) - MeasureTheory.charFun ν (-ω))]
  have hzero : (∫ ω, ‖MeasureTheory.charFun μ (-ω) - MeasureTheory.charFun ν (-ω)‖ ^ 2 ∂Λ) = 0 := by
    rw [← norm_meanEmbedding_sub_sq Λ hk μ ν, h, sub_self]
    simp
  have hsupp0 : Λ (Function.support fun ω : EuclideanSpace ℝ (Fin d) =>
      ‖MeasureTheory.charFun μ (-ω) - MeasureTheory.charFun ν (-ω)‖ ^ 2) = 0 := by
    by_contra hne
    have hpos : 0 < Λ (Function.support fun ω : EuclideanSpace ℝ (Fin d) =>
        ‖MeasureTheory.charFun μ (-ω) - MeasureTheory.charFun ν (-ω)‖ ^ 2) := by
      rw [pos_iff_ne_zero]
      exact hne
    have hlt := (MeasureTheory.integral_pos_iff_support_of_nonneg
      (fun ω => sq_nonneg _) hfi).mpr hpos
    rw [hzero] at hlt
    exact lt_irrefl _ hlt
  ext t
  rw [← neg_neg t]
  have hD : MeasureTheory.charFun μ (-(-t)) - MeasureTheory.charFun ν (-(-t)) = 0 := by
    by_contra hD
    have hmem : (-t) ∈ Function.support fun ω : EuclideanSpace ℝ (Fin d) =>
        ‖MeasureTheory.charFun μ (-ω) - MeasureTheory.charFun ν (-ω)‖ ^ 2 := by
      simp only [Function.mem_support, ne_eq]
      exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hD)
    have hopen : IsOpen (Function.support fun ω : EuclideanSpace ℝ (Fin d) =>
        ‖MeasureTheory.charFun μ (-ω) - MeasureTheory.charFun ν (-ω)‖ ^ 2) := by
      have heq : (Function.support fun ω : EuclideanSpace ℝ (Fin d) =>
          ‖MeasureTheory.charFun μ (-ω) - MeasureTheory.charFun ν (-ω)‖ ^ 2) =
          (fun ω : EuclideanSpace ℝ (Fin d) =>
            ‖MeasureTheory.charFun μ (-ω) - MeasureTheory.charFun ν (-ω)‖ ^ 2) ⁻¹' {0}ᶜ := by
        ext ω
        simp [Function.mem_support]
      rw [heq]
      exact isOpen_compl_singleton.preimage hcontf
    have hmemsupp : (-t) ∈ Λ.support := by rw [hsupp]; trivial
    have hpos : 0 < Λ (Function.support fun ω : EuclideanSpace ℝ (Fin d) =>
        ‖MeasureTheory.charFun μ (-ω) - MeasureTheory.charFun ν (-ω)‖ ^ 2) :=
      (MeasureTheory.Measure.mem_support_iff_forall (-t)).mp hmemsupp _ (hopen.mem_nhds hmem)
    rw [hsupp0] at hpos
    exact lt_irrefl _ hpos
  rw [neg_neg] at hD
  simpa only [neg_neg] using sub_eq_zero.mp hD

private lemma charFun_real
    (Λ : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure Λ]
    (hk : ∀ x y : EuclideanSpace ℝ (Fin d), (kernelValue H x y : ℂ) =
      ∫ ω, Complex.exp (-((⟪x - y, ω⟫_ℝ : ℝ) : ℂ) * Complex.I) ∂Λ)
    (t : EuclideanSpace ℝ (Fin d)) :
    MeasureTheory.charFun Λ t = ((kernelValue H 0 t : ℝ) : ℂ) := by
  have h := kernelValue_eq_charFun Λ hk 0 t
  simpa using h.symm

private lemma measure_map_neg_eq
    (Λ : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure Λ]
    (hk : ∀ x y : EuclideanSpace ℝ (Fin d), (kernelValue H x y : ℂ) =
      ∫ ω, Complex.exp (-((⟪x - y, ω⟫_ℝ : ℝ) : ℂ) * Complex.I) ∂Λ) :
    Λ.map Neg.neg = Λ := by
  have hfin : IsFiniteMeasure (Λ.map Neg.neg) := by
    refine ⟨?_⟩
    rw [MeasureTheory.Measure.map_apply measurable_neg MeasurableSet.univ]
    simp
  apply MeasureTheory.Measure.ext_of_charFun
  funext t
  rw [MeasureTheory.charFun_apply, MeasureTheory.charFun_apply,
    MeasureTheory.integral_map measurable_neg.aemeasurable
      (by fun_prop : AEStronglyMeasurable (fun x : EuclideanSpace ℝ (Fin d) =>
        Complex.exp (⟪x, t⟫_ℝ * Complex.I)) (Λ.map Neg.neg))]
  have hconj : (∫ x : EuclideanSpace ℝ (Fin d),
        Complex.exp (⟪-x, t⟫_ℝ * Complex.I) ∂Λ) =
      (starRingEnd ℂ) (∫ x : EuclideanSpace ℝ (Fin d),
        Complex.exp (⟪x, t⟫_ℝ * Complex.I) ∂Λ) := by
    rw [← integral_conj]
    apply integral_congr_ae
    filter_upwards with x
    rw [inner_neg_left, ← Complex.exp_conj]
    congr 1
    simp
  rw [hconj, ← MeasureTheory.charFun_apply, charFun_real Λ hk t]
  simp


private lemma neg_mem_support
    (Λ : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure Λ]
    (hΛ : Λ.map Neg.neg = Λ) (x : EuclideanSpace ℝ (Fin d)) :
    -x ∈ Λ.support ↔ x ∈ Λ.support := by
  have hball : ∀ y : EuclideanSpace ℝ (Fin d),
      y ∈ Λ.support ↔ ∀ ε > 0, 0 < Λ (Metric.ball y ε) :=
    fun y => Metric.nhds_basis_ball.mem_measureSupport
  have hpre : ∀ (ε : ℝ),
      Neg.neg ⁻¹' Metric.ball (-x) ε = Metric.ball x ε := by
    intro ε
    ext y
    simp [Metric.mem_ball]
  have hmeas : ∀ (ε : ℝ), Λ (Metric.ball (-x) ε) = Λ (Metric.ball x ε) := by
    intro ε
    have h : (Λ.map Neg.neg) (Metric.ball (-x) ε) =
        Λ (Neg.neg ⁻¹' Metric.ball (-x) ε) :=
      MeasureTheory.Measure.map_apply measurable_neg
        (Metric.isOpen_ball (x := -x) (ε := ε)).measurableSet
    rw [hpre] at h
    rw [hΛ] at h
    exact h
  rw [hball, hball]
  constructor
  · intro h ε hε
    rw [← hmeas ε]
    exact h ε hε
  · intro h ε hε
    rw [hmeas ε]
    exact h ε hε

private lemma exists_bump_point
    (Λ : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure Λ]
    (hΛ : Λ.map Neg.neg = Λ) (hd : 0 < d)
    (hsupp : Λ.support ≠ Set.univ) :
    ∃ ω₁ : EuclideanSpace ℝ (Fin d), ω₁ ≠ 0 ∧ ω₁ ∉ Λ.support ∧
      ∃ r : ℝ, 0 < r ∧ r < ‖ω₁‖ / 2 ∧
        Metric.closedBall ω₁ r ⊆ Λ.supportᶜ ∧
        Metric.closedBall (-ω₁) r ⊆ Λ.supportᶜ := by
  obtain ⟨ω₀, hω₀⟩ : ∃ ω₀, ω₀ ∉ Λ.support := by
    by_contra hcon
    apply hsupp
    apply Set.eq_univ_of_forall
    intro ω₀
    by_contra hmem
    exact hcon ⟨ω₀, hmem⟩
  have hU : IsOpen Λ.supportᶜ := MeasureTheory.Measure.isClosed_support.isOpen_compl
  obtain ⟨ω₁, hω₁, hω₁0⟩ : ∃ ω₁ ∈ Λ.supportᶜ, ω₁ ≠ 0 := by
    by_cases h0 : ω₀ = 0
    · subst h0
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU 0 hω₀
      refine ⟨(r / 2) • EuclideanSpace.single ⟨0, hd⟩ (1 : ℝ), ?_, ?_⟩
      · apply hball
        rw [Metric.mem_ball, dist_zero_right]
        have hnorm : ‖((r / 2) • EuclideanSpace.single ⟨0, hd⟩ (1 : ℝ) :
            EuclideanSpace ℝ (Fin d))‖ = r / 2 := by
          rw [norm_smul]
          simp [Real.norm_eq_abs, abs_of_pos hr]
        rw [hnorm]
        linarith
      · intro hcon
        have hnorm : ‖((r / 2) • EuclideanSpace.single ⟨0, hd⟩ (1 : ℝ) :
            EuclideanSpace ℝ (Fin d))‖ = r / 2 := by
          rw [norm_smul]
          simp [Real.norm_eq_abs, abs_of_pos hr]
        rw [hcon, norm_zero] at hnorm
        linarith
    · exact ⟨ω₀, hω₀, h0⟩
  have hneg : -ω₁ ∈ Λ.supportᶜ := by
    rw [Set.mem_compl_iff]
    intro hmem
    exact hω₁ ((neg_mem_support Λ hΛ ω₁).mp hmem)
  obtain ⟨r₁, hr₁, hb₁⟩ := Metric.isOpen_iff.mp hU ω₁ hω₁
  obtain ⟨r₂, hr₂, hb₂⟩ := Metric.isOpen_iff.mp hU (-ω₁) hneg
  refine ⟨ω₁, hω₁0, hω₁, (min (min r₁ r₂ / 2) (‖ω₁‖ / 4)), ?_, ?_, ?_, ?_⟩
  · have h1 : (0:ℝ) < min r₁ r₂ / 2 := by positivity
    have h2 : (0:ℝ) < ‖ω₁‖ / 4 := by positivity
    exact lt_min h1 h2
  · have h1 : min (min r₁ r₂ / 2) (‖ω₁‖ / 4) ≤ ‖ω₁‖ / 4 := min_le_right _ _
    have h3 : (0:ℝ) < ‖ω₁‖ := norm_pos_iff.mpr hω₁0
    linarith
  · have hr1 : min (min r₁ r₂ / 2) (‖ω₁‖ / 4) < r₁ := by
      have ha : min (min r₁ r₂ / 2) (‖ω₁‖ / 4) ≤ min r₁ r₂ / 2 := min_le_left _ _
      have hb : min r₁ r₂ ≤ r₁ := min_le_left _ _
      linarith
    intro y hy
    apply hb₁
    rw [Metric.mem_ball]
    exact lt_of_le_of_lt (Metric.mem_closedBall.mp hy) hr1
  · have hr2 : min (min r₁ r₂ / 2) (‖ω₁‖ / 4) < r₂ := by
      have ha : min (min r₁ r₂ / 2) (‖ω₁‖ / 4) ≤ min r₁ r₂ / 2 := min_le_left _ _
      have hb : min r₁ r₂ ≤ r₂ := min_le_right _ _
      linarith
    intro y hy
    apply hb₂
    rw [Metric.mem_ball]
    exact lt_of_le_of_lt (Metric.mem_closedBall.mp hy) hr2


private lemma exists_bump_theta
    (Λ : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure Λ]
    (ω₁ : EuclideanSpace ℝ (Fin d)) (hω₁0 : ω₁ ≠ 0)
    (r : ℝ) (hr : 0 < r) (hr2 : r < ‖ω₁‖ / 2)
    (hsub1 : Metric.closedBall ω₁ r ⊆ Λ.supportᶜ)
    (hsub2 : Metric.closedBall (-ω₁) r ⊆ Λ.supportᶜ) :
    ∃ θ : EuclideanSpace ℝ (Fin d) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) θ ∧ HasCompactSupport θ ∧ (∀ ω, θ (-ω) = θ ω) ∧
      (∀ ω, 0 ≤ θ ω) ∧ θ ω₁ ≠ 0 ∧ θ 0 = 0 ∧ (∀ ω ∈ Λ.support, θ ω = 0) := by
  obtain ⟨b, hb_tsupp, hb_cs, hb_smooth, hb_range, hb_one⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) (s := Metric.ball ω₁ r) (x := ω₁)
      (Metric.ball_mem_nhds ω₁ hr)
  have hb_nonneg : ∀ ω, 0 ≤ b ω := fun ω => (hb_range ⟨ω, rfl⟩).1
  have hb_le : ∀ ω, b ω ≤ 1 := fun ω => (hb_range ⟨ω, rfl⟩).2
  have hball_neg : ∀ y : EuclideanSpace ℝ (Fin d),
      -y ∈ Metric.ball ω₁ r → y ∈ Metric.closedBall (-ω₁) r := by
    intro y hy
    have hdist : dist y (-ω₁) = dist (-y) ω₁ := by
      rw [dist_eq_norm, dist_eq_norm]
      rw [show (-y - ω₁) = -(y + ω₁) by abel, norm_neg]
      simp [sub_neg_eq_add]
    rw [Metric.mem_closedBall, hdist]
    exact le_of_lt (Metric.mem_ball.mp hy)
  have hball_neg_ball : ∀ y : EuclideanSpace ℝ (Fin d),
      -y ∈ Metric.ball ω₁ r → y ∈ Metric.ball (-ω₁) r := by
    intro y hy
    have hdist : dist y (-ω₁) = dist (-y) ω₁ := by
      rw [dist_eq_norm, dist_eq_norm]
      rw [show (-y - ω₁) = -(y + ω₁) by abel, norm_neg]
      simp [sub_neg_eq_add]
    rw [Metric.mem_ball, hdist]
    exact Metric.mem_ball.mp hy
  have hsupp_ball : ∀ ω : EuclideanSpace ℝ (Fin d),
      (fun ω => b ω + b (-ω)) ω ≠ 0 →
        ω ∈ Metric.ball ω₁ r ∨ ω ∈ Metric.ball (-ω₁) r := by
    intro ω hω
    simp only [ne_eq] at hω
    by_cases hb1 : b ω = 0
    · have hne : b (-ω) ≠ 0 := by
        intro hcon
        exact hω (by simp [hb1, hcon])
      have hmem : -ω ∈ Metric.ball ω₁ r :=
        hb_tsupp (subset_closure hne)
      exact Or.inr (hball_neg_ball ω hmem)
    · have hmem : ω ∈ Metric.ball ω₁ r :=
        hb_tsupp (subset_closure hb1)
      exact Or.inl hmem
  have hsupp_closed : Function.support (fun ω => b ω + b (-ω)) ⊆
      Metric.closedBall ω₁ r ∪ Metric.closedBall (-ω₁) r := by
    intro ω hω
    rcases hsupp_ball ω hω with hmem | hmem
    · exact Or.inl (Metric.ball_subset_closedBall hmem)
    · exact Or.inr (Metric.ball_subset_closedBall hmem)
  refine ⟨fun ω => b ω + b (-ω), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hb_smooth.add (hb_smooth.comp (by fun_prop))
  · exact HasCompactSupport.of_support_subset_isCompact
      ((isCompact_closedBall ..).union (isCompact_closedBall ..)) hsupp_closed
  · intro ω
    simp [add_comm]
  · intro ω
    exact add_nonneg (hb_nonneg ω) (hb_nonneg (-ω))
  · have h1 : b ω₁ = 1 := hb_one
    have h2 : 0 ≤ b (-ω₁) := hb_nonneg _
    have : b ω₁ + b (-ω₁) ≠ 0 := by
      rw [h1]
      intro hcon
      have : b (-ω₁) = -1 := by linarith
      linarith
    exact this
  · by_contra hcon
    rcases hsupp_ball 0 hcon with hmem | hmem
    · rw [Metric.mem_ball, dist_zero_left] at hmem
      have h3 : (0:ℝ) < ‖ω₁‖ := norm_pos_iff.mpr hω₁0
      linarith
    · rw [Metric.mem_ball, dist_zero_left, norm_neg] at hmem
      have h3 : (0:ℝ) < ‖ω₁‖ := norm_pos_iff.mpr hω₁0
      linarith
  · intro ω hω
    by_contra hcon
    rcases hsupp_closed hcon with hmem | hmem
    · exact (hsub1 hmem) hω
    · exact (hsub2 hmem) hω

private lemma integral_neg_of_integrable {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℂ) :
    ∫ x, f (-x) ∂(volume : Measure E) = ∫ x, f x ∂(volume : Measure E) := by
  have hmp : MeasurePreserving (fun x : E => -x) (volume : Measure E) (volume : Measure E) :=
    LinearIsometryEquiv.measurePreserving (LinearIsometryEquiv.neg ℝ (E := E))
  exact hmp.integral_comp measurableEmbedding_neg f

private lemma schwartz_ratio_bound {d : ℕ}
    (S : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ) :
    ∃ R : ℝ, ∀ x : EuclideanSpace ℝ (Fin d),
      |(2 * Real.pi) ^ d * (S x).re| ≤
        R * ∏ i : Fin d, ProbabilityTheory.cauchyPDFReal 0 1 (x i) := by
  obtain ⟨C0, _, hC0⟩ := S.decay 0 0
  obtain ⟨C1, _, hC1⟩ := S.decay (2 * (d + 1)) 0
  simp only [pow_zero, one_mul, norm_iteratedFDeriv_zero] at hC0 hC1
  set M := max C0 C1 with hMdef
  have hM0 : 0 ≤ M := le_max_of_le_left (by positivity)
  have hS0 : ∀ x, ‖S x‖ ≤ M := fun x => (hC0 x).trans (le_max_left _ _)
  have hSk : ∀ x, ‖x‖ ^ (2 * (d + 1)) * ‖S x‖ ≤ M :=
    fun x => (hC1 x).trans (le_max_right _ _)
  have hkey : ∀ x : EuclideanSpace ℝ (Fin d),
      ‖S x‖ * (1 + ‖x‖ ^ 2) ^ (d + 1) ≤ 2 ^ (d + 1) * M := by
    intro x
    rcases le_total ‖x‖ 1 with hx | hx
    · have h2 : (1 + ‖x‖ ^ 2) ^ (d + 1) ≤ 2 ^ (d + 1) := by
        apply pow_le_pow_left₀ (by positivity)
        nlinarith [sq_nonneg ‖x‖, hx, norm_nonneg x]
      calc ‖S x‖ * (1 + ‖x‖ ^ 2) ^ (d + 1)
          ≤ M * 2 ^ (d + 1) :=
            mul_le_mul (hS0 x) h2 (by positivity) (by positivity)
        _ = 2 ^ (d + 1) * M := by ring
    · have hsq : (1 : ℝ) ≤ ‖x‖ ^ 2 := by
        calc (1 : ℝ) = 1 ^ 2 := by simp
          _ ≤ ‖x‖ ^ 2 := pow_le_pow_left₀ (by norm_num) hx 2
      have h3 : (1 + ‖x‖ ^ 2) ^ (d + 1) ≤ 2 ^ (d + 1) * ‖x‖ ^ (2 * (d + 1)) := by
        have h4 : (1 + ‖x‖ ^ 2) ≤ 2 * ‖x‖ ^ 2 := by linarith
        calc (1 + ‖x‖ ^ 2) ^ (d + 1) ≤ (2 * ‖x‖ ^ 2) ^ (d + 1) :=
              pow_le_pow_left₀ (by positivity) h4 _
          _ = 2 ^ (d + 1) * (‖x‖ ^ 2) ^ (d + 1) := by rw [mul_pow]
          _ = 2 ^ (d + 1) * ‖x‖ ^ (2 * (d + 1)) := by rw [← pow_mul]
      calc ‖S x‖ * (1 + ‖x‖ ^ 2) ^ (d + 1)
          ≤ ‖S x‖ * (2 ^ (d + 1) * ‖x‖ ^ (2 * (d + 1))) :=
            mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
        _ = 2 ^ (d + 1) * (‖x‖ ^ (2 * (d + 1)) * ‖S x‖) := by ring
        _ ≤ 2 ^ (d + 1) * M :=
            mul_le_mul_of_nonneg_left (hSk x) (by positivity)
  have hcoord : ∀ (x : EuclideanSpace ℝ (Fin d)) (i : Fin d),
      (x i) ^ 2 ≤ ‖x‖ ^ 2 := by
    intro x i
    have hnorm : ‖x‖ ^ 2 = ∑ j : Fin d, (x j) ^ 2 := by
      rw [EuclideanSpace.norm_eq]
      rw [Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)]
      apply Finset.sum_congr rfl
      intro j _
      rw [Real.norm_eq_abs, sq_abs]
    rw [hnorm]
    exact Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
  have hprod : ∀ x : EuclideanSpace ℝ (Fin d),
      ∏ i : Fin d, (1 + (x i) ^ 2) ≤ (1 + ‖x‖ ^ 2) ^ d := by
    intro x
    have hgen : ∀ s : Finset (Fin d),
        ∏ i ∈ s, (1 + (x i) ^ 2) ≤ (1 + ‖x‖ ^ 2) ^ s.card := by
      intro s
      induction s using Finset.induction with
      | empty => simp
      | insert a t hat ih =>
        rw [Finset.prod_insert hat, Finset.card_insert_of_notMem hat]
        calc (1 + (x a) ^ 2) * ∏ i ∈ t, (1 + (x i) ^ 2)
            ≤ (1 + ‖x‖ ^ 2) * (1 + ‖x‖ ^ 2) ^ t.card :=
              mul_le_mul (by linarith [hcoord x a]) ih (by positivity) (by positivity)
          _ = (1 + ‖x‖ ^ 2) ^ (t.card + 1) := by
              rw [pow_succ]; ring
    have h := hgen Finset.univ
    rw [Finset.card_univ, Fintype.card_fin] at h
    exact h
  refine ⟨(2 * Real.pi) ^ d * 2 ^ (d + 1) * M * Real.pi ^ d, fun x => ?_⟩
  have hgform : (∏ i : Fin d, ProbabilityTheory.cauchyPDFReal 0 1 (x i)) =
      Real.pi⁻¹ ^ d * (∏ i : Fin d, (1 + (x i) ^ 2))⁻¹ := by
    calc ∏ i : Fin d, ProbabilityTheory.cauchyPDFReal 0 1 (x i)
        = ∏ i : Fin d, (Real.pi⁻¹ * (1 + (x i) ^ 2)⁻¹) := by
          apply Finset.prod_congr rfl
          intro i _
          rw [ProbabilityTheory.cauchyPDFReal_def]
          simp only [sub_zero, NNReal.coe_one, one_pow, mul_one]
          rw [add_comm]
      _ = Real.pi⁻¹ ^ d * ∏ i : Fin d, (1 + (x i) ^ 2)⁻¹ := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
            Fintype.card_fin]
      _ = Real.pi⁻¹ ^ d * (∏ i : Fin d, (1 + (x i) ^ 2))⁻¹ := by
          rw [Finset.prod_inv_distrib]
  have hgpos : 0 < ∏ i : Fin d, (1 + (x i) ^ 2) := by
    apply Finset.prod_pos
    intro i _
    positivity
  have hPpos : (0:ℝ) < (1 + ‖x‖ ^ 2) ^ d := by positivity
  have hge : ((1 + ‖x‖ ^ 2) ^ d)⁻¹ ≤ (∏ i : Fin d, (1 + (x i) ^ 2))⁻¹ :=
    (inv_le_inv₀ hPpos hgpos).mpr (hprod x)
  have hSbound : ‖S x‖ ≤ 2 ^ (d + 1) * M * ((1 + ‖x‖ ^ 2) ^ (d + 1))⁻¹ := by
    have hpos1 : (0:ℝ) < (1 + ‖x‖ ^ 2) ^ (d + 1) := by positivity
    rw [le_mul_inv_iff₀ hpos1]
    exact hkey x
  have hfac : ((1 + ‖x‖ ^ 2) ^ d)⁻¹ * ((1 + ‖x‖ ^ 2))⁻¹ ≤
      (∏ i : Fin d, (1 + (x i) ^ 2))⁻¹ * 1 := by
    exact mul_le_mul hge (inv_le_one_of_one_le₀ (le_add_of_nonneg_right (sq_nonneg ‖x‖)))
      (by positivity) (by positivity)
  have hpi : Real.pi ^ d * Real.pi⁻¹ ^ d = 1 := by
    rw [inv_pow, mul_inv_cancel₀ (by positivity)]
  calc |(2 * Real.pi) ^ d * (S x).re|
      = (2 * Real.pi) ^ d * |(S x).re| := by
        rw [abs_mul, abs_of_pos (by positivity)]
    _ ≤ (2 * Real.pi) ^ d * ‖S x‖ := by
        gcongr
        exact Complex.abs_re_le_norm _
    _ ≤ (2 * Real.pi) ^ d * (2 ^ (d + 1) * M * ((1 + ‖x‖ ^ 2) ^ (d + 1))⁻¹) := by
        gcongr
    _ = (2 * Real.pi) ^ d * 2 ^ (d + 1) * M *
        (((1 + ‖x‖ ^ 2) ^ d)⁻¹ * ((1 + ‖x‖ ^ 2))⁻¹) := by
        rw [pow_succ]
        field_simp
        ring
    _ ≤ (2 * Real.pi) ^ d * 2 ^ (d + 1) * M *
        ((∏ i : Fin d, (1 + (x i) ^ 2))⁻¹ * 1) :=
        mul_le_mul_of_nonneg_left hfac (by positivity)
    _ = (2 * Real.pi) ^ d * 2 ^ (d + 1) * M * Real.pi ^ d *
        (Real.pi⁻¹ ^ d * (∏ i : Fin d, (1 + (x i) ^ 2))⁻¹) := by
        rw [mul_one]
        calc (2 * Real.pi) ^ d * 2 ^ (d + 1) * M * (∏ i : Fin d, (1 + (x i) ^ 2))⁻¹
            = (2 * Real.pi) ^ d * 2 ^ (d + 1) * M * ((Real.pi ^ d * Real.pi⁻¹ ^ d) *
              (∏ i : Fin d, (1 + (x i) ^ 2))⁻¹) := by rw [hpi, one_mul]
          _ = (2 * Real.pi) ^ d * 2 ^ (d + 1) * M * Real.pi ^ d *
              (Real.pi⁻¹ ^ d * (∏ i : Fin d, (1 + (x i) ^ 2))⁻¹) := by ring
    _ = (2 * Real.pi) ^ d * 2 ^ (d + 1) * M * Real.pi ^ d *
        ∏ i : Fin d, ProbabilityTheory.cauchyPDFReal 0 1 (x i) := by
        rw [hgform]

private lemma exists_perturbation
    (θ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hθdiff : ContDiff ℝ (⊤ : ℕ∞) θ) (hθcs : HasCompactSupport θ)
    (hθeven : ∀ ω, θ (-ω) = θ ω) (hθ0 : θ 0 = 0)
    (ω₁ : EuclideanSpace ℝ (Fin d)) (hθω₁ : θ ω₁ ≠ 0) :
    ∃ s : EuclideanSpace ℝ (Fin d) → ℝ,
      Continuous s ∧ Integrable s (volume : Measure (EuclideanSpace ℝ (Fin d))) ∧
      (∀ ξ : EuclideanSpace ℝ (Fin d),
        ∫ x, ((s x : ℝ) : ℂ) * Complex.exp (((⟪x, ξ⟫_ℝ : ℝ) : ℂ) * Complex.I)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin d))) =
          (((2 * Real.pi) ^ d * θ ξ : ℝ) : ℂ)) ∧
      (∃ x, s x ≠ 0) ∧ (∫ x, s x ∂(volume : Measure (EuclideanSpace ℝ (Fin d)))) = 0 ∧
      (∃ R : ℝ, ∀ x, |s x| ≤
        R * ∏ i : Fin d, ProbabilityTheory.cauchyPDFReal 0 1 (x i)) := by
  classical
  have h2pi : (2 : ℝ) * Real.pi ≠ 0 := by positivity
  have hθ2diff : ContDiff ℝ (⊤ : ℕ∞)
      (fun ω : EuclideanSpace ℝ (Fin d) => θ ((2 * Real.pi) • ω)) :=
    hθdiff.comp (by fun_prop)
  have hθ2cs : HasCompactSupport (fun ω : EuclideanSpace ℝ (Fin d) =>
      θ ((2 * Real.pi) • ω)) := hθcs.comp_smul h2pi
  have hΘCdiff : ContDiff ℝ (⊤ : ℕ∞)
      (fun ω : EuclideanSpace ℝ (Fin d) => ((θ ((2 * Real.pi) • ω) : ℝ) : ℂ)) :=
    hθ2diff.continuousLinearMap_comp (RCLike.ofRealCLM (K := ℂ))
  have hΘCcs : HasCompactSupport
      (fun ω : EuclideanSpace ℝ (Fin d) => ((θ ((2 * Real.pi) • ω) : ℝ) : ℂ)) := by
    have hsupp : Function.support
        (fun ω : EuclideanSpace ℝ (Fin d) => ((θ ((2 * Real.pi) • ω) : ℝ) : ℂ)) =
        Function.support (fun ω : EuclideanSpace ℝ (Fin d) =>
          θ ((2 * Real.pi) • ω)) := by
      ext ω
      simp [Function.mem_support]
    rw [HasCompactSupport, tsupport, hsupp, ← tsupport]
    exact hθ2cs
  set Θ : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ :=
    HasCompactSupport.toSchwartzMap hΘCcs hΘCdiff with hΘdef
  have hΘapply : ∀ ω : EuclideanSpace ℝ (Fin d),
      Θ ω = ((θ ((2 * Real.pi) • ω) : ℝ) : ℂ) := fun ω => rfl
  have hΘeven : ∀ ω : EuclideanSpace ℝ (Fin d), Θ (-ω) = Θ ω := by
    intro ω
    rw [hΘapply, hΘapply, smul_neg, hθeven]
  set S : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ := 𝓕⁻ Θ with hSdef
  have hSconj : ∀ x : EuclideanSpace ℝ (Fin d), (starRingEnd ℂ) (S x) = S x := by
    intro x
    have hSeven : S (-x) = S x := by
      rw [hSdef, SchwartzMap.fourierInv_coe, Real.fourierInv_eq' (⇑Θ) (-x),
        Real.fourierInv_eq' (⇑Θ) x]
      have hg : Integrable (fun v : EuclideanSpace ℝ (Fin d) =>
          Complex.exp ((↑(2 * Real.pi * ⟪v, -x⟫_ℝ) * Complex.I)) • Θ v)
          (volume : Measure (EuclideanSpace ℝ (Fin d))) := by
        have hΘint : Integrable (⇑Θ) (volume : Measure (EuclideanSpace ℝ (Fin d))) :=
          Θ.integrable
        refine hΘint.mono ?_ (Filter.Eventually.of_forall fun v => ?_)
        · fun_prop
        · rw [smul_eq_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
      rw [← integral_neg_of_integrable _]
      apply integral_congr_ae
      filter_upwards with v
      rw [hΘeven]
      congr 1
      rw [inner_neg_left, inner_neg_right, neg_neg]
    have hconj : (starRingEnd ℂ) (S x) = S (-x) := by
      rw [hSdef, SchwartzMap.fourierInv_coe, Real.fourierInv_eq' (⇑Θ) x,
        Real.fourierInv_eq' (⇑Θ) (-x), ← integral_conj]
      apply integral_congr_ae
      filter_upwards with v
      rw [smul_eq_mul, smul_eq_mul, map_mul, hΘapply]
      simp only [Complex.conj_ofReal]
      rw [← Complex.exp_conj]
      congr 1
      rw [inner_neg_right, map_mul]
      simp only [Complex.conj_ofReal, Complex.conj_I]
      push_cast
      ring_nf
    rw [hconj, hSeven]
  have hSim : ∀ x : EuclideanSpace ℝ (Fin d), (S x).im = 0 := by
    intro x
    have h := congrArg Complex.im (hSconj x)
    simp only [Complex.conj_im] at h
    linarith
  have hSeq : ∀ x : EuclideanSpace ℝ (Fin d), S x = ((S x).re : ℂ) := by
    intro x
    rw [← Complex.re_add_im (S x), hSim x]
    simp
  set s : EuclideanSpace ℝ (Fin d) → ℝ :=
    fun x => (2 * Real.pi) ^ d * (S x).re with hsdef
  have hscont : Continuous s := by
    rw [hsdef]
    exact continuous_const.mul (Complex.continuous_re.comp S.continuous)
  have hsint : Integrable s (volume : Measure (EuclideanSpace ℝ (Fin d))) := by
    rw [hsdef]
    exact (S.integrable.re).const_mul _
  have hFourierAll : ∀ ξ : EuclideanSpace ℝ (Fin d),
      ∫ x, ((s x : ℝ) : ℂ) * Complex.exp (((⟪x, ξ⟫_ℝ : ℝ) : ℂ) * Complex.I)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin d))) =
        (((2 * Real.pi) ^ d * θ ξ : ℝ) : ℂ) := by
    intro ξ
    have hη : ((2 * Real.pi : ℝ)) • ((2 * Real.pi)⁻¹ • ξ) = ξ := by
      rw [smul_smul, mul_inv_cancel₀ h2pi, one_smul]
    have hFourier : (∫ x, S x * Complex.exp (((⟪x, ξ⟫_ℝ : ℝ) : ℂ) * Complex.I)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin d)))) =
        Θ (-((2 * Real.pi)⁻¹ • ξ)) := by
      have hstep : (∫ x, S x * Complex.exp (((⟪x, ξ⟫_ℝ : ℝ) : ℂ) * Complex.I)
            ∂(volume : Measure (EuclideanSpace ℝ (Fin d)))) =
          𝓕 (⇑S) (-((2 * Real.pi)⁻¹ • ξ)) := by
        rw [Real.fourier_eq']
        apply integral_congr_ae
        filter_upwards with x
        rw [smul_eq_mul, mul_comm]
        congr 1
        rw [inner_neg_right, inner_smul_right]
        congr 1
        push_cast
        rw [show (-2 * (Real.pi:ℂ)) * (-((2 * (Real.pi:ℂ))⁻¹ * (⟪x, ξ⟫_ℝ:ℂ))) =
            (⟪x, ξ⟫_ℝ:ℂ) by
          have hne : ((2:ℂ) * (Real.pi:ℂ)) ≠ 0 := by exact_mod_cast h2pi
          field_simp]
      rw [hstep, hSdef, SchwartzMap.fourierInv_coe]
      have hpair : 𝓕 (𝓕⁻ ⇑Θ) (-((2 * Real.pi)⁻¹ • ξ)) = Θ (-((2 * Real.pi)⁻¹ • ξ)) := by
        have h := congrArg (fun F : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ =>
            F (-((2 * Real.pi)⁻¹ • ξ)))
          (@FourierInvPair.fourier_fourierInv_eq
            (SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ)
            (SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ) _ _ _ Θ)
        rwa [SchwartzMap.fourier_coe, SchwartzMap.fourierInv_coe] at h
      exact hpair
    have hΘξ : Θ (-((2 * Real.pi)⁻¹ • ξ)) = ((θ ξ : ℝ) : ℂ) := by
      rw [hΘapply, show (2 * Real.pi) • (-((2 * Real.pi)⁻¹ • ξ)) = -ξ by
        rw [smul_neg, smul_smul, mul_inv_cancel₀ h2pi, one_smul], hθeven]
    calc ∫ x, ((s x : ℝ) : ℂ) * Complex.exp (((⟪x, ξ⟫_ℝ : ℝ) : ℂ) * Complex.I)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin d)))
        = ∫ x, (2 * Real.pi) ^ d * (S x * Complex.exp (((⟪x, ξ⟫_ℝ : ℝ) : ℂ) * Complex.I))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin d))) := by
          apply integral_congr_ae
          filter_upwards with x
          rw [hsdef]
          simp only
          rw [hSeq x]
          push_cast
          simp only [Complex.ofReal_re]
          ring
      _ = (2 * Real.pi) ^ d * ∫ x, S x * Complex.exp (((⟪x, ξ⟫_ℝ : ℝ) : ℂ) * Complex.I)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin d))) :=
          integral_const_mul _ _
      _ = (2 * Real.pi) ^ d * Θ (-((2 * Real.pi)⁻¹ • ξ)) := by rw [hFourier]
      _ = (((2 * Real.pi) ^ d * θ ξ : ℝ) : ℂ) := by
          rw [hΘξ]
          push_cast
          ring
  have hexists : ∃ x, s x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h0 := hFourierAll ω₁
    simp only [hcon, Complex.ofReal_zero, zero_mul, MeasureTheory.integral_zero] at h0
    have hreal : (2 * Real.pi) ^ d * θ ω₁ = 0 := Complex.ofReal_eq_zero.mp h0.symm
    have hpos : (2 * Real.pi) ^ d ≠ 0 := by positivity
    rcases mul_eq_zero.mp hreal with h | h
    · exact absurd h hpos
    · exact hθω₁ h
  have hint0 : (∫ x, s x ∂(volume : Measure (EuclideanSpace ℝ (Fin d)))) = 0 := by
    have h0 := hFourierAll 0
    have hLHS : (∫ x, ((s x : ℝ) : ℂ) *
        Complex.exp (((⟪x, (0 : EuclideanSpace ℝ (Fin d))⟫_ℝ : ℝ) : ℂ) * Complex.I)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin d)))) =
        ((∫ x, s x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))) : ℝ) : ℂ) := by
      have h1 : (∫ x, ((s x : ℝ) : ℂ) *
        Complex.exp (((⟪x, (0 : EuclideanSpace ℝ (Fin d))⟫_ℝ : ℝ) : ℂ) * Complex.I)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin d)))) =
          ∫ x, ((s x : ℝ) : ℂ) ∂(volume : Measure (EuclideanSpace ℝ (Fin d))) := by
        apply integral_congr_ae
        filter_upwards with x
        simp
      rw [h1]
      exact integral_ofReal
    rw [hLHS, hθ0] at h0
    simp only [mul_zero, Complex.ofReal_zero] at h0
    exact Complex.ofReal_eq_zero.mp h0
  have hratio : ∃ R : ℝ, ∀ x, |s x| ≤
      R * ∏ i : Fin d, ProbabilityTheory.cauchyPDFReal 0 1 (x i) := by
    obtain ⟨R, hR⟩ := schwartz_ratio_bound S
    exact ⟨R, fun x => by simpa [hsdef] using hR x⟩
  exact ⟨s, hscont, hsint, hFourierAll, hexists, hint0, hratio⟩

private lemma not_isCharacteristic_of_support_ne_univ
    (Λ : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure Λ]
    (hk : ∀ x y : EuclideanSpace ℝ (Fin d), (kernelValue H x y : ℂ) =
      ∫ ω, Complex.exp (-((⟪x - y, ω⟫_ℝ : ℝ) : ℂ) * Complex.I) ∂Λ)
    (hd : 0 < d) (hsupp : Λ.support ≠ Set.univ) :
    ¬ IsCharacteristic H := by
  intro hIsChar
  have hsymm := measure_map_neg_eq Λ hk
  obtain ⟨ω₁, hω₁0, hω₁, r, hr, hr2, hsub1, hsub2⟩ :=
    exists_bump_point Λ hsymm hd hsupp
  obtain ⟨θ, hθdiff, hθcs, hθeven, _hθnonneg, hθω₁, hθ0, hθsupp⟩ :=
    exists_bump_theta Λ ω₁ hω₁0 r hr hr2 hsub1 hsub2
  obtain ⟨s, hscont, hsint, hsfour, hexists, hsint0, ⟨R, hR⟩⟩ :=
    exists_perturbation θ hθdiff hθcs hθeven hθ0 ω₁ hθω₁
  set g : EuclideanSpace ℝ (Fin d) → ℝ :=
    fun x => ∏ i : Fin d, ProbabilityTheory.cauchyPDFReal 0 1 (x i) with hgdef
  have hgcont : Continuous g := by
    rw [hgdef]
    have hc : Continuous fun t : ℝ => ProbabilityTheory.cauchyPDFReal 0 1 t := by
      have heq : (fun t : ℝ => ProbabilityTheory.cauchyPDFReal 0 1 t) =
          fun t => Real.pi⁻¹ * ((t ^ 2 + 1)⁻¹) := by
        funext t
        rw [ProbabilityTheory.cauchyPDFReal_def]
        simp
      rw [heq]
      have h2 : Continuous fun t : ℝ => t ^ 2 + 1 := by fun_prop
      exact continuous_const.mul (h2.inv₀
        (fun t => ne_of_gt (by have h := sq_nonneg t; linarith)))
    exact continuous_list_prod (List.finRange d) fun i _ =>
      hc.comp (by fun_prop : Continuous fun x : EuclideanSpace ℝ (Fin d) => x i)
  have hgpos : ∀ x : EuclideanSpace ℝ (Fin d), 0 < g x := by
    intro x
    rw [hgdef]
    apply Finset.prod_pos
    intro i _
    exact ProbabilityTheory.cauchyPDF_pos 0 (by norm_num) _
  have hgint : Integrable g (volume : Measure (EuclideanSpace ℝ (Fin d))) := by
    rw [hgdef]
    have hPi : Integrable (fun y : Fin d → ℝ =>
        ∏ i : Fin d, ProbabilityTheory.cauchyPDFReal 0 1 (y i))
        (Measure.pi fun _ : Fin d => (volume : Measure ℝ)) :=
      Integrable.fintype_prod (fun _ => ProbabilityTheory.integrable_cauchyPDFReal 0)
    have htr := (PiLp.volume_preserving_toLp (Fin d)).integrable_comp_emb
      (MeasurableEquiv.measurableEmbedding (MeasurableEquiv.toLp 2 (Fin d → ℝ)))
      (g := fun x : EuclideanSpace ℝ (Fin d) =>
        ∏ i : Fin d, ProbabilityTheory.cauchyPDFReal 0 1 (x i))
    exact htr.mp hPi
  have hgint1 : ∫ x, g x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))) = 1 := by
    rw [hgdef]
    have htr : ∫ x : EuclideanSpace ℝ (Fin d),
        (∏ i : Fin d, ProbabilityTheory.cauchyPDFReal 0 1 (x i))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin d))) =
        ∫ y : Fin d → ℝ, ∏ i : Fin d, ProbabilityTheory.cauchyPDFReal 0 1 (y i)
          ∂(volume : Measure (Fin d → ℝ)) :=
      ((PiLp.volume_preserving_toLp (Fin d)).integral_comp
        (MeasurableEquiv.measurableEmbedding (MeasurableEquiv.toLp 2 (Fin d → ℝ)))
        (fun x : EuclideanSpace ℝ (Fin d) =>
          ∏ i : Fin d, ProbabilityTheory.cauchyPDFReal 0 1 (x i))).symm
    rw [htr, MeasureTheory.integral_fintype_prod_volume_eq_prod]
    have h1 : ∀ i : Fin d, (∫ x : ℝ, ProbabilityTheory.cauchyPDFReal 0 1 x
        ∂(volume : Measure ℝ)) = 1 :=
      fun _ => ProbabilityTheory.integral_cauchyPDFReal_eq_one 0 (by norm_num)
    rw [Finset.prod_congr rfl (fun i _ => h1 i)]
    exact Finset.prod_const_one
  have hε : ∃ ε : ℝ, 0 < ε ∧ ∀ x, ε * |s x| ≤ g x / 2 := by
    refine ⟨1 / (2 * (|R| + 1)), by positivity, fun x => ?_⟩
    have hR' : |s x| ≤ |R| * g x :=
      (hR x).trans (mul_le_mul_of_nonneg_right (le_abs_self R) (le_of_lt (hgpos x)))
    have hpos2 : (0:ℝ) < 2 * (|R| + 1) := by positivity
    calc 1 / (2 * (|R| + 1)) * |s x|
        ≤ 1 / (2 * (|R| + 1)) * (|R| * g x) :=
          mul_le_mul_of_nonneg_left hR' (by positivity)
      _ = (|R| / (2 * (|R| + 1))) * g x := by
          field_simp
      _ ≤ (1 / 2) * g x := by
          apply mul_le_mul_of_nonneg_right _ (le_of_lt (hgpos x))
          rw [div_le_iff₀ hpos2]
          have := abs_nonneg R
          nlinarith
      _ = g x / 2 := by ring
  obtain ⟨ε, hεpos, hεbound⟩ := hε
  have hρpos : ∀ (c : ℝ), |c| ≤ ε → ∀ x : EuclideanSpace ℝ (Fin d),
      0 < g x + c * s x := by
    intro c hc x
    have h1 : |c * s x| ≤ g x / 2 := by
      calc |c * s x| = |c| * |s x| := abs_mul _ _
        _ ≤ ε * |s x| := mul_le_mul_of_nonneg_right hc (abs_nonneg _)
        _ ≤ g x / 2 := hεbound x
    have h2 : -(g x / 2) ≤ c * s x := by
      have := neg_abs_le (c * s x)
      linarith
    linarith [hgpos x]
  have hρint : ∀ (c : ℝ), Integrable (fun x => g x + c * s x)
      (volume : Measure (EuclideanSpace ℝ (Fin d))) :=
    fun c => hgint.add (hsint.const_mul c)
  have hρint1 : ∀ (c : ℝ), (∫ x, (g x + c * s x)
      ∂(volume : Measure (EuclideanSpace ℝ (Fin d)))) = 1 := by
    intro c
    rw [integral_add hgint (hsint.const_mul c), hgint1, integral_const_mul, hsint0,
      mul_zero, add_zero]
  have hρmeas : ∀ (c : ℝ), Measurable
      (fun x : EuclideanSpace ℝ (Fin d) => ENNReal.ofReal (g x + c * s x)) := by
    intro c
    exact ENNReal.measurable_ofReal.comp
      ((hgcont.add (hscont.const_mul c)).measurable)
  -- characteristic functions of the perturbed measures
  have hchar : ∀ (c : ℝ), |c| ≤ ε → ∀ (t : EuclideanSpace ℝ (Fin d)),
      MeasureTheory.charFun
        ((volume : Measure (EuclideanSpace ℝ (Fin d))).withDensity
          (fun x => ENNReal.ofReal (g x + c * s x))) t =
        ∫ x, (((g x + c * s x : ℝ)) : ℂ) *
          Complex.exp (((⟪x, t⟫_ℝ : ℝ) : ℂ) * Complex.I)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin d))) := by
    intro c hc t
    rw [MeasureTheory.charFun_apply,
      integral_withDensity_eq_integral_toReal_smul (hρmeas c)
        (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
    apply integral_congr_ae
    filter_upwards with x
    rw [ENNReal.toReal_ofReal (le_of_lt (hρpos c hc x))]
    rw [Complex.real_smul]
  -- the two perturbed measures
  set μpos : Measure (EuclideanSpace ℝ (Fin d)) :=
    (volume : Measure (EuclideanSpace ℝ (Fin d))).withDensity
      (fun x => ENNReal.ofReal (g x + ε * s x)) with hμposdef
  set μneg : Measure (EuclideanSpace ℝ (Fin d)) :=
    (volume : Measure (EuclideanSpace ℝ (Fin d))).withDensity
      (fun x => ENNReal.ofReal (g x + (-ε) * s x)) with hμnegdef
  have hεabs : |ε| ≤ ε := by rw [abs_of_pos hεpos]
  have hεabs' : |-ε| ≤ ε := by rw [abs_neg, abs_of_pos hεpos]
  have hprobPos : IsProbabilityMeasure μpos := by
    refine ⟨?_⟩
    rw [hμposdef, withDensity_apply _
      MeasurableSet.univ, MeasureTheory.Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal (hρint ε)
        (Filter.Eventually.of_forall fun x => le_of_lt (hρpos ε hεabs x)),
      hρint1 ε, ENNReal.ofReal_one]
  have hprobNeg : IsProbabilityMeasure μneg := by
    refine ⟨?_⟩
    rw [hμnegdef, withDensity_apply _
      MeasurableSet.univ, MeasureTheory.Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal (hρint (-ε))
        (Filter.Eventually.of_forall fun x => le_of_lt (hρpos (-ε) hεabs' x)),
      hρint1 (-ε), ENNReal.ofReal_one]
  have hprobPosI : IsProbabilityMeasure μpos := hprobPos
  have hprobNegI : IsProbabilityMeasure μneg := hprobNeg
  -- the characteristic functions agree on the support of Λ
  have hint : ∀ (c : ℝ), |c| ≤ ε → ∀ ω : EuclideanSpace ℝ (Fin d),
      Integrable (fun x => (((g x + c * s x : ℝ)) : ℂ) *
        Complex.exp (((⟪x, -ω⟫_ℝ : ℝ) : ℂ) * Complex.I))
        (volume : Measure (EuclideanSpace ℝ (Fin d))) := by
    intro c hc ω
    have hb : Integrable (fun x : EuclideanSpace ℝ (Fin d) => (3 / 2 : ℝ) * g x)
        (volume : Measure (EuclideanSpace ℝ (Fin d))) := hgint.const_mul _
    refine hb.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
    · have h1 : Continuous fun x : EuclideanSpace ℝ (Fin d) =>
          ((g x + c * s x : ℝ) : ℂ) :=
        (RCLike.ofRealCLM (K := ℂ)).continuous.comp (hgcont.add (hscont.const_mul c))
      have h2 : Continuous fun x : EuclideanSpace ℝ (Fin d) =>
          Complex.exp (((⟪x, -ω⟫_ℝ : ℝ) : ℂ) * Complex.I) := by fun_prop
      exact (h1.mul h2).aestronglyMeasurable
    · have hρ : |g x + c * s x| ≤ (3 / 2 : ℝ) * g x := by
        have h1 : |c * s x| ≤ g x / 2 := by
          calc |c * s x| = |c| * |s x| := abs_mul _ _
            _ ≤ ε * |s x| := mul_le_mul_of_nonneg_right hc (abs_nonneg _)
            _ ≤ g x / 2 := hεbound x
        have h3 := abs_le.mp h1
        refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith [hgpos x, h3.1, h3.2]
      calc ‖((g x + c * s x : ℝ) : ℂ) * Complex.exp (((⟪x, -ω⟫_ℝ : ℝ) : ℂ) * Complex.I)‖
          = ‖((g x + c * s x : ℝ) : ℂ)‖ := by
            rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
        _ = |g x + c * s x| := by rw [Complex.norm_real, Real.norm_eq_abs]
        _ ≤ (3 / 2 : ℝ) * g x := hρ
  have hD : ∀ ω : EuclideanSpace ℝ (Fin d), ω ∈ Λ.support →
      MeasureTheory.charFun μpos (-ω) - MeasureTheory.charFun μneg (-ω) = 0 := by
    intro ω hω
    have hθ0' : θ (-ω) = 0 :=
      hθsupp (-ω) ((neg_mem_support Λ hsymm ω).mpr hω)
    have hfour0 : (∫ x, ((s x : ℝ) : ℂ) *
        Complex.exp (((⟪x, -ω⟫_ℝ : ℝ) : ℂ) * Complex.I)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin d)))) = 0 := by
      simpa [hθ0'] using hsfour (-ω)
    rw [hμposdef, hμnegdef, hchar ε hεabs (-ω), hchar (-ε) hεabs' (-ω),
      ← integral_sub (hint ε hεabs ω) (hint (-ε) hεabs' ω)]
    have hdiff : (∫ x, ((((g x + ε * s x : ℝ)) : ℂ) *
          Complex.exp (((⟪x, -ω⟫_ℝ : ℝ) : ℂ) * Complex.I) -
          (((g x + (-ε) * s x : ℝ)) : ℂ) *
          Complex.exp (((⟪x, -ω⟫_ℝ : ℝ) : ℂ) * Complex.I))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin d)))) =
        (2 * ε : ℂ) * ∫ x, ((s x : ℝ) : ℂ) *
          Complex.exp (((⟪x, -ω⟫_ℝ : ℝ) : ℂ) * Complex.I)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin d))) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      push_cast
      ring
    rw [hdiff, hfour0, mul_zero]
  have hae : ∀ᵐ ω ∂Λ, ω ∈ Λ.support := by
    rw [MeasureTheory.ae_iff]
    have hset : {ω : EuclideanSpace ℝ (Fin d) | ¬ ω ∈ Λ.support} = Λ.supportᶜ := by
      ext ω
      simp
    rw [hset]
    exact MeasureTheory.Measure.measure_compl_support
  have hemb : meanEmbedding H μpos = meanEmbedding H μneg := by
    have h0 : ‖meanEmbedding H μpos - meanEmbedding H μneg‖ ^ 2 = 0 := by
      rw [norm_meanEmbedding_sub_sq Λ hk μpos μneg]
      apply MeasureTheory.integral_eq_zero_of_ae
      filter_upwards [hae] with ω hω
      rw [hD ω hω]
      simp
    have hnorm : ‖meanEmbedding H μpos - meanEmbedding H μneg‖ = 0 := by
      rw [← sq_eq_zero_iff]
      exact h0
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
  -- the measures are distinct
  obtain ⟨x0, hx0⟩ := hexists
  obtain ⟨δ, hδpos, hδ⟩ :=
    (Metric.tendsto_nhds_nhds.mp (hscont.tendsto x0)) (|s x0| / 2)
      (half_pos (abs_pos.mpr hx0))
  obtain ⟨φ, hφtsupp, _hφcs, hφsmooth, hφrange, hφone⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) (s := Metric.ball x0 δ) (x := x0)
      (Metric.ball_mem_nhds x0 hδpos)
  have hφcont : Continuous φ := hφsmooth.continuous
  have hφnn : ∀ x, 0 ≤ φ x := fun x => (hφrange ⟨x, rfl⟩).1
  have hφsupp : ∀ x, φ x ≠ 0 → x ∈ Metric.ball x0 δ := by
    intro x hx
    exact hφtsupp (subset_closure hx)
  have hsign : ∀ x ∈ Metric.ball x0 δ, (s x0) * s x ≥ (s x0) ^ 2 / 2 := by
    intro x hx
    have h1 : |s x - s x0| < |s x0| / 2 := by
      have h := hδ (Metric.mem_ball.mp hx)
      rwa [Real.dist_eq] at h
    by_cases ha : 0 ≤ s x0
    · have ha' : 0 < s x0 := lt_of_le_of_ne ha (Ne.symm hx0)
      have hb : s x0 / 2 < s x := by
        have habs := abs_lt.mp h1
        rw [abs_of_nonneg ha] at habs
        linarith [habs.1]
      nlinarith [hb, ha']
    · push Not at ha
      have hb : s x < s x0 / 2 := by
        have habs := abs_lt.mp h1
        rw [abs_of_neg ha] at habs
        linarith [habs.2]
      nlinarith [hb, ha]
  have hψint : Integrable (fun x => s x0 * (φ x * s x))
      (volume : Measure (EuclideanSpace ℝ (Fin d))) := by
    have h1 : Integrable (fun x => φ x * s x)
        (volume : Measure (EuclideanSpace ℝ (Fin d))) := by
      refine (hsint.norm).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
      · exact (hφcont.mul hscont).aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hφnn x)]
        calc φ x * |s x| ≤ 1 * |s x| :=
              mul_le_mul_of_nonneg_right (hφrange ⟨x, rfl⟩).2 (abs_nonneg _)
          _ = |s x| := one_mul _
    exact h1.const_mul _
  have hψnn : ∀ x, 0 ≤ s x0 * (φ x * s x) := by
    intro x
    by_cases hφx : φ x = 0
    · simp [hφx]
    · have hx : x ∈ Metric.ball x0 δ := hφsupp x hφx
      have h1 := hsign x hx
      nlinarith [hφnn x, h1]
  have hψpos : 0 < ∫ x, s x0 * (φ x * s x)
      ∂(volume : Measure (EuclideanSpace ℝ (Fin d))) := by
    apply (MeasureTheory.integral_pos_iff_support_of_nonneg
      (fun x => hψnn x) hψint).mpr
    have hopen : IsOpen (Function.support fun x => s x0 * (φ x * s x)) := by
      have heq : (Function.support fun x => s x0 * (φ x * s x)) =
          (fun x => s x0 * (φ x * s x)) ⁻¹' {0}ᶜ := by
        ext x
        simp [Function.mem_support]
      rw [heq]
      exact isOpen_compl_singleton.preimage (continuous_const.mul (hφcont.mul hscont))
    have hmem : x0 ∈ Function.support fun x => s x0 * (φ x * s x) := by
      simp only [Function.mem_support, ne_eq]
      rw [hφone]
      simp [hx0]
    exact MeasureTheory.Measure.measure_pos_of_mem_nhds
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin d)))) (hopen.mem_nhds hmem)
  have hφs_ne : (∫ x, φ x * s x ∂(volume : Measure (EuclideanSpace ℝ (Fin d)))) ≠ 0 := by
    intro hcon
    have hψeq : (∫ x, s x0 * (φ x * s x)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin d)))) =
        s x0 * ∫ x, φ x * s x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))) :=
      integral_const_mul _ _
    rw [hψeq, hcon, mul_zero] at hψpos
    exact lt_irrefl _ hψpos
  have hφint : ∀ (c : ℝ), |c| ≤ ε → Integrable (fun x => φ x * (g x + c * s x))
      (volume : Measure (EuclideanSpace ℝ (Fin d))) := by
    intro c hc
    refine ((hρint c).norm).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact (hφcont.mul (hgcont.add (hscont.const_mul c))).aestronglyMeasurable
    · simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hφnn x)]
      calc φ x * |g x + c * s x| ≤ 1 * |g x + c * s x| :=
            mul_le_mul_of_nonneg_right (hφrange ⟨x, rfl⟩).2 (abs_nonneg _)
        _ = |g x + c * s x| := one_mul _
  have hφμ : ∀ (c : ℝ), |c| ≤ ε →
      (∫ x, φ x ∂((volume : Measure (EuclideanSpace ℝ (Fin d))).withDensity
          (fun x => ENNReal.ofReal (g x + c * s x)))) =
        ∫ x, φ x * (g x + c * s x)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin d))) := by
    intro c hc
    rw [integral_withDensity_eq_integral_toReal_smul (hρmeas c)
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
    apply integral_congr_ae
    filter_upwards with x
    rw [ENNReal.toReal_ofReal (le_of_lt (hρpos c hc x)), smul_eq_mul, mul_comm]
  have hμne : μpos ≠ μneg := by
    intro heq
    have h1 := hφμ ε hεabs
    have h2 := hφμ (-ε) hεabs'
    rw [← hμposdef, heq] at h1
    rw [← hμnegdef] at h2
    have hdiff : (∫ x, φ x * (g x + ε * s x)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin d)))) -
        (∫ x, φ x * (g x + (-ε) * s x)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin d)))) = 0 := by
      rw [← h1, ← h2, sub_self]
    have hdiff2 : (∫ x, φ x * (g x + ε * s x)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin d)))) -
        (∫ x, φ x * (g x + (-ε) * s x)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin d)))) =
        2 * ε * ∫ x, φ x * s x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))) := by
      rw [← integral_sub (hφint ε hεabs) (hφint (-ε) hεabs'),
        ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      ring
    rw [hdiff2] at hdiff
    have hne : (2 : ℝ) * ε * ∫ x, φ x * s x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin d))) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) (ne_of_gt hεpos)) hφs_ne
    exact hne hdiff
  exact hμne (hIsChar μpos μneg hprobPos hprobNeg (integrable_featureMap Λ hk μpos)
    (integrable_featureMap Λ hk μneg) hemb)

end Helpers

/-- **Characterization of characteristic translation-invariant kernels** (Sriperumbudur,
Gretton, Fukumizu, Schölkopf and Lanckriet, *Hilbert space embeddings and metrics on probability
measures*, JMLR 11 (2010), Theorem 9). Let `d ≥ 1` and let `H` be a real RKHS on `ℝ^d`
whose kernel is `k(x, y) = ψ(x - y)` with `ψ(x) = ∫ exp(-i xᵀω) dΛ(ω)` for a finite Borel
measure `Λ`, so that `ψ` is a bounded continuous real positive-definite function
(equation (11)). Then `k` is characteristic if and only if the support of `Λ` is all of
`ℝ^d`. -/
theorem isCharacteristic_iff_support_eq_univ {d : ℕ} (hd : 0 < d) {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [RKHS ℝ H (EuclideanSpace ℝ (Fin d)) ℝ]
    (Λ : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure Λ]
    (hk : ∀ x y : EuclideanSpace ℝ (Fin d), (kernelValue H x y : ℂ) =
      ∫ ω, Complex.exp (-((⟪x - y, ω⟫_ℝ : ℝ) : ℂ) * Complex.I) ∂Λ) :
    IsCharacteristic H ↔ Λ.support = Set.univ := by
  constructor
  · intro hchar
    by_contra hsupp
    exact not_isCharacteristic_of_support_ne_univ Λ hk hd hsupp hchar
  · intro hsupp μ ν _ _ hμ hν hemb
    have hcharFun := charFun_eq_of_support_eq_univ Λ hk hsupp μ ν hemb
    exact MeasureTheory.Measure.ext_of_charFun hcharFun


end MathlibExt.Probability.TranslationInvariantCharacteristicKernelWanted
