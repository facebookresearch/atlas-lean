/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Analysis.SineIntegral
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# Gil-Pelaez inversion formula

For a probability law `μ` on `ℝ` with finite mean and every `x`,
`½ + π⁻¹ ∫₀^T Im(e^{-i t x} φ_μ(t)) / t dt → ½ (μ(x, ∞) + μ[x, ∞))` as `T → ∞`
(`tendsto_gilPelaez`). At an atom the limit is the mid-p value, not `μ(x, ∞)`.

Helpers: `im_cexp_mul_charFun` (`Im(e^{-i t x} φ_μ(t)) = ∫ sin(t (y - x)) dμ(y)`) and
`integral_sign_sub` (`∫ sign(y - x) dμ(y) = μ(x, ∞) + μ[x, ∞) - 1`).

## Source contract

J. Gil-Pelaez, *Note on the inversion theorem*, Biometrika 38 (1951), 481–482. The finite-mean
hypothesis is stronger than Gil-Pelaez's and is used only for Fubini on `[0, T] × ℝ`.

## Attribution

Copied verbatim (statements and proofs unchanged) from
`MathlibExt/Biology/StatisticalGenetics/RareVariantInference/BurdenSKATO.lean`
(T88, open PR #1621, commit 45948b862),
section `GilPelaez`, where it feeds Davies' p-value formula. Only the namespace changed; the
sine-integral lemmas it uses now live in `MathlibExt.Analysis.SineIntegral`. The BurdenSKATO
copies are deleted after #1621 merges; until then both namespaces hold identical copies.

## API-00 receipt (base `origin/main` f8123a751)

Reuse search of `MathlibExt`, `WantedExt`, `CSLibExt` and the pinned Mathlib for Gil-Pelaez
or Imhof inversion found nothing. Reused: Mathlib's `charFun`, `charFun_apply_real`,
`integral_integral_swap`, `tendsto_integral_filter_of_dominated_convergence`.
-/

@[expose] public section

open MeasureTheory MathlibExt.Analysis.SineIntegral

namespace MathlibExt.Analysis.GilPelaez

open Real Set Filter Topology

open Complex in
/-- `Im(e^{-i t x} φ_μ(t)) = ∫ sin(t (y - x)) dμ(y)`. -/
theorem im_cexp_mul_charFun (μ : Measure ℝ) [IsProbabilityMeasure μ] (t x : ℝ) :
    (cexp (-(t * x) * I) * charFun μ t).im = ∫ y, Real.sin (t * (y - x)) ∂μ := by
  have h : ∀ y : ℝ, cexp (-(t * x) * I) * cexp (t * y * I) = cexp (↑(t * (y - x)) * I) := by
    intro y
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hint : Integrable (fun y : ℝ => cexp (↑(t * (y - x)) * I)) μ := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) (ae_of_all _ fun y => ?_)
    rw [norm_exp_ofReal_mul_I]
  rw [charFun_apply_real, ← integral_const_mul]
  simp_rw [h]
  have := integral_im hint
  simp only [RCLike.im_to_complex] at this
  rw [← this]
  simp_rw [exp_ofReal_mul_I_im]

private theorem sin_div_eq_mul_sinc {t : ℝ} (ht : t ≠ 0) (s : ℝ) :
    Real.sin (t * s) / t = s * sinc (t * s) := by
  rcases eq_or_ne s 0 with rfl | hs
  · simp
  · rw [sinc_of_ne_zero (mul_ne_zero ht hs)]
    field_simp

/-- `∫ sign(y - x) dμ(y) = P(Y > x) + P(Y ≥ x) - 1`. -/
theorem integral_sign_sub {μ : Measure ℝ} [IsProbabilityMeasure μ] (x : ℝ) :
    ∫ y, Real.sign (y - x) ∂μ = μ.real (Ioi x) + μ.real (Ici x) - 1 := by
  have h : (fun y => Real.sign (y - x)) =
      fun y => (Ioi x).indicator 1 y - (Iio x).indicator 1 y := by
    funext y
    rcases lt_trichotomy y x with h | rfl | h
    · simp [Real.sign_of_neg (sub_neg.2 h), h, not_lt.2 h.le]
    · simp
    · simp [Real.sign_of_pos (sub_pos.2 h), h, not_lt.2 h.le]
  have h1 : Integrable ((Ioi x).indicator (1 : ℝ → ℝ)) μ :=
    (integrable_const (1 : ℝ)).indicator measurableSet_Ioi
  have h2 : Integrable ((Iio x).indicator (1 : ℝ → ℝ)) μ :=
    (integrable_const (1 : ℝ)).indicator measurableSet_Iio
  rw [h, integral_sub h1 h2,
    integral_indicator_one measurableSet_Ioi, integral_indicator_one measurableSet_Iio,
    ← compl_Ici, measureReal_compl measurableSet_Ici, probReal_univ]
  ring

open Complex in
/-- **Gil-Pelaez inversion formula** (Gil-Pelaez 1951). For a probability law `μ` on `ℝ` with
finite mean and every `x`,
`½ + π⁻¹ ∫₀^T Im(e^{-i t x} φ_μ(t)) / t dt → ½ (μ(x, ∞) + μ[x, ∞))` as `T → ∞`.
The finite mean is used only for Fubini on `[0, T] × ℝ`. -/
theorem tendsto_gilPelaez {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : Integrable id μ)
    (x : ℝ) :
    Tendsto (fun T => 1 / 2 + π⁻¹ * ∫ t in (0 : ℝ)..T, (cexp (-(t * x) * I) * charFun μ t).im / t)
      atTop (𝓝 ((μ.real (Ioi x) + μ.real (Ici x)) / 2)) := by
  have hsub : Integrable (fun y => y - x) μ := hμ.sub (integrable_const x)
  -- the inner integral over `t`, after Fubini
  have key : ∀ T, 0 < T → ∫ t in (0 : ℝ)..T, (cexp (-(t * x) * I) * charFun μ t).im / t =
      ∫ y, sineIntegral ((y - x) * T) ∂μ := by
    intro T hT
    set F : ℝ → ℝ → ℝ := fun t y => (y - x) * sinc (t * (y - x))
    have hF : Continuous (Function.uncurry F) := by
      unfold F; exact (by fun_prop : Continuous fun p : ℝ × ℝ => (p.2 - x) * sinc (p.1 * (p.2 - x)))
    have hFle : ∀ t y, ‖F t y‖ ≤ |y - x| := by
      intro t y
      simp only [F, Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (abs_sinc_le_one _)
    have hint : Integrable (Function.uncurry F) ((volume.restrict (Ioc 0 T)).prod μ) := by
      rw [integrable_prod_iff hF.aestronglyMeasurable]
      refine ⟨Filter.Eventually.of_forall fun t => ?_, ?_⟩
      · exact hsub.abs.mono' (hF.comp (Continuous.prodMk_right t)).aestronglyMeasurable
          (ae_of_all _ fun y => hFle t y)
      · refine Integrable.mono' (integrable_const (∫ y, |y - x| ∂μ))
          (hF.norm.aestronglyMeasurable.integral_prod_right') (ae_of_all _ fun t => ?_)
        simp only [Function.uncurry_apply_pair]
        rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
        exact integral_mono (hsub.abs.mono'
          (hF.comp (Continuous.prodMk_right t)).norm.aestronglyMeasurable
          (ae_of_all _ fun y => by simpa using hFle t y)) hsub.abs fun y => hFle t y
    calc ∫ t in (0 : ℝ)..T, (cexp (-(t * x) * I) * charFun μ t).im / t
        = ∫ t in Ioc 0 T, ∫ y, F t y ∂μ := by
          rw [intervalIntegral.integral_of_le hT.le]
          refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
          rw [im_cexp_mul_charFun, ← integral_div]
          exact integral_congr_ae (ae_of_all _ fun y => sin_div_eq_mul_sinc ht.1.ne' _)
      _ = ∫ y, (∫ t in Ioc 0 T, F t y) ∂μ := integral_integral_swap hint
      _ = ∫ y, sineIntegral ((y - x) * T) ∂μ := by
          refine integral_congr_ae (ae_of_all _ fun y => ?_)
          beta_reduce
          rw [← intervalIntegral.integral_of_le hT.le]
          exact integral_mul_sinc (y - x) T
  have hlim : Tendsto (fun T => ∫ y, sineIntegral ((y - x) * T) ∂μ) atTop
      (𝓝 (∫ y, π / 2 * Real.sign (y - x) ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => 4)
      (Filter.Eventually.of_forall fun T => ?_) (Filter.Eventually.of_forall fun T =>
        ae_of_all _ fun y => abs_sineIntegral_le _) (integrable_const _)
      (ae_of_all _ fun y => tendsto_sineIntegral_mul_atTop (y - x))
    exact (continuous_sineIntegral.comp
      (by fun_prop : Continuous fun y : ℝ => (y - x) * T)).aestronglyMeasurable
  rw [integral_const_mul, integral_sign_sub] at hlim
  have h2 := (hlim.const_mul π⁻¹).const_add (1 / 2)
  have hval : 1 / 2 + π⁻¹ * (π / 2 * (μ.real (Ioi x) + μ.real (Ici x) - 1)) =
      (μ.real (Ioi x) + μ.real (Ici x)) / 2 := by
    field_simp
    ring
  rw [hval] at h2
  refine h2.congr' ((eventually_gt_atTop 0).mono fun T hT => ?_)
  beta_reduce
  rw [key T hT]

end MathlibExt.Analysis.GilPelaez
