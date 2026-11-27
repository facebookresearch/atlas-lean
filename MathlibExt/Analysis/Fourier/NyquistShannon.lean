/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Fourier.PoissonSummation
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.PSeries

/-!
# The Nyquist–Shannon sampling theorem

A Schwartz function `f : ℝ → ℂ` whose Fourier transform vanishes outside the Nyquist band
`[-1/2, 1/2]` (Mathlib's convention `𝓕 f ξ = ∫ f(x) e^{-2πixξ} dx`) is recovered from its integer
samples by the Whittaker–Shannon cardinal series `f(t) = ∑_n f(n) sinc(π(n - t))`.

Proof: Poisson's summation formula for the Schwartz function `𝓕 f` shows that on `(-1/2, 1/2)` the
spectrum is the Fourier series of the samples, `𝓕 f ξ = ∑_n f(n) e^{-2πinξ}` (`fourier_eq_tsum`).
Fourier inversion writes `f(t)` as the integral of `𝓕 f ξ e^{2πitξ}` over `[-1/2, 1/2]`; the
series converges uniformly because the samples are summable, and each term integrates to
`f(n) sinc(π(n - t))`.

## Main declarations

* `fourier_fourier_apply` : `𝓕 (𝓕 f) x = f (-x)` for Schwartz functions.
* `fourier_eq_tsum` : a band-limited spectrum is the Fourier series of the samples.
* `nyquist_shannon_sampling` : the sampling theorem, with summability of the cardinal series.
-/

@[expose] public section

open scoped FourierTransform SchwartzMap
open Set MeasureTheory Complex Real

noncomputable section

namespace MathlibExt.Analysis.Fourier.NyquistShannon

/-- **The Fourier transform applied twice reflects.** For a Schwartz function `f`,
`𝓕 (𝓕 f) x = f (-x)`, a consequence of Fourier inversion (`𝓕⁻ (𝓕 f) = f`) and
`𝓕⁻ g x = 𝓕 g (-x)`. -/
theorem fourier_fourier_apply (f : 𝓢(ℝ, ℂ)) (x : ℝ) : 𝓕 (𝓕 f) x = f (-x) := by
  have h0 : 𝓕⁻ (𝓕 f : 𝓢(ℝ, ℂ)) = f := FourierTransform.fourierInv_fourier_eq f
  have h := congrArg (fun g : 𝓢(ℝ, ℂ) => g (-x)) h0
  rw [← h, SchwartzMap.fourierInv_coe, fourierInv_eq_fourier_neg, neg_neg,
    SchwartzMap.fourier_coe]

theorem integral_exp_two_pi_mul_I (a : ℝ) :
    ∫ ξ in (-(1 / 2 : ℝ))..(1 / 2), Complex.exp (2 * π * a * ξ * I) =
      if a = 0 then 1 else ((Real.sin (π * a) / (π * a) : ℝ) : ℂ) := by
  split_ifs with ha
  · subst ha; norm_num
  · have hc : (2 * π * a * I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, ha, I_ne_zero]
    have := integral_exp_mul_complex (a := -(1/2 : ℝ)) (b := 1/2) hc
    simp_rw [show ∀ ξ : ℝ, (2 * π * a * ξ * I : ℂ) = 2 * π * a * I * ξ from fun ξ => by ring]
    rw [this]
    push_cast
    unfold Complex.sin
    have hpa : (π : ℂ) * a ≠ 0 := by simp [Real.pi_ne_zero, ha]
    field_simp
    ring_nf
    rw [I_sq]
    ring_nf

theorem summable_norm_int (f : 𝓢(ℝ, ℂ)) : Summable (fun n : ℤ => ‖f n‖) :=
  summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
    (((f.isBigO_cocompact_rpow (-2)).norm_left).comp_tendsto Int.tendsto_coe_cofinite)

/-- **A band-limited spectrum is the Fourier series of the samples.** If the Fourier transform of
a Schwartz function `f` vanishes outside `[-1/2, 1/2]`, then for `ξ ∈ (-1/2, 1/2)`,
`𝓕 f ξ = ∑_n f(n) e^{-2πinξ}` (Poisson's summation formula applied to `𝓕 f`, whose periodization
reduces to one term on `(-1/2, 1/2)`). -/
theorem fourier_eq_tsum (f : 𝓢(ℝ, ℂ)) (hf : ∀ ξ : ℝ, ξ ∉ Icc (-(1 / 2 : ℝ)) (1 / 2) → 𝓕 f ξ = 0)
    {ξ : ℝ} (hξ : ξ ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2)) :
    𝓕 f ξ = ∑' n : ℤ, f n * Complex.exp (2 * π * ((-n : ℤ) : ℝ) * ξ * I) := by
  have hP := SchwartzMap.tsum_eq_tsum_fourier (𝓕 f) ξ
  rw [tsum_eq_single 0 (fun m hm => ?_)] at hP
  · simp only [Int.cast_zero, add_zero] at hP
    rw [hP]
    rw [← (Equiv.neg ℤ).tsum_eq]
    refine tsum_congr fun n => ?_
    simp only [Equiv.neg_apply, fourier_coe_apply]
    rw [fourier_fourier_apply]
    push_cast
    refine congrArg₂ (· * ·) (by simp) ?_
    congr 1
    rw [div_one]
    ring
  · apply hf
    intro h
    rcases lt_or_gt_of_ne hm with hm' | hm'
    · have : (m : ℝ) ≤ -1 := by exact_mod_cast (show m ≤ -1 by omega)
      linarith [h.1, hξ.2]
    · have : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
      linarith [h.2, hξ.1]

theorem eq_intervalIntegral (f : 𝓢(ℝ, ℂ)) (hf : ∀ ξ : ℝ, ξ ∉ Icc (-(1 / 2 : ℝ)) (1 / 2) → 𝓕 f ξ = 0)
    (t : ℝ) :
    f t = ∫ ξ in (-(1 / 2 : ℝ))..(1 / 2), Complex.exp (2 * π * t * ξ * I) * 𝓕 f ξ := by
  have h := fourier_fourier_apply f (-t)
  rw [neg_neg] at h
  rw [← h, SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul]
  have hzero : ∀ v ∉ Icc (-(1 / 2 : ℝ)) (1 / 2),
      Complex.exp (↑(-2 * π * v * -t) * I) • (𝓕 f) v = 0 := fun v hv => by
    rw [hf v hv, smul_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
    intervalIntegral.integral_of_le (by norm_num), integral_Icc_eq_integral_Ioc]
  refine setIntegral_congr_fun measurableSet_Ioc fun v _ => ?_
  rw [smul_eq_mul]
  push_cast
  ring_nf

theorem ofReal_sinc_pi_mul_sub (n t : ℝ) :
    ((Real.sinc (π * (n - t)) : ℝ) : ℂ) =
      if t - n = 0 then 1 else ((Real.sin (π * (t - n)) / (π * (t - n)) : ℝ) : ℂ) := by
  by_cases h : t - n = 0
  · have : π * (n - t) = 0 := by rw [show n - t = -(t - n) by ring, h]; simp
    simp [this, h]
  · have : π * (n - t) ≠ 0 := by
      have : n - t ≠ 0 := fun h' => h (by linarith)
      exact mul_ne_zero Real.pi_ne_zero this
    rw [Real.sinc_of_ne_zero this]
    simp only [h, ↓reduceIte]
    rw [show π * (n - t) = -(π * (t - n)) by ring,
      Real.sin_neg, neg_div_neg_eq]

/-- **Nyquist–Shannon sampling theorem (Whittaker–Shannon interpolation formula).** Let `f` be a
complex Schwartz function on `ℝ` whose Fourier transform `𝓕 f ξ = ∫ f(x) e^{-2πixξ} dx` vanishes
outside `[-1/2, 1/2]`. Then for every real `t` the cardinal series
`∑_{n ∈ ℤ} f(n) sinc(π(n - t))` is summable over `ℤ` and
`f(t) = ∑_{n ∈ ℤ} f(n) sinc(π(n - t))`, with `sinc x = sin x / x` and `sinc 0 = 1`
(`Real.sinc`) (C. E. Shannon, *Communication in the presence of noise*, Proc. IRE 37 (1949),
10–21, Theorem 1 and the interpolation series (7), with band `W = 1/2` and samples `1/(2W) = 1`
apart). This is the statement once recorded as wanted in `WantedExt.Analysis.NyquistShannonWanted`,
whose `sinc` agrees with `Real.sinc`. -/
theorem nyquist_shannon_sampling (f : 𝓢(ℝ, ℂ))
    (hf : ∀ ξ : ℝ, ξ ∉ Icc (-(1 / 2 : ℝ)) (1 / 2) → 𝓕 f ξ = 0) :
    ∀ t : ℝ,
      Summable (fun n : ℤ ↦ f (n : ℝ) * (Real.sinc (Real.pi * ((n : ℝ) - t)) : ℂ)) ∧
        f t =
          ∑' n : ℤ, f (n : ℝ) * (Real.sinc (Real.pi * ((n : ℝ) - t)) : ℂ) := by
  intro t
  have hs := summable_norm_int f
  refine ⟨Summable.of_norm_bounded hs fun n => ?_, ?_⟩
  · rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact Real.abs_sinc_le_one _)
  set g : ℤ → C(ℝ, ℂ) := fun n =>
    ⟨fun ξ => Complex.exp (2 * π * t * ξ * I) *
      (f n * Complex.exp (2 * π * ((-n : ℤ) : ℝ) * ξ * I)), by fun_prop⟩ with hg
  have hg_sum : Summable fun n : ℤ =>
      ‖(g n).restrict
        (⟨uIcc (-(1 / 2 : ℝ)) (1 / 2), isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ)‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) hs
    refine (ContinuousMap.norm_le _ (norm_nonneg _)).mpr fun x => ?_
    simp [g, Complex.norm_exp]
  rw [eq_intervalIntegral f hf t]
  rw [intervalIntegral.integral_congr_Ioo_of_le (by norm_num) (g := fun ξ => ∑' n : ℤ, g n ξ)
    (fun ξ hξ => by
      simp only [g, ContinuousMap.coe_mk]
      rw [fourier_eq_tsum f hf hξ, ← tsum_mul_left])]
  rw [← intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm hg_sum]
  refine tsum_congr fun n => ?_
  simp only [g, ContinuousMap.coe_mk]
  have : ∀ ξ : ℝ, Complex.exp (2 * π * t * ξ * I) *
      (f n * Complex.exp (2 * π * ((-n : ℤ) : ℝ) * ξ * I)) =
        f n * Complex.exp (2 * π * ((t - n : ℝ)) * ξ * I) := fun ξ => by
    rw [mul_left_comm, ← Complex.exp_add]
    push_cast
    ring_nf
  simp_rw [this]
  rw [intervalIntegral.integral_const_mul, integral_exp_two_pi_mul_I, ofReal_sinc_pi_mul_sub]

end MathlibExt.Analysis.Fourier.NyquistShannon
