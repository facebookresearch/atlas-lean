/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_LanglandsTunnell_HonestLDatum.lean`,
`Theorems/Thm_LanglandsTunnell_Converse_MellinUniqueness_eq_of_laplace_eq_of_boundedOnStrips.lean`
and
`P2M/Sol/S_LanglandsTunnell_Converse_MellinUniqueness_eq_of_laplace_eq_of_boundedOnStrips.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import MathlibExt.Analysis.Complex.BoundedOnStrips
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section

noncomputable section

open MeasureTheory
open Complex Filter Set
open scoped Real Topology FourierTransform ContDiff

namespace LanglandsTunnell.Converse.MellinUniqueness

private noncomputable def luqLap (ψ : ℝ → ℝ) (s : ℂ) : ℂ :=
  ∫ x : ℝ, cexp (-(s * (x : ℂ))) * ((ψ x : ℝ) : ℂ)

private theorem luqLap_deriv {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hsupp : HasCompactSupport ψ)
    (s : ℂ) : luqLap (deriv ψ) s = s * luqLap ψ s := by
  have hd : Differentiable ℝ ψ := (contDiff_infty_iff_deriv.1 hψ).1
  have hc : Continuous ψ := hψ.continuous
  have hc' : Continuous (deriv ψ) := (contDiff_infty_iff_deriv.1 hψ).2.continuous
  have hu : ∀ x : ℝ, HasDerivAt (fun x : ℝ => cexp (-(s * (x : ℂ))))
      (-s * cexp (-(s * (x : ℂ)))) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => -(s * (x : ℂ))) (-s) x := by
      have h__af := ((hasDerivAt_id x).ofReal_comp.const_mul s).neg
      simp at h__af
      exact h__af
    simpa [mul_comm] using h1.cexp
  have hv : ∀ x : ℝ, HasDerivAt (fun x : ℝ => ((ψ x : ℝ) : ℂ)) ((deriv ψ x : ℝ) : ℂ) x :=
    fun x => (hd x).hasDerivAt.ofReal_comp
  have hψC : HasCompactSupport (fun x : ℝ => ((ψ x : ℝ) : ℂ)) :=
    hsupp.comp_left Complex.ofReal_zero
  have hψ'C : HasCompactSupport (fun x : ℝ => ((deriv ψ x : ℝ) : ℂ)) :=
    hsupp.deriv.comp_left Complex.ofReal_zero
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun x : ℝ => cexp (-(s * (x : ℂ)))) (v := fun x : ℝ => ((ψ x : ℝ) : ℂ))
    (u' := fun x : ℝ => -s * cexp (-(s * (x : ℂ)))) (v' := fun x : ℝ => ((deriv ψ x : ℝ) : ℂ))
    (fun x _ => hu x) (fun x _ => hv x)
    ((by fun_prop : Continuous _).integrable_of_hasCompactSupport hψ'C.mul_left)
    ((by fun_prop : Continuous _).integrable_of_hasCompactSupport hψC.mul_left)
    ((by fun_prop : Continuous _).integrable_of_hasCompactSupport hψC.mul_left)
  unfold luqLap
  beta_reduce at key
  refine key.trans ?_
  simp only [neg_mul, integral_neg, neg_neg, mul_assoc]
  exact integral_const_mul s _

private theorem luqLap_norm_le {ψ : ℝ → ℝ} (hc : Continuous ψ) (hsupp : HasCompactSupport ψ)
    {S : ℝ} {s : ℂ} (hs : |s.re| ≤ S) :
    ‖luqLap ψ s‖ ≤ ∫ x : ℝ, Real.exp (S * |x|) * ‖ψ x‖ := by
  unfold luqLap
  refine norm_integral_le_of_norm_le ?_ (ae_of_all _ fun x => ?_)
  · exact (by fun_prop : Continuous _).integrable_of_hasCompactSupport hsupp.norm.mul_left
  · rw [norm_mul, Complex.norm_exp, Complex.norm_real]
    have hre : (-(s * (x : ℂ))).re = -(s.re * x) := by simp
    rw [hre]
    gcongr
    calc -(s.re * x) ≤ |s.re * x| := neg_le_abs _
      _ = |s.re| * |x| := abs_mul _ _
      _ ≤ S * |x| := by gcongr

private theorem luqLap_decay {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hsupp : HasCompactSupport ψ)
    (S : ℝ) : ∃ C : ℝ, ∀ s : ℂ, |s.re| ≤ S → ‖luqLap ψ s‖ * (1 + s.im ^ 2) ≤ C := by
  have h1 := contDiff_infty_iff_deriv.1 hψ
  have h2 := contDiff_infty_iff_deriv.1 h1.2
  refine ⟨(∫ x : ℝ, Real.exp (S * |x|) * ‖ψ x‖) +
    ∫ x : ℝ, Real.exp (S * |x|) * ‖deriv (deriv ψ) x‖, fun s hs => ?_⟩
  have e0 := luqLap_norm_le hψ.continuous hsupp hs
  have e2 := luqLap_norm_le h2.2.continuous hsupp.deriv.deriv hs
  have hsq : luqLap (deriv (deriv ψ)) s = s ^ 2 * luqLap ψ s := by
    rw [luqLap_deriv h1.2 hsupp.deriv, luqLap_deriv hψ hsupp]; ring
  rw [hsq, norm_mul, norm_pow] at e2
  have him : s.im ^ 2 ≤ ‖s‖ ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_im_le_norm s) 2
  calc ‖luqLap ψ s‖ * (1 + s.im ^ 2) ≤ ‖luqLap ψ s‖ * (1 + ‖s‖ ^ 2) := by gcongr
    _ = ‖luqLap ψ s‖ + ‖s‖ ^ 2 * ‖luqLap ψ s‖ := by ring
    _ ≤ _ := add_le_add e0 e2

private theorem luqLap_differentiable {ψ : ℝ → ℝ} (hc : Continuous ψ)
    (hsupp : HasCompactSupport ψ) : Differentiable ℂ (luqLap ψ) := by
  intro s₀
  have hψC : HasCompactSupport (fun x : ℝ => ((ψ x : ℝ) : ℂ)) :=
    hsupp.comp_left Complex.ofReal_zero
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure ℝ)) (x₀ := s₀) (s := Metric.ball s₀ 1)
    (F := fun (s : ℂ) (x : ℝ) => cexp (-(s * (x : ℂ))) * ((ψ x : ℝ) : ℂ))
    (F' := fun (s : ℂ) (x : ℝ) => -(x : ℂ) * cexp (-(s * (x : ℂ))) * ((ψ x : ℝ) : ℂ))
    (bound := fun x : ℝ => Real.exp ((|s₀.re| + 1) * |x|) * (|x| * ‖ψ x‖))
    (Metric.ball_mem_nhds s₀ one_pos)
    (Eventually.of_forall fun s => (by fun_prop : Continuous _).aestronglyMeasurable)
    ((by fun_prop : Continuous _).integrable_of_hasCompactSupport hψC.mul_left)
    ((by fun_prop : Continuous _).aestronglyMeasurable)
    ?_ ((by fun_prop : Continuous _).integrable_of_hasCompactSupport
      (hsupp.norm.mul_left (f := fun x : ℝ => |x|)).mul_left) ?_
  · exact key.2.differentiableAt
  · refine ae_of_all _ fun x s hs => ?_
    have hs' : |s.re| ≤ |s₀.re| + 1 := by
      have h1 : |(s - s₀).re| ≤ ‖s - s₀‖ := Complex.abs_re_le_norm _
      have h2 : ‖s - s₀‖ < 1 := by rwa [← dist_eq_norm, ← Metric.mem_ball]
      rw [Complex.sub_re] at h1
      have := abs_sub_abs_le_abs_sub s.re s₀.re
      linarith
    have hle : -(s.re * x) ≤ (|s₀.re| + 1) * |x| :=
      calc -(s.re * x) ≤ |s.re * x| := neg_le_abs _
        _ = |s.re| * |x| := abs_mul _ _
        _ ≤ (|s₀.re| + 1) * |x| := by gcongr
    have hnorm : ‖-(x : ℂ) * cexp (-(s * (x : ℂ))) * ((ψ x : ℝ) : ℂ)‖ =
        Real.exp (-(s.re * x)) * (|x| * ‖ψ x‖) := by
      rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Complex.norm_exp, Complex.norm_real,
        Real.norm_eq_abs]
      have hre : (-(s * (x : ℂ))).re = -(s.re * x) := by simp
      rw [hre]
      ring
    rw [hnorm]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hle) (by positivity)
  · refine ae_of_all _ fun x s _ => ?_
    have h1 : HasDerivAt (fun s : ℂ => -(s * (x : ℂ))) (-(x : ℂ)) s := by
      have h__af := (((hasDerivAt_id s).mul_const (x : ℂ)).neg)
      simp at h__af
      exact h__af
    have h2 := h1.cexp.mul_const ((ψ x : ℝ) : ℂ)
    have h3 : HasDerivAt (fun s : ℂ => cexp (-(s * (x : ℂ))) * ((ψ x : ℝ) : ℂ))
        (-(x : ℂ) * cexp (-(s * (x : ℂ))) * ((ψ x : ℝ) : ℂ)) s := by
      convert h2 using 1
      ring
    exact h3

private theorem luqLap_fourier (ψ : ℝ → ℝ) (σ w : ℝ) :
    𝓕 (fun x : ℝ => cexp (-((σ : ℂ) * (x : ℂ))) * ((ψ x : ℝ) : ℂ)) w =
      luqLap ψ (σ + 2 * π * w * I) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  unfold luqLap
  congr 1
  ext v
  rw [smul_eq_mul, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

private theorem luqIntegrable {F : ℝ → ℂ} (hF : Continuous F) {a C : ℝ} (ha : a ≠ 0)
    (hb : ∀ y : ℝ, ‖F y‖ * (1 + (a * y) ^ 2) ≤ C) : Integrable F := by
  refine Integrable.mono' ((integrable_inv_one_add_sq.comp_mul_left' ha).const_mul C)
    hF.aestronglyMeasurable (ae_of_all _ fun y => ?_)
  have hpos : 0 < 1 + (a * y) ^ 2 := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hpos]
  exact hb y

private theorem luqLine {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hsupp : HasCompactSupport ψ)
    (g : ℝ → ℂ) (Λ : ℂ → ℂ) (σ : ℝ)
    (h : ∀ s : ℂ, s.re = σ → Integrable (fun t : ℝ => g t * cexp (s * (t : ℂ))) ∧
      ∫ t : ℝ, g t * cexp (s * (t : ℂ)) = Λ s) :
    ∫ x : ℝ, ((ψ x : ℝ) : ℂ) * g x =
      ∫ ξ : ℝ, Λ (σ - 2 * π * ξ * I) * luqLap ψ (σ - 2 * π * ξ * I) := by
  set φ : ℝ → ℂ := fun x : ℝ => cexp (-((σ : ℂ) * (x : ℂ))) * ((ψ x : ℝ) : ℂ) with hφdef
  set G : ℝ → ℂ := fun x : ℝ => g x * cexp ((σ : ℂ) * (x : ℂ)) with hGdef
  have hG : Integrable G := (h σ (Complex.ofReal_re σ)).1
  have hcont : Continuous (luqLap ψ) := (luqLap_differentiable hψ.continuous hsupp).continuous
  obtain ⟨C, hC⟩ := luqLap_decay hψ hsupp |σ|
  have hFφ : 𝓕 φ = fun w : ℝ => luqLap ψ (σ + 2 * π * w * I) :=
    funext fun w => luqLap_fourier ψ σ w
  have hFiφ : 𝓕⁻ φ = fun w : ℝ => luqLap ψ (σ - 2 * π * w * I) := by
    funext w
    rw [Real.fourierInv_eq_fourier_neg, hFφ]
    dsimp only
    congr 1
    push_cast
    ring
  have hint1 : Integrable (𝓕 φ) := by
    rw [hFφ]
    refine luqIntegrable (hcont.comp (by fun_prop)) (mul_ne_zero two_ne_zero Real.pi_ne_zero)
      (C := C) fun y => ?_
    simpa using hC (σ + 2 * π * y * I) (by simp)
  have hint2 : Integrable (𝓕⁻ φ) := by
    rw [hFiφ]
    refine luqIntegrable (hcont.comp (by fun_prop)) (a := -(2 * π))
      (neg_ne_zero.2 (mul_ne_zero two_ne_zero Real.pi_ne_zero)) (C := C) fun y => ?_
    simpa using hC (σ - 2 * π * y * I) (by simp)
  have hφc : Continuous φ := by
    have := hψ.continuous
    fun_prop
  have hφi : Integrable φ :=
    hφc.integrable_of_hasCompactSupport (hsupp.comp_left Complex.ofReal_zero).mul_left
  have key := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
    (μ := volume) (ν := volume) (f := G) (g := 𝓕⁻ φ)
    Real.continuous_fourierChar continuous_inner hG hint2
  have key' : ∫ ξ : ℝ, 𝓕 G ξ * 𝓕⁻ φ ξ = ∫ x : ℝ, G x * 𝓕 (𝓕⁻ φ) x := by
    simp at key
    exact key
  rw [hφc.fourier_fourierInv_eq hφi hint1] at key'
  have hR : (fun x : ℝ => G x * φ x) = fun x : ℝ => ((ψ x : ℝ) : ℂ) * g x := by
    funext x
    simp only [hGdef, hφdef]
    have : cexp ((σ : ℂ) * (x : ℂ)) * cexp (-((σ : ℂ) * (x : ℂ))) = 1 := by
      rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
    calc g x * cexp ((σ : ℂ) * (x : ℂ)) * (cexp (-((σ : ℂ) * (x : ℂ))) * ((ψ x : ℝ) : ℂ))
        = (cexp ((σ : ℂ) * (x : ℂ)) * cexp (-((σ : ℂ) * (x : ℂ)))) * (((ψ x : ℝ) : ℂ) * g x) := by
          ring
      _ = ((ψ x : ℝ) : ℂ) * g x := by rw [this, one_mul]
  have hL : ∀ ξ : ℝ, 𝓕 G ξ = Λ (σ - 2 * π * ξ * I) := by
    intro ξ
    rw [Real.fourier_real_eq_integral_exp_smul, ← (h (σ - 2 * π * ξ * I) (by simp)).2]
    congr 1
    ext v
    simp only [hGdef, smul_eq_mul]
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  simp_rw [hL, hFiφ] at key'
  rw [hR] at key'
  exact key'.symm

private theorem luqShift (H : ℂ → ℂ) (hH : Differentiable ℂ H) (σ₁ σ₂ C : ℝ)
    (hb : ∀ s : ℂ, s.re ∈ Set.uIcc σ₂ σ₁ → ‖H s‖ * (1 + s.im ^ 2) ≤ C) :
    ∫ y : ℝ, H (σ₁ + y * I) = ∫ y : ℝ, H (σ₂ + y * I) := by
  have hint : ∀ σ : ℝ, σ ∈ Set.uIcc σ₂ σ₁ → Integrable fun y : ℝ => H (σ + y * I) := by
    intro σ hσ
    refine luqIntegrable (hH.continuous.comp (by fun_prop)) one_ne_zero (C := C) fun y => ?_
    simpa using hb (σ + y * I) (by simpa using hσ)
  have hhor : ∀ Y : ℝ, ‖∫ x : ℝ in σ₂..σ₁, H (x + Y * I)‖ ≤ C * (1 + Y ^ 2)⁻¹ * |σ₁ - σ₂| := by
    intro Y
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
    have hx' : x ∈ Set.uIcc σ₂ σ₁ := Set.uIoc_subset_uIcc hx
    have := hb (x + Y * I) (by simpa using hx')
    have hpos : 0 < 1 + Y ^ 2 := by positivity
    rw [← div_eq_mul_inv, le_div_iff₀ hpos]
    simpa using this
  have hlim0 : Tendsto (fun Y : ℝ => C * (1 + Y ^ 2)⁻¹ * |σ₁ - σ₂|) atTop (𝓝 0) := by
    have h1 : Tendsto (fun Y : ℝ => 1 + Y ^ 2) atTop atTop :=
      tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop two_ne_zero)
    have h2 := (tendsto_inv_atTop_zero.comp h1).const_mul C
    have h3 := h2.mul_const |σ₁ - σ₂|
    simpa using h3
  have htop : ∀ Y : ℝ, Tendsto (fun Y : ℝ => ∫ x : ℝ in σ₂..σ₁, H (x + Y * I)) atTop (𝓝 0) :=
    fun _ => squeeze_zero_norm hhor hlim0
  have hbot : Tendsto (fun Y : ℝ => ∫ x : ℝ in σ₂..σ₁, H (x + (-Y) * I)) atTop (𝓝 0) := by
    have hhor' : ∀ Y : ℝ, ‖∫ x : ℝ in σ₂..σ₁, H (x + (-Y) * I)‖
        ≤ C * (1 + Y ^ 2)⁻¹ * |σ₁ - σ₂| := by
      intro Y
      have := hhor (-Y)
      push_cast at this
      simpa using this
    exact squeeze_zero_norm hhor' hlim0
  have hv₁ : Tendsto (fun Y : ℝ => ∫ y : ℝ in -Y..Y, H (σ₁ + y * I)) atTop
      (𝓝 (∫ y : ℝ, H (σ₁ + y * I))) :=
    intervalIntegral_tendsto_integral (hint σ₁ Set.right_mem_uIcc) tendsto_neg_atTop_atBot
      tendsto_id
  have hv₂ : Tendsto (fun Y : ℝ => ∫ y : ℝ in -Y..Y, H (σ₂ + y * I)) atTop
      (𝓝 (∫ y : ℝ, H (σ₂ + y * I))) :=
    intervalIntegral_tendsto_integral (hint σ₂ Set.left_mem_uIcc) tendsto_neg_atTop_atBot
      tendsto_id
  have hrect : ∀ Y : ℝ, I * (∫ y : ℝ in -Y..Y, H (σ₁ + y * I)) -
      I * (∫ y : ℝ in -Y..Y, H (σ₂ + y * I)) =
      (∫ x : ℝ in σ₂..σ₁, H (x + Y * I)) - ∫ x : ℝ in σ₂..σ₁, H (x + (-Y) * I) := by
    intro Y
    have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn H ⟨σ₂, -Y⟩ ⟨σ₁, Y⟩
      hH.differentiableOn
    simp only [smul_eq_mul] at h
    push_cast at h ⊢
    linear_combination h
  have hlhs : Tendsto (fun Y : ℝ => I * (∫ y : ℝ in -Y..Y, H (σ₁ + y * I)) -
      I * (∫ y : ℝ in -Y..Y, H (σ₂ + y * I))) atTop
      (𝓝 (I * (∫ y : ℝ, H (σ₁ + y * I)) - I * ∫ y : ℝ, H (σ₂ + y * I))) :=
    (hv₁.const_mul I).sub (hv₂.const_mul I)
  have hrhs : Tendsto (fun Y : ℝ => (∫ x : ℝ in σ₂..σ₁, H (x + Y * I)) -
      ∫ x : ℝ in σ₂..σ₁, H (x + (-Y) * I)) atTop (𝓝 (0 - 0)) :=
    (htop 0).sub hbot
  rw [show (fun Y : ℝ => I * (∫ y : ℝ in -Y..Y, H (σ₁ + y * I)) -
      I * (∫ y : ℝ in -Y..Y, H (σ₂ + y * I))) = (fun Y : ℝ => (∫ x : ℝ in σ₂..σ₁, H (x + Y * I)) -
      ∫ x : ℝ in σ₂..σ₁, H (x + (-Y) * I)) from funext hrect] at hlhs
  have := tendsto_nhds_unique hlhs hrhs
  rw [sub_zero, sub_eq_zero] at this
  exact mul_left_cancel₀ Complex.I_ne_zero this

/-- Two continuous functions with the same Laplace transform, given by
a differentiable function bounded on strips, are equal. -/
theorem eq_of_laplace_eq_of_boundedOnStrips
    (g₁ g₂ : ℝ → ℂ) (hg₁ : Continuous g₁) (hg₂ : Continuous g₂)
    (c : ℝ) (Λ : ℂ → ℂ) (hΛ : Differentiable ℂ Λ) (hb : Complex.BoundedOnStrips Λ)
    (h₁ : ∀ s : ℂ, c < s.re →
      Integrable (fun t : ℝ => g₁ t * Complex.exp (s * (t : ℂ))) ∧ ∫ t : ℝ, g₁ t * Complex.exp (s *
        (t : ℂ)) = Λ s)
    (h₂ : ∀ s : ℂ, s.re < -c →
      Integrable (fun t : ℝ => g₂ t * Complex.exp (s * (t : ℂ))) ∧ ∫ t : ℝ, g₂ t * Complex.exp (s *
        (t : ℂ)) = Λ s) :
    g₁ = g₂ := by
  have hS : c < |c| + 1 := lt_of_le_of_lt (le_abs_self c) (lt_add_one _)
  refine (hg₁.ae_eq_iff_eq volume hg₂).1 ?_
  refine ae_eq_of_integral_contDiff_smul_eq hg₁.locallyIntegrable hg₂.locallyIntegrable ?_
  intro ψ hψ hsupp
  set S : ℝ := |c| + 1 with hSdef
  obtain ⟨Cψ, hCψ⟩ := luqLap_decay hψ hsupp S
  obtain ⟨M, hM⟩ := hb (-S) S
  set H : ℂ → ℂ := fun s => Λ s * luqLap ψ s with hHdef
  have hH : Differentiable ℂ H := hΛ.mul (luqLap_differentiable hψ.continuous hsupp)
  have hHb : ∀ s : ℂ, s.re ∈ Set.uIcc (-S) S → ‖H s‖ * (1 + s.im ^ 2) ≤ M * Cψ := by
    intro s hs
    have hS0 : 0 ≤ S := by positivity
    rw [Set.uIcc_of_le (by linarith), Set.mem_Icc] at hs
    have e1 := hM s hs.1 hs.2
    have e2 := hCψ s (abs_le.2 ⟨hs.1, hs.2⟩)
    have hM0 : 0 ≤ M := (norm_nonneg _).trans e1
    rw [hHdef, norm_mul, mul_assoc]
    exact mul_le_mul e1 e2 (by positivity) hM0
  have eshift := luqShift H hH S (-S) (M * Cψ) hHb
  have e1 := luqLine hψ hsupp g₁ Λ S fun s hs => h₁ s (by rw [hs]; exact hS)
  have e2 := luqLine hψ hsupp g₂ Λ (-S) fun s hs => h₂ s (by rw [hs]; linarith)
  have e3 : ∀ σ : ℝ, ∫ ξ : ℝ, Λ (σ - 2 * π * ξ * I) * luqLap ψ (σ - 2 * π * ξ * I) =
      ∫ x : ℝ, H (σ + ((-(2 * π) * x : ℝ) : ℂ) * I) := by
    intro σ
    congr 1
    funext ξ
    simp only [hHdef]
    congr 2 <;> (push_cast; ring)
  have hcm : ∀ σ : ℝ, ∫ x : ℝ, H (σ + ((-(2 * π) * x : ℝ) : ℂ) * I) =
      |(-(2 * π))⁻¹| • ∫ y : ℝ, H (σ + y * I) := by
    intro σ
    have h := Measure.integral_comp_mul_left (fun y : ℝ => H (σ + y * I)) (-(2 * π))
    beta_reduce at h
    exact h
  have key : ∫ x : ℝ, ((ψ x : ℝ) : ℂ) * g₁ x = ∫ x : ℝ, ((ψ x : ℝ) : ℂ) * g₂ x := by
    rw [e1, e2, e3, e3, hcm, hcm, eshift]
  exact key

end LanglandsTunnell.Converse.MellinUniqueness
