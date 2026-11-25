/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:
`benchmark/level2/ma_proofbench_l2_70.lean` (openbmb/ma-proofbench, commit
31bab4c78fd1b0c464e767d62e9202163d1e9029).
Copyright holder: OpenBMB. License: MIT. Authors: L. Pu et al. (MA-ProofBench).
The adapted portions are the Bernstein inequality statement and its documentation.

Copyright (c) 2026 OpenBMB

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Bernstein inequality for band-limited Schwartz functions

For a Schwartz function on the real line whose Fourier transform is supported in the unit ball,
the derivative is bounded on every $L^p$, $1 ≤ p ≤ ∞$, with a common constant.
-/

open MeasureTheory
open scoped FourierTransform ENNReal

namespace MathlibExt.Analysis.Fourier.BernsteinInequalityBandLimitedWanted

private theorem fourier_deriv_apply (f : SchwartzMap ℝ ℂ) (ξ : ℝ) :
    𝓕 (SchwartzMap.derivCLM ℂ ℂ f) ξ = (2 * Real.pi * Complex.I * ξ) * 𝓕 f ξ :=
  congrFun (Real.fourier_deriv f.integrable f.differentiable
    (SchwartzMap.derivCLM ℂ ℂ f).integrable) ξ

-- Cut off the differentiation multiplier outside the unit band.
private theorem exists_deriv_kernel :
    ∃ k : SchwartzMap ℝ ℂ, ∀ f : SchwartzMap ℝ ℂ,
      Function.support (fun ξ : ℝ => (𝓕 f) ξ) ⊆ Metric.ball (0 : ℝ) 1 →
      SchwartzMap.derivCLM ℂ ℂ f = SchwartzMap.convolution (.mul ℂ ℂ) k f := by
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  let χ : SchwartzMap ℝ ℂ := (b.hasCompactSupport.comp_left (g := Complex.ofRealCLM)
    (by simp)).toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff)
  refine ⟨SchwartzMap.derivCLM ℂ ℂ (𝓕⁻ χ), ?_⟩
  intro f hf
  apply (FourierTransform.fourierCLE ℂ (SchwartzMap ℝ ℂ)).injective
  simp only [FourierTransform.fourierCLE_apply]
  rw [SchwartzMap.fourier_convolution]
  ext ξ : 1
  simp only [fourier_deriv_apply, SchwartzMap.pairing_apply_apply, ContinuousLinearMap.mul_apply',
    FourierInvPair.fourier_fourierInv_eq]
  by_cases hξ : (𝓕 f) ξ = 0
  · simp [hξ]
  · have hb := b.one_of_mem_closedBall (Metric.ball_subset_closedBall (hf hξ))
    have hχ : χ ξ = 1 := by
      change (b ξ : ℂ) = 1
      simp [hb]
    simp [hχ]

-- Averaging translates against a probability measure is contractive in finite Lᵖ.
private theorem lintegral_translate_rpow_le (f : SchwartzMap ℝ ℂ) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {p : ℝ≥0∞} (hp : 1 ≤ p) (ht : p ≠ ∞) :
    (∫⁻ x : ℝ, (∫⁻ y, ‖f (x - y)‖ₑ ∂μ) ^ p.toReal) ≤ ∫⁻ x, ‖f x‖ₑ ^ p.toReal := by
  have hp₀ : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hr := ENNReal.toReal_pos hp₀ ht
  calc
    _ ≤ ∫⁻ x : ℝ, ∫⁻ y, ‖f (x - y)‖ₑ ^ p.toReal ∂μ := by
      apply lintegral_mono
      intro x
      have hm : AEStronglyMeasurable (fun y => f (x - y)) μ :=
        (f.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      have h := eLpNorm_le_eLpNorm_of_exponent_le (f := fun y => f (x - y)) (μ := μ) hp
      rw [eLpNorm_one_eq_lintegral_eNorm hm, eLpNorm_eq_lintegral_rpow_eNorm_toReal hp₀ ht hm] at h
      simpa only [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hr.ne', ENNReal.rpow_one] using
        ENNReal.rpow_le_rpow h hr.le
    _ = ∫⁻ y, ∫⁻ x : ℝ, ‖f (x - y)‖ₑ ^ p.toReal ∂volume ∂μ := by
      apply lintegral_lintegral_swap
      exact ((f.continuous.comp (continuous_fst.sub continuous_snd)).measurable.eNorm.pow_const
        p.toReal).aemeasurable
    _ = _ := by
      simp_rw [lintegral_sub_right_eq_self (fun x => ‖f x‖ₑ ^ p.toReal)]
      simp

-- Young's L¹–Lᵖ estimate for the fixed Schwartz kernel.
private theorem convolution_bound (k f : SchwartzMap ℝ ℂ) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (SchwartzMap.convolution (.mul ℂ ℂ) k f) p ≤ eLpNorm k 1 * eLpNorm f p := by
  let g := SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) k f
  change eLpNorm g p ≤ _
  by_cases ht : p = ∞
  · subst p
    rw [eLpNorm_exponent_top g.continuous.aestronglyMeasurable]
    apply eLpNormEssSup_le_of_ae_eNorm_bound
    apply Filter.Eventually.of_forall
    intro x
    rw [show g x = _ from SchwartzMap.convolution_apply _ k f x]
    simpa using eNorm_convolution_le (.mul ℂ ℂ) (p := 1) (q := ∞)
      k.continuous.aestronglyMeasurable f.continuous.aestronglyMeasurable x
  let ν : FiniteMeasure ℝ := ⟨volume.withDensity (fun y => ‖k y‖ₑ),
    isFiniteMeasure_withDensity k.integrable.hasFiniteIntegral.ne⟩
  let μ : Measure ℝ := ν.normalize
  have : IsProbabilityMeasure μ := ν.normalize.prop
  have hμ : (ν : Measure ℝ) = ν.mass • μ :=
    congrArg FiniteMeasure.toMeasure ν.self_eq_mass_smul_normalize
  have hmass : (ν.mass : ℝ≥0∞) = eLpNorm k 1 := by
    rw [FiniteMeasure.ennreal_mass,
      eLpNorm_one_eq_lintegral_eNorm k.continuous.aestronglyMeasurable]
    simp [ν]
  have hpoint (x : ℝ) : ‖g x‖ₑ ≤ ν.mass * ∫⁻ y, ‖f (x - y)‖ₑ ∂μ := by
    calc
      _ ≤ ∫⁻ y, ‖k y‖ₑ * ‖f (x - y)‖ₑ := by
        rw [show g x = _ from SchwartzMap.convolution_apply _ k f x, convolution_def]
        simpa using eNorm_integral_le_lintegral_eNorm (fun y => k y * f (x - y))
      _ = ∫⁻ y, ‖f (x - y)‖ₑ ∂(ν : Measure ℝ) := by
        exact (lintegral_withDensity_eq_lintegral_mul volume k.continuous.measurable.eNorm
          (f.continuous.comp (continuous_const.sub continuous_id)).measurable.eNorm).symm
      _ = _ := by rw [hμ, lintegral_smul_measure]; rfl
  have hp₀ : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hr := ENNReal.toReal_pos hp₀ ht
  have hpow : (∫⁻ x, ‖g x‖ₑ ^ p.toReal) ≤ (ν.mass : ℝ≥0∞) ^ p.toReal *
      ∫⁻ x, ‖f x‖ₑ ^ p.toReal := calc
    _ ≤ ∫⁻ x : ℝ, (ν.mass : ℝ≥0∞) ^ p.toReal * (∫⁻ y, ‖f (x - y)‖ₑ ∂μ) ^ p.toReal :=
      lintegral_mono fun x => (ENNReal.rpow_le_rpow (hpoint x) hr.le).trans_eq
        (ENNReal.mul_rpow_of_nonneg _ _ hr.le)
    _ ≤ _ := by
      rw [lintegral_const_mul' _ _ (ENNReal.rpow_lt_top_of_nonneg hr.le (by simp)).ne]
      exact mul_le_mul_right (lintegral_translate_rpow_le f μ hp ht) _
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hp₀ ht g.continuous.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_eNorm_toReal hp₀ ht f.continuous.aestronglyMeasurable]
  simpa only [one_div, ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr hr.le),
    ← ENNReal.rpow_mul, mul_inv_cancel₀ hr.ne', ENNReal.rpow_one, hmass] using
    ENNReal.rpow_le_rpow hpow (inv_nonneg.mpr hr.le)

/-- **Bernstein inequality for band-limited Schwartz functions.** For a Schwartz function
$f : \mathbb{R} \to \mathbb{C}$ write $\hat f(\xi) = \int_{\mathbb{R}} f(x) e^{-2\pi i x\xi}\,dx$
for its Fourier transform. There is a constant $C_0 > 0$ such that for every $p \in [1, \infty]$
and every Schwartz function $f : \mathbb{R} \to \mathbb{C}$ with $\hat f(\xi) = 0$ whenever
$|\xi| \ge 1$,
$$\|f'\|_{L^p(\mathbb{R})} \le C_0 \|f\|_{L^p(\mathbb{R})}.$$

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functional analysis; Linear
function spaces and their duals), `benchmark/level2/ma_proofbench_l2_70.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem exists_norm_deriv_toLp_le_of_support_fourier_subset_ball :
    ∃ C0 > 0, ∀ p : ENNReal,
      (1 : ENNReal) ≤ p  →
      ∀ f : SchwartzMap ℝ ℂ,
        Function.support (fun ξ : ℝ => (𝓕 f) ξ) ⊆ Metric.ball (0 : ℝ) 1 →
          ‖(SchwartzMap.derivCLM ℂ ℂ f).toLp p
              (MeasureTheory.volume : MeasureTheory.Measure ℝ)‖ ≤
            C0 * ‖f.toLp p (MeasureTheory.volume : MeasureTheory.Measure ℝ)‖ := by
  obtain ⟨k, hk⟩ := exists_deriv_kernel
  refine ⟨‖k.toLp 1 volume‖ + 1, by positivity, ?_⟩
  intro p hp f hf
  have : Fact (1 ≤ p) := ⟨hp⟩
  rw [hk f hf]
  calc
    _ ≤ ‖k.toLp 1 volume‖ * ‖f.toLp p volume‖ := by
      simp only [SchwartzMap.norm_toLp, ← ENNReal.toReal_mul]
      exact ENNReal.toReal_mono (ENNReal.mul_ne_top (k.memLp 1 volume).eLpNorm_ne_top
        (f.memLp p volume).eLpNorm_ne_top) (convolution_bound k f hp)
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (norm_nonneg _)

end MathlibExt.Analysis.Fourier.BernsteinInequalityBandLimitedWanted
