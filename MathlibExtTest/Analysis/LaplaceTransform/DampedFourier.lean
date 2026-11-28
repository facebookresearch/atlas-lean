/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.LaplaceTransform.DampedFourier

/-! # Tests for the one-sided Laplace–Fourier identity -/

open MeasureTheory MetaMathlibExt
open scoped FourierTransform Real

-- Unit damping of a constant at the nonzero frequency corresponding to angular frequency 1.
-- The independent improper-integral evaluation checks the sign and the factor of `2 * π`.
example :
    𝓕 ((Set.Ioi 0).indicator (fun t : ℝ ↦ (Real.exp (-t) : ℂ))) (1 / (2 * π)) =
      (1 + Complex.I)⁻¹ := by
  have hd : IntegrableOn (fun t : ℝ ↦ Complex.exp (-(1 : ℂ) * (t : ℂ))) (Set.Ioi 0) :=
    integrableOn_exp_mul_complex_Ioi (by norm_num) 0
  have hf : Integrable ((Set.Ioi 0).indicator
      (fun t : ℝ ↦ Real.exp (-(1 : ℝ) * t) • (1 : ℂ))) := by
    simpa only [← Complex.coe_smul, smul_eq_mul, mul_one, Complex.ofReal_exp,
      Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_one] using
      hd.integrable_indicator measurableSet_Ioi
  have hfreq : 2 * π * (1 / (2 * π)) = 1 := by
    field_simp [Real.pi_ne_zero]
  have hL : HasLaplace (fun _ ↦ (1 : ℂ)) (1 + Complex.I)
      (𝓕 ((Set.Ioi 0).indicator (fun t : ℝ ↦ (Real.exp (-t) : ℂ))) (1 / (2 * π))) := by
    simpa only [hfreq, Complex.ofReal_one, one_mul, neg_one_mul, ← Complex.coe_smul,
      smul_eq_mul, mul_one] using (hasLaplace_damped_fourier (σ := 1) hf).1 (1 / (2 * π))
  calc
    _ = laplace (fun _ ↦ (1 : ℂ)) (1 + Complex.I) := hL.2.symm
    _ = (1 + Complex.I)⁻¹ := by
      have hre : (-(1 + Complex.I)).re < 0 := by norm_num [Complex.neg_re, Complex.add_re]
      simp only [laplace, smul_eq_mul, mul_one]
      rw [integral_exp_mul_complex_Ioi hre]
      simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, neg_div_neg_eq, one_div]

-- With zero damping, the bound is the ordinary one-sided `L¹` norm, also for vector signals.
example {f : ℝ → ℂ × ℂ} (hf : IntegrableOn f (Set.Ioi 0)) (ξ : ℝ) :
    ‖laplace f (↑(2 * π * ξ) * Complex.I)‖ ≤ ∫ t : ℝ in Set.Ioi 0, ‖f t‖ := by
  have h0 : Integrable ((Set.Ioi 0).indicator (fun t : ℝ ↦ Real.exp (-(0 : ℝ) * t) • f t)) := by
    simpa only [neg_zero, zero_mul, Real.exp_zero, one_smul] using
      hf.integrable_indicator measurableSet_Ioi
  have hb := (hasLaplace_damped_fourier (σ := 0) h0).2.1 ξ
  simpa only [neg_zero, zero_mul, Real.exp_zero, one_smul, Complex.ofReal_zero, zero_add,
    norm_indicator_eq_indicator_norm, integral_indicator measurableSet_Ioi] using hb

-- A consumer with an `IntegrableOn` hypothesis can use angular frequency instead of cycles.
example {f : ℝ → ℂ × ℂ} {σ : ℝ}
    (hf : IntegrableOn (fun t : ℝ ↦ Real.exp (-σ * t) • f t) (Set.Ioi 0)) :
    Continuous (fun ω : ℝ ↦ laplace f ((σ : ℂ) + (ω : ℂ) * Complex.I)) := by
  have hc := (hasLaplace_damped_fourier (hf.integrable_indicator measurableSet_Ioi)).2.2
  have hfreq (ω : ℝ) : 2 * π * (ω / (2 * π)) = ω := by
    field_simp [Real.pi_ne_zero]
  simpa only [Function.comp_def, id_eq, hfreq] using
    hc.comp (continuous_id.div_const (2 * π))
