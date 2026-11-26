/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Analysis.Fourier.AiryKatoSmoothingIdentity

open MeasureTheory
open scoped SchwartzMap FourierTransform
open MathlibExt.Analysis.Fourier.AiryKatoSmoothingIdentityWanted

-- At time zero the normalization must recover the datum at the original spatial point.
example (u : 𝓢(ℝ, ℂ)) (x : ℝ) : AirySolution u 0 x = u x := by
  let p := 2 * Real.pi
  have hp : 0 < p := mul_pos zero_lt_two Real.pi_pos
  let g (y : ℝ) := Complex.exp (↑(-2 * Real.pi * y * -x) * Complex.I) * (𝓕 u) y
  have hinv : ∫ y, g y = u x := by
    have h := congrFun (u.continuous.fourierInv_fourier_eq u.integrable (𝓕 u).integrable) x
    rwa [Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul] at h
  have hphase (ξ : ℝ) : -2 * Real.pi * (ξ / p) * -x = x * ξ := by
    change -2 * Real.pi * (ξ / (2 * Real.pi)) * -x = _
    field_simp
  have hscale : (Real.sqrt p : ℂ) ^ 2 = (p : ℂ) := by exact_mod_cast Real.sq_sqrt hp.le
  have hs : (Real.sqrt p : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hp).ne'
  unfold AirySolution
  simp only [Complex.ofReal_zero, zero_mul, zero_add, Complex.ofReal_inv]
  change (Real.sqrt p : ℂ)⁻¹ * _ = _
  calc
    _ = (Real.sqrt p : ℂ)⁻¹ * ((Real.sqrt p : ℂ)⁻¹ * ∫ ξ, g (ξ / p)) := by
      congr 1
      rw [← integral_const_mul]
      apply integral_congr_ae
      refine .of_forall fun ξ => ?_
      dsimp only [g]
      rw [hphase, Complex.ofReal_mul, mul_comm Complex.I]
      exact mul_left_comm _ _ _
    _ = u x := by
      rw [Measure.integral_comp_div, abs_of_pos hp, Complex.real_smul, hinv]
      field_simp
      linear_combination -u x * hscale

example (u : 𝓢(ℝ, ℂ)) (x : ℝ) :
    (∫ t, ‖deriv (AirySolution u t) x‖ ^ 2) = (1 / 3 : ℝ) * ∫ y, ‖u y‖ ^ 2 :=
  (integral_norm_deriv_airySolution_sq_eq u x).2
