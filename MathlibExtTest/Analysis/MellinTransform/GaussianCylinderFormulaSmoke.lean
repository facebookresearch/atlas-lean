/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

import MathlibExt.Analysis.MellinTransform.Gaussian
import MathlibExt.Analysis.MellinTransform.GaussianContinuation
import Mathlib.Tactic.NormNum

/-!
# Gaussian Mellin values and parabolic-cylinder normalization

The positive-half-line Gaussian Mellin integral at `s = 2`, with scale `b = 1/2`, is `1`.
The tilted integral at zero tilt has the same value and agrees with `U(3/2,0) = 1`.
The Hermite case `U(-1/2,i) = exp(1/4)` tests the complex argument and the normalization
`U(a,z) = D(-a-1/2,z)`.

At `s = -1`, the zero-tilt meromorphic continuation has the nonzero value
`2^(-3/2) Γ(-1/2)`. The ordinary totalized product `Γ(-1) U(-3/2,0)` is zero. This endpoint
comparison concerns the meromorphic continuation and makes no Mellin-integrability claim
outside the positive real half-plane.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace GaussianCylinderFormulaSmoke

private theorem gamma_two : Complex.Gamma (2 : ℂ) = 1 := by
  norm_num

private theorem cylinder_three_halves_zero : Complex.parabolicCylinderU (3 / 2 : ℂ) 0 = 1 := by
  have h := Complex.Gamma_mul_parabolicCylinderU_zero_of_re_pos
    (2 : ℂ) (by norm_num)
  have harg : (2 : ℂ) - 1 / 2 = 3 / 2 := by norm_num
  have hpower : (2 : ℂ) / 2 - 1 = 0 := by norm_num
  have hhalf : (2 : ℂ) / 2 = 1 := by norm_num
  rw [gamma_two, harg, hpower, hhalf, Complex.cpow_zero, Complex.Gamma_one] at h
  simpa only [one_mul] using h

private theorem gamma_negative_half_ne_zero : Complex.Gamma (-1 / 2 : ℂ) ≠ 0 := by
  have hpos : Complex.Gamma (1 / 2 : ℂ) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by norm_num)
  have hshift := Complex.Gamma_add_one (-1 / 2 : ℂ) (by norm_num)
  have harg : (-1 / 2 : ℂ) + 1 = 1 / 2 := by norm_num
  rw [harg] at hshift
  intro hzero
  rw [hzero, mul_zero] at hshift
  exact hpos hshift

private theorem continuation_endpoint_ne_zero :
    Complex.gaussianLaplaceMellinContinuation 0 (-1) ≠ 0 := by
  rw [Complex.gaussianLaplaceMellinContinuation_zero_neg_one]
  exact mul_ne_zero
    (Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num : (2 : ℂ) ≠ 0)))
    gamma_negative_half_ne_zero

example : HasMellin (fun t : ℝ => (Real.exp (-(1 / 2) * t ^ 2) : ℂ)) (2 : ℂ) 1 := by
  have h := hasMellin_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num)
    (s := (2 : ℂ)) (by norm_num)
  norm_num only [Complex.cpow_one, Complex.Gamma_one] at h
  have hscale : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by
    rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  have hvalue : (1 / 2 : ℂ) * (1 / (1 / 2 : ℂ) * 1) = 1 := by
    simpa only [one_div, mul_one, inv_inv] using
      (inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0))
  simpa only [hscale, hvalue] using h

example : Complex.parabolicCylinderU (-1 / 2 : ℂ) Complex.I = Complex.exp (1 / 4 : ℂ) := by
  rw [Complex.parabolicCylinderU_neg_one_half]
  norm_num [pow_two, Complex.I_mul_I]

example : Complex.parabolicCylinderU (3 / 2 : ℂ) 0 = 1 ∧
    mellin (fun t : ℝ => Complex.exp (-(t : ℂ) ^ 2 / 2)) (2 : ℂ) = 1 := by
  refine ⟨cylinder_three_halves_zero, ?_⟩
  have h := Complex.mellin_gaussian_laplace_eq_parabolicCylinderU
    (2 : ℂ) 0 (by norm_num)
  have harg : (2 : ℂ) - 1 / 2 = 3 / 2 := by norm_num
  have hexp : Complex.exp ((0 : ℂ) ^ 2 / 4) = 1 := by
    rw [pow_two, zero_mul, zero_div, Complex.exp_zero]
  simpa only [hexp, gamma_two, harg, zero_mul, sub_zero, one_mul,
    cylinder_three_halves_zero] using h

example : MellinConvergent
    (fun t : ℝ => Complex.exp (-(t : ℂ) ^ 2 / 2 - Complex.I * (t : ℂ))) (2 : ℂ) :=
  mellinConvergent_gaussian_laplace (by norm_num)

example : Complex.gaussianLaplaceMellinContinuation 0 (-1) =
      (2 : ℂ) ^ (-3 / 2 : ℂ) * Complex.Gamma (-1 / 2) ∧
    Complex.gaussianLaplaceMellinContinuation 0 (-1) ≠ 0 ∧
    Complex.Gamma (-1 : ℂ) * Complex.parabolicCylinderU (-3 / 2) 0 = 0 := by
  refine ⟨Complex.gaussianLaplaceMellinContinuation_zero_neg_one,
    continuation_endpoint_ne_zero, ?_⟩
  have hGamma : Complex.Gamma (-1 : ℂ) = 0 := by
    simpa only [Nat.cast_one] using Complex.Gamma_neg_nat_eq_zero 1
  rw [hGamma, zero_mul]

end GaussianCylinderFormulaSmoke
