/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace StatMech.Onsager

noncomputable def ons_KWsymbolMat (x ω z₁ z₂ : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![ 1 - x*z₁,              -x*(-Complex.I*ω)*z₂,   0,                      -x*ω*z₂⁻¹ ;
      -x*ω*z₁,               1 - x*z₂,               -x*(-Complex.I*ω)*z₁⁻¹, 0 ;
      0,                     -x*ω*z₂,                1 - x*z₁⁻¹,             -x*(-Complex.I*ω)*z₂⁻¹ ;
      -x*(-Complex.I*ω)*z₁,  0,                      -x*ω*z₁⁻¹,              1 - x*z₂⁻¹ ]

theorem ons_symbol_det_z (x ω z₁ z₂ : ℂ) (hω : ω^2 = Complex.I) (hz₁ : z₁ ≠ 0) (hz₂ : z₂ ≠ 0) :
    (ons_KWsymbolMat x ω z₁ z₂).det
      = (1 + x^2)^2 - x*(1 - x^2)*(z₁ + z₁⁻¹ + z₂ + z₂⁻¹) := by
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have hω4 : ω ^ 4 = -1 := by rw [show (4:ℕ) = 2 * 2 from rfl, pow_mul, hω, hI]
  have hI4 : Complex.I ^ 4 = 1 := by
    rw [show (4:ℕ) = 2 * 2 from rfl, pow_mul, hI]; ring
  rw [ons_KWsymbolMat, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix_apply, Fin.succAbove]
  field_simp [hz₁, hz₂]
  ring_nf
  rw [hω4, hω]
  ring_nf
  rw [hI4, hI]
  ring

theorem ons_symbol_det_cos (x k₁ k₂ : ℝ) :
    (ons_KWsymbolMat (x:ℂ) (Complex.exp (Complex.I*(Real.pi/4)))
        (Complex.exp (Complex.I*k₁)) (Complex.exp (Complex.I*k₂))).det
      = ((1 + (x:ℂ)^2)^2 - 2*x*(1 - (x:ℂ)^2)*((Real.cos k₁ : ℂ) + (Real.cos k₂ : ℂ))) := by
  have hω : (Complex.exp (Complex.I * ((Real.pi:ℂ)/4)))^2 = Complex.I := by
    rw [← Complex.exp_nat_mul]
    have harg : ((2:ℕ):ℂ) * (Complex.I * ((Real.pi:ℂ)/4)) = (Real.pi:ℂ)/2 * Complex.I := by
      push_cast; ring
    rw [harg, Complex.exp_pi_div_two_mul_I]
  have hcos : ∀ k : ℝ,
      Complex.exp (Complex.I * (k:ℂ)) + (Complex.exp (Complex.I * (k:ℂ)))⁻¹
        = 2 * (Real.cos k : ℂ) := by
    intro k
    have hneg : (Complex.exp (Complex.I * (k:ℂ)))⁻¹ = Complex.exp (-(Complex.I * (k:ℂ))) :=
      (Complex.exp_neg _).symm
    rw [hneg, Complex.ofReal_cos, Complex.two_cos, mul_comm Complex.I (k:ℂ), neg_mul]
  rw [ons_symbol_det_z (x:ℂ) _ _ _ hω (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)]
  linear_combination (-(x:ℂ) * (1 - (x:ℂ)^2)) * hcos k₁
    + (-(x:ℂ) * (1 - (x:ℂ)^2)) * hcos k₂

theorem ons_dispersion_cosh (β c : ℝ) :
    (1 + Real.tanh β^2)^2 - 2*Real.tanh β*(1 - Real.tanh β^2)*c
      = (Real.cosh (2*β)^2 - Real.sinh (2*β)*c) / Real.cosh β^4 := by
  have hc : Real.cosh β ≠ 0 := (Real.cosh_pos β).ne'
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_two_mul, Real.cosh_two_mul]
  field_simp
  linear_combination (-(Real.sinh β * Real.cosh β * 2 * c)) * Real.cosh_sq_sub_sinh_sq β

end StatMech.Onsager
