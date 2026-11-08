/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!

# The Kac-Ward symbol and the Onsager dispersion relation

The `4 × 4` Fourier symbol of the Kac-Ward matrix and its determinant.

## i. Overview

After Fourier transform in both lattice directions, the Kac-Ward matrix becomes, at momentum
`(k₁, k₂)`, a `4 × 4` matrix indexed by the four directions. With `ω ^ 2 = i` its determinant is
`(1 + x²)² - x (1 - x²)(z₁ + z₁⁻¹ + z₂ + z₂⁻¹)`, `zⱼ = e^{i kⱼ}`, that is
`(1 + x²)² - 2x(1 - x²)(cos k₁ + cos k₂)`. At `x = tanh β` this equals
`(cosh² 2β - sinh 2β (cos k₁ + cos k₂)) / cosh⁴ β`, the integrand of Onsager's formula.

## ii. Key results

- `ons_KWsymbolMat` : the Kac-Ward symbol at `(z₁, z₂)`
- `ons_symbol_det_z` : the determinant of the symbol
- `ons_symbol_det_cos` : the determinant at `zⱼ = e^{i kⱼ}`
- `ons_dispersion_cosh` : the dispersion relation at `x = tanh β`

## iii. Table of contents

- A. The symbol
- B. Its determinant

## iv. References

- M. Kac and J. C. Ward, *A combinatorial solution of the two-dimensional Ising model*, Phys. Rev.
  88 (1952) 1332-1337
- L. Onsager, *Crystal statistics. I. A two-dimensional model with an order-disorder transition*,
  Phys. Rev. 65 (1944) 117-149

-/

@[expose] public section

namespace StatMech.Onsager

/-! ## A. The symbol -/

/-- The `4 × 4` Fourier symbol of `1 - ons_KWmat` at `zⱼ = e^{i kⱼ}`, rows and columns indexed by
the directions east, north, west, south. -/
noncomputable def ons_KWsymbolMat (x ω z₁ z₂ : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![ 1 - x*z₁,             -x*(-Complex.I*ω)*z₂, 0,                      -x*ω*z₂⁻¹ ;
      -x*ω*z₁,              1 - x*z₂,             -x*(-Complex.I*ω)*z₁⁻¹, 0 ;
      0,                    -x*ω*z₂,              1 - x*z₁⁻¹,             -x*(-Complex.I*ω)*z₂⁻¹ ;
      -x*(-Complex.I*ω)*z₁, 0,                    -x*ω*z₁⁻¹,              1 - x*z₂⁻¹ ]

/-! ## B. Its determinant -/

lemma ons_symbol_det_z (x ω z₁ z₂ : ℂ) (hω : ω^2 = Complex.I) (hz₁ : z₁ ≠ 0) (hz₂ : z₂ ≠ 0) :
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

lemma ons_symbol_det_cos (x k₁ k₂ : ℝ) :
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

lemma ons_dispersion_cosh (β c : ℝ) :
    (1 + Real.tanh β^2)^2 - 2*Real.tanh β*(1 - Real.tanh β^2)*c
      = (Real.cosh (2*β)^2 - Real.sinh (2*β)*c) / Real.cosh β^4 := by
  have hc : Real.cosh β ≠ 0 := (Real.cosh_pos β).ne'
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_two_mul, Real.cosh_two_mul]
  field_simp
  linear_combination (-(Real.sinh β * Real.cosh β * 2 * c)) * Real.cosh_sq_sub_sinh_sq β

end StatMech.Onsager
