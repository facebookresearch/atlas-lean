/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.StatisticalGenetics.LatentCausalVariable

@[expose] public section

open MeasureTheory ProbabilityTheory MathlibExt.Biology.StatisticalGenetics.LatentCausalVariable
open scoped ENNReal

namespace MathlibExtTest.Biology.StatisticalGenetics.LatentCausalVariable

/-! ### A non-vacuous model

`Ω = Fin 2` with the uniform measure, `π = ±1` (mean `0`, variance `1`, `E π⁴ = 1`, so
`κ_π = -2`), no non-mediated effects, and `q₁ = q₂ = 1` (both traits are the latent variable). -/

/-- The uniform probability measure on `Fin 2`. -/
noncomputable def μ2 : Measure (Fin 2) := (2⁻¹ : ℝ≥0∞) • Measure.count

instance : IsProbabilityMeasure μ2 :=
  ⟨by simpa [μ2] using ENNReal.inv_mul_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num)⟩

/-- Integration against `μ2` is averaging over the two outcomes. -/
theorem integral_μ2 (f : Fin 2 → ℝ) : ∫ ω, f ω ∂μ2 = (f 0 + f 1) / 2 := by
  simp only [μ2, integral_smul_measure, integral_count, Fin.sum_univ_two]
  norm_num
  ring

/-- The fair sign `π = ±1`. -/
def sgn : Fin 2 → ℝ := ![1, -1]

/-- The witness model. -/
noncomputable def D : Model μ2 where
  q1 := 1
  q2 := 1
  pi := sgn
  g1 := fun _ => 0
  g2 := fun _ => 0
  memLp_pi := MemLp.of_discrete
  memLp_g1 := MemLp.of_discrete
  memLp_g2 := MemLp.of_discrete
  indep := indepFun_const_right _ _
  symm_left := by simpa using IdentDistrib.refl (μ := μ2) aemeasurable_const
  symm_right := by simpa using IdentDistrib.refl (μ := μ2) aemeasurable_const
  integral_pi := by simp [integral_μ2, sgn]
  integral_pi_sq := by simp [integral_μ2, sgn]
  integral_alpha1_sq := by simp [integral_μ2, sgn]
  integral_alpha2_sq := by simp [integral_μ2, sgn]

theorem kurtosis_D : D.kurtosis = -2 := by
  simp [Model.kurtosis, D, integral_μ2, sgn]
  norm_num

/-- Equation 2 on the witness: `E(α₁³ α₂) = κ_π + 3 = 1`. -/
example : ∫ ω, D.alpha1 ω ^ 3 * D.alpha2 ω ∂μ2 = 1 := by
  rw [D.integral_alpha1_pow_three_mul_alpha2, kurtosis_D]
  simp [D]
  norm_num

/-- The same value by direct computation: `π⁴ = 1`. -/
example : ∫ ω, D.alpha1 ω ^ 3 * D.alpha2 ω ∂μ2 = 1 := by
  simp [Model.alpha1, Model.alpha2, D, integral_μ2, sgn]
  norm_num

/-- Here `E π⁴ = 1` attains the lower bound `E π⁴ ≥ 1`. -/
example : ∫ ω, D.pi ω ^ 4 ∂μ2 = 1 := by
  simp [D, integral_μ2, sgn]
  norm_num

/-! ### The genetic causality proportion -/

/-- `q₁ = 1/2`, `q₂ = 1/4`: `gcp = (log(1/4) - log(1/2)) / (log(1/4) + log(1/2)) = 1/3`. -/
example : gcp (1 / 2) (1 / 4) = 1 / 3 := by
  have h4 : Real.log (1 / 4 : ℝ) = 2 * Real.log (1 / 2) := by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.log_pow]
    norm_num
  have h2 : Real.log (1 / 2 : ℝ) ≠ 0 := by
    rw [one_div, Real.log_inv]
    exact neg_ne_zero.mpr (Real.log_pos (by norm_num)).ne'
  rw [gcp, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4), abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2),
    h4]
  field_simp
  ring

/-- With `q₁² ≥ q₂²` the gcp is nonnegative. -/
example : 0 ≤ gcp (1 / 2) (1 / 4) :=
  (gcp_nonneg_iff (by norm_num) (by norm_num) (by norm_num)).mpr (by norm_num)

/-- Equation 1: `q₂² / q₁² = (ρ²)^gcp`. -/
example : (((1 / 2 : ℝ) * (1 / 4)) ^ 2) ^ gcp (1 / 2) (1 / 4) = (1 / 4) ^ 2 / (1 / 2) ^ 2 :=
  rpow_gcp (by norm_num) (by norm_num) (by norm_num)

/-- Junk value outside the domain: for `|q₁| = |q₂| = 1` (`ρ² = 1`) the denominator vanishes and
`gcp = 0`. -/
example : gcp 1 (-1) = 0 := by
  simp [gcp]

end MathlibExtTest.Biology.StatisticalGenetics.LatentCausalVariable
