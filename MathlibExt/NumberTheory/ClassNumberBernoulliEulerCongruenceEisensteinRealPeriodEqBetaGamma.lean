/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Beta and Gamma values of the real Eisenstein period

The real period `∫ t in (0 : ℝ)..1, (1 - t ^ 3) ^ (-(2 / 3) : ℝ)` equals one third of
the Beta integral `Complex.betaIntegral (1 / 3) (1 / 3)`, equals
`Real.Gamma (1 / 3) ^ 3 / (2 * Real.pi * Real.sqrt 3)`, and equals
`(2 : ℝ) ^ (1 / 3 : ℝ) / (3 * Real.sqrt 3)` times
`Complex.betaIntegral (1 / 6) (1 / 2)`.

## Reference

Akihiro Goto, *Congruence Relations Connecting Tate-Shafarevich Groups with
Bernoulli-Hurwitz Numbers by Elliptic Gauss Sums in the Eisenstein Integers Case*, INTEGERS 26
(2026), Article A112, Lemma 1
(`integers-2026-A112-lem-1`).
-/

namespace MetaMathlibExt

private theorem rpow_cube_factor (t : ℝ) (ht : 0 < t) :
    (t ^ 3) ^ (-(2 / 3) : ℝ) * t ^ 2 = 1 := by
  have ht_nn : (0 : ℝ) ≤ t := le_of_lt ht
  have hpow : (t ^ 3) ^ (-(2 / 3) : ℝ) = t ^ ((-2 : ℝ)) := by
    rw [← Real.rpow_natCast t 3, ← Real.rpow_mul ht_nn]
    congr 1
    norm_num
  rw [hpow, ← Real.rpow_natCast t 2, ← Real.rpow_add ht]
  have hexp : (-2 : ℝ) + ((2 : ℕ) : ℝ) = 0 := by norm_num
  rw [hexp, Real.rpow_zero]

private theorem subst_eisenstein_beta :
    ∫ t in (0 : ℝ)..1, (1 - t ^ 3) ^ (-(2 / 3) : ℝ)
      = (1 / 3) * ∫ u in (0 : ℝ)..1, u ^ (-(2 / 3) : ℝ) * (1 - u) ^ (-(2 / 3) : ℝ) := by
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (f := fun t : ℝ => t ^ 3) (f' := fun t : ℝ => 3 * t ^ 2)
    (g := fun u : ℝ => (1 / 3) * (u ^ (-(2 / 3) : ℝ) * (1 - u) ^ (-(2 / 3) : ℝ)))
    (a := 0) (b := 1) (continuousOn_id.pow 3)
    (fun x _ => by simpa using hasDerivAt_pow 3 x) (fun x _ => by positivity)
  simp only [Function.comp_apply, show ((0 : ℝ) ^ 3) = 0 by norm_num,
    show ((1 : ℝ) ^ 3) = 1 by norm_num] at hsub
  have hRHS : ∫ u in (0 : ℝ)..1, (1 / 3) * (u ^ (-(2 / 3) : ℝ) * (1 - u) ^ (-(2 / 3) : ℝ))
      = (1 / 3) * ∫ u in (0 : ℝ)..1, u ^ (-(2 / 3) : ℝ) * (1 - u) ^ (-(2 / 3) : ℝ) :=
    intervalIntegral.integral_const_mul _ _
  rw [hRHS] at hsub
  rw [← hsub]
  symm
  apply intervalIntegral.integral_congr_ae
  filter_upwards with t ht
  rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
  obtain ⟨htpos, -⟩ := Set.mem_Ioc.mp ht
  have h1 := rpow_cube_factor t htpos
  calc (1 / 3) * ((t ^ 3) ^ (-(2 / 3) : ℝ) * (1 - t ^ 3) ^ (-(2 / 3) : ℝ)) * (3 * t ^ 2)
      = ((t ^ 3) ^ (-(2 / 3) : ℝ) * t ^ 2) * (1 - t ^ 3) ^ (-(2 / 3) : ℝ) := by ring
    _ = (1 - t ^ 3) ^ (-(2 / 3) : ℝ) := by rw [h1, one_mul]

private theorem cast_real_beta :
    ((∫ u in (0 : ℝ)..1, u ^ (-(2 / 3) : ℝ) * (1 - u) ^ (-(2 / 3) : ℝ) : ℝ) : ℂ)
      = Complex.betaIntegral (1 / 3) (1 / 3) := by
  simp only [Complex.betaIntegral]
  rw [← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr_ae
  filter_upwards with u hu
  rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hu
  obtain ⟨hu0, hu1⟩ := Set.mem_Ioc.mp hu
  have hr : ((-(2 / 3) : ℝ) : ℂ) = (1 / 3 : ℂ) - 1 := by push_cast; ring
  rw [Complex.ofReal_mul, Complex.ofReal_cpow (le_of_lt hu0) (-(2 / 3)),
    Complex.ofReal_cpow (sub_nonneg.mpr hu1) (-(2 / 3)), Complex.ofReal_sub, Complex.ofReal_one,
    hr]

private theorem beta_gamma_third :
    Complex.betaIntegral (1 / 3) (1 / 3)
      = ((Real.Gamma (1 / 3) * Real.Gamma (1 / 3) / Real.Gamma (2 / 3) : ℝ) : ℂ) := by
  have h13 : ((1 / 3 : ℝ) : ℂ) = (1 / 3 : ℂ) := by
    rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  have hre : (0 : ℝ) < (1 / 3 : ℂ).re := by rw [← h13, Complex.ofReal_re]; norm_num
  have hsum : (1 / 3 : ℂ) + (1 / 3 : ℂ) = ((2 / 3 : ℝ) : ℂ) := by push_cast; ring
  rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ hre hre, hsum, ← h13, Complex.Gamma_ofReal,
    Complex.Gamma_ofReal, Complex.ofReal_div, Complex.ofReal_mul]

private theorem gamma_reflection_third :
    Real.Gamma (1 / 3) * Real.Gamma (2 / 3) = 2 * Real.pi / Real.sqrt 3 := by
  have hrefl := Real.Gamma_mul_Gamma_one_sub (1 / 3 : ℝ)
  rw [show (1 : ℝ) - 1 / 3 = 2 / 3 by norm_num, show Real.pi * (1 / 3 : ℝ) = Real.pi / 3 by ring,
    Real.sin_pi_div_three] at hrefl
  have hs3 : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  rw [hrefl]
  field_simp

private theorem beta_gamma_sixth_half :
    Complex.betaIntegral (1 / 6) (1 / 2)
      = ((Real.Gamma (1 / 6) * Real.sqrt Real.pi / Real.Gamma (2 / 3) : ℝ) : ℂ) := by
  have h16 : ((1 / 6 : ℝ) : ℂ) = (1 / 6 : ℂ) := by
    rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  have h12 : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by
    rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  have hre6 : (0 : ℝ) < (1 / 6 : ℂ).re := by rw [← h16, Complex.ofReal_re]; norm_num
  have hre2 : (0 : ℝ) < (1 / 2 : ℂ).re := by rw [← h12, Complex.ofReal_re]; norm_num
  have hsum : (1 / 6 : ℂ) + (1 / 2 : ℂ) = ((2 / 3 : ℝ) : ℂ) := by push_cast; ring
  rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ hre6 hre2, hsum, ← h16, ← h12,
    Complex.Gamma_ofReal, Complex.Gamma_ofReal, Complex.Gamma_ofReal, Real.Gamma_one_half_eq,
    Complex.ofReal_div, Complex.ofReal_mul]

private theorem gamma_dup_sixth :
    Real.Gamma (1 / 6) * Real.Gamma (2 / 3)
      = Real.Gamma (1 / 3) * (2 : ℝ) ^ ((2 / 3 : ℝ)) * Real.sqrt Real.pi := by
  have hdup := Real.Gamma_mul_Gamma_add_half (1 / 6 : ℝ)
  rw [show (1 / 6 : ℝ) + 1 / 2 = 2 / 3 by norm_num, show (2 : ℝ) * (1 / 6) = 1 / 3 by norm_num,
    show (1 : ℝ) - 1 / 3 = 2 / 3 by norm_num] at hdup
  exact hdup

/-- **Beta and Gamma values of the real Eisenstein period.** The real number
$\varpi_1 = \int_0^1 (1 - t^3)^{-2/3}\,dt$ satisfies
$\varpi_1 = \frac13 B(\frac13, \frac13) = \frac{\Gamma(1/3)^3}{2\pi\sqrt3}
= \frac{2^{1/3}}{3\sqrt3} B(\frac16, \frac12)$, where $B$ is the Beta function.

Source: Akihiro Goto, *Congruence Relations Connecting Tate-Shafarevich Groups with
Bernoulli-Hurwitz Numbers by Elliptic Gauss Sums in the Eisenstein Integers Case*, INTEGERS 26
(2026), Article A112, Lemma 1
(`integers-2026-A112-lem-1`). -/
public theorem eisensteinRealPeriod_eq_beta_gamma :
    let ϖ : ℝ := ∫ t in (0 : ℝ)..1, (1 - t ^ 3) ^ (-(2 / 3) : ℝ)
    (ϖ : ℂ) = Complex.betaIntegral (1 / 3) (1 / 3) / 3 ∧
      ϖ = Real.Gamma (1 / 3) ^ 3 / (2 * Real.pi * Real.sqrt 3) ∧
      (ϖ : ℂ) = (((2 : ℝ) ^ (1 / 3 : ℝ) / (3 * Real.sqrt 3) : ℝ) : ℂ) *
        Complex.betaIntegral (1 / 6) (1 / 2)
    := by
  change ((∫ t in (0 : ℝ)..1, (1 - t ^ 3) ^ (-(2 / 3) : ℝ) : ℝ) : ℂ)
      = Complex.betaIntegral (1 / 3) (1 / 3) / 3 ∧
    (∫ t in (0 : ℝ)..1, (1 - t ^ 3) ^ (-(2 / 3) : ℝ))
      = Real.Gamma (1 / 3) ^ 3 / (2 * Real.pi * Real.sqrt 3) ∧
    ((∫ t in (0 : ℝ)..1, (1 - t ^ 3) ^ (-(2 / 3) : ℝ) : ℝ) : ℂ)
      = (((2 : ℝ) ^ (1 / 3 : ℝ) / (3 * Real.sqrt 3) : ℝ) : ℂ) *
        Complex.betaIntegral (1 / 6) (1 / 2)
  have h13 : ((1 / 3 : ℝ) : ℂ) = (1 / 3 : ℂ) := by
    rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  have h1 : ((∫ t in (0 : ℝ)..1, (1 - t ^ 3) ^ (-(2 / 3) : ℝ) : ℝ) : ℂ)
      = Complex.betaIntegral (1 / 3) (1 / 3) / 3 := by
    calc ((∫ t in (0 : ℝ)..1, (1 - t ^ 3) ^ (-(2 / 3) : ℝ) : ℝ) : ℂ)
        = (((1 / 3) * ∫ u in (0 : ℝ)..1,
            u ^ (-(2 / 3) : ℝ) * (1 - u) ^ (-(2 / 3) : ℝ) : ℝ) : ℂ) := by
          rw [subst_eisenstein_beta]
      _ = ((1 / 3 : ℝ) : ℂ) * Complex.betaIntegral (1 / 3) (1 / 3) := by
          rw [Complex.ofReal_mul, cast_real_beta]
      _ = Complex.betaIntegral (1 / 3) (1 / 3) / 3 := by rw [h13]; ring
  have hϖ : (∫ t in (0 : ℝ)..1, (1 - t ^ 3) ^ (-(2 / 3) : ℝ))
      = Real.Gamma (1 / 3) * Real.Gamma (1 / 3) / Real.Gamma (2 / 3) / 3 := by
    apply Complex.ofReal_inj.mp
    rw [h1, beta_gamma_third]
    simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat]
  have ha : Real.Gamma (1 / 3) ≠ 0 := ne_of_gt (Real.Gamma_pos_of_pos (by norm_num))
  have hb : Real.Gamma (2 / 3) ≠ 0 := ne_of_gt (Real.Gamma_pos_of_pos (by norm_num))
  have hc : Real.Gamma (1 / 6) ≠ 0 := ne_of_gt (Real.Gamma_pos_of_pos (by norm_num))
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hs3 : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hsπ : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
  have hsq3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hpi_sq : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi :=
    Real.mul_self_sqrt (le_of_lt Real.pi_pos)
  have hrefl' : Real.Gamma (1 / 3) * Real.Gamma (2 / 3) * Real.sqrt 3 = 2 * Real.pi := by
    rw [gamma_reflection_third]
    field_simp
  have h2 : (∫ t in (0 : ℝ)..1, (1 - t ^ 3) ^ (-(2 / 3) : ℝ))
      = Real.Gamma (1 / 3) ^ 3 / (2 * Real.pi * Real.sqrt 3) := by
    rw [hϖ, div_div, div_eq_div_iff (mul_ne_zero hb (by norm_num))
      (mul_ne_zero (mul_ne_zero (by norm_num) hπ) hs3)]
    linear_combination (-(Real.sqrt 3 * Real.Gamma (1 / 3) ^ 2)) * hrefl' +
      (Real.Gamma (1 / 3) ^ 3 * Real.Gamma (2 / 3)) * hsq3
  have hrpow : (2 : ℝ) ^ ((1 / 3 : ℝ)) * (2 : ℝ) ^ ((2 / 3 : ℝ)) = 2 := by
    rw [← Real.rpow_add (by norm_num), show (1 / 3 : ℝ) + 2 / 3 = 1 by norm_num, Real.rpow_one]
  have hc' : Real.Gamma (1 / 6)
      = Real.Gamma (1 / 3) * (2 : ℝ) ^ ((2 / 3 : ℝ)) * Real.sqrt Real.pi / Real.Gamma (2 / 3) := by
    rw [eq_div_iff hb]
    exact gamma_dup_sixth
  have hX : ((Real.Gamma (1 / 3) * (2 : ℝ) ^ ((2 / 3 : ℝ)) * Real.sqrt Real.pi /
      Real.Gamma (2 / 3)) *
      Real.sqrt Real.pi / Real.Gamma (2 / 3))
      = (Real.Gamma (1 / 3) * (2 : ℝ) ^ ((2 / 3 : ℝ)) * (Real.sqrt Real.pi * Real.sqrt Real.pi)) /
        (Real.Gamma (2 / 3) * Real.Gamma (2 / 3)) := by
    rw [div_mul_eq_mul_div, div_div]
    ring
  have h3 : ((∫ t in (0 : ℝ)..1, (1 - t ^ 3) ^ (-(2 / 3) : ℝ) : ℝ) : ℂ)
      = (((2 : ℝ) ^ (1 / 3 : ℝ) / (3 * Real.sqrt 3) : ℝ) : ℂ) *
        Complex.betaIntegral (1 / 6) (1 / 2) := by
    have hreal : (∫ t in (0 : ℝ)..1, (1 - t ^ 3) ^ (-(2 / 3) : ℝ))
        = (2 : ℝ) ^ (1 / 3 : ℝ) / (3 * Real.sqrt 3) *
          (Real.Gamma (1 / 6) * Real.sqrt Real.pi / Real.Gamma (2 / 3)) := by
      rw [hϖ, hc', div_div, hX, div_mul_div_comm, div_eq_div_iff (mul_ne_zero hb (by norm_num))
        (mul_ne_zero (mul_ne_zero (by norm_num) hs3) (mul_ne_zero hb hb))]
      linear_combination (-3 * Real.Gamma (1 / 3) * Real.Gamma (2 / 3) * Real.sqrt Real.pi *
        Real.sqrt Real.pi) * hrpow +
        (-6 * Real.Gamma (1 / 3) * Real.Gamma (2 / 3)) * hpi_sq +
        (3 * Real.Gamma (1 / 3) * Real.Gamma (2 / 3)) * hrefl'
    calc ((∫ t in (0 : ℝ)..1, (1 - t ^ 3) ^ (-(2 / 3) : ℝ) : ℝ) : ℂ)
        = ((((2 : ℝ) ^ (1 / 3 : ℝ) / (3 * Real.sqrt 3) *
          (Real.Gamma (1 / 6) * Real.sqrt Real.pi / Real.Gamma (2 / 3)) : ℝ)) : ℂ) :=
          congrArg _ hreal
      _ = (((2 : ℝ) ^ (1 / 3 : ℝ) / (3 * Real.sqrt 3) : ℝ) : ℂ) *
          Complex.betaIntegral (1 / 6) (1 / 2) := by
          rw [Complex.ofReal_mul, ← beta_gamma_sixth_half]
  exact ⟨h1, h2, h3⟩

end MetaMathlibExt
