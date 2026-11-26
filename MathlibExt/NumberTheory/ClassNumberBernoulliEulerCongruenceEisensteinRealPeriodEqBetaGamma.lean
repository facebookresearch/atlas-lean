/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.NumberField.ClassNumber
public import MathlibExt.Analysis.Ramanujan.Part1Ch5Entry10bEuleriansymmetry
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.RingTheory.Binomial
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.JacobiSum.Basic
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import Mathlib.RingTheory.Trace.Defs
public import MathlibExt.NumberTheory.SlHurwitzNumbers
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
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

private theorem int_rpow_one_sub :
    IntervalIntegrable (fun t : ℝ => (1 - t) ^ (-(2 / 3) : ℝ)) MeasureTheory.volume 0 1 := by
  have hbase : IntervalIntegrable (fun x : ℝ => x ^ (-(2 / 3) : ℝ)) MeasureTheory.volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have h := hbase.comp_sub_left (1 : ℝ)
  rw [show (1 : ℝ) - 0 = 1 by norm_num, show (1 : ℝ) - 1 = 0 by norm_num] at h
  exact h.symm

private theorem cont_pow2_factor :
    ContinuousOn (fun t : ℝ => (1 + t + t ^ 2) ^ (-(2 / 3) : ℝ)) (Set.uIcc 0 1) := by
  refine ContinuousOn.rpow_const
    ((continuousOn_const.add continuousOn_id).add (continuousOn_id.pow 2)) (fun t ht => Or.inl ?_)
  rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
  obtain ⟨ht0, -⟩ := Set.mem_Icc.mp ht
  have hpos : (0 : ℝ) < 1 + t + t ^ 2 := by positivity
  exact ne_of_gt hpos

private theorem int_eisenstein_integrand :
    IntervalIntegrable (fun t : ℝ => (1 - t ^ 3) ^ (-(2 / 3) : ℝ)) MeasureTheory.volume 0 1 := by
  refine IntervalIntegrable.congr (fun t ht => ?_)
    (int_rpow_one_sub.mul_continuousOn cont_pow2_factor)
  rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
  obtain ⟨ht0, ht1⟩ := Set.mem_Ioc.mp ht
  have hfactor : (1 : ℝ) - t ^ 3 = (1 - t) * (1 + t + t ^ 2) := by ring
  rw [hfactor, Real.mul_rpow (sub_nonneg.mpr ht1) (by positivity : (0 : ℝ) ≤ 1 + t + t ^ 2)]

private theorem cont_beta_left :
    ContinuousOn (fun u : ℝ => (1 - u) ^ (-(2 / 3) : ℝ)) (Set.uIcc 0 (1 / 2)) := by
  refine ContinuousOn.rpow_const (continuousOn_const.sub continuousOn_id) (fun u hu => Or.inl ?_)
  rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hu
  obtain ⟨-, hu1⟩ := Set.mem_Icc.mp hu
  have hpos : (0 : ℝ) < 1 - u := by linarith
  exact ne_of_gt hpos

private theorem cont_beta_right :
    ContinuousOn (fun u : ℝ => u ^ (-(2 / 3) : ℝ)) (Set.uIcc (1 / 2) 1) := by
  refine ContinuousOn.rpow_const continuousOn_id (fun u hu => Or.inl ?_)
  rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] at hu
  obtain ⟨hu0, -⟩ := Set.mem_Icc.mp hu
  have hpos : (0 : ℝ) < u := by linarith
  exact ne_of_gt hpos

private theorem int_rpow_one_sub_right :
    IntervalIntegrable (fun u : ℝ => (1 - u) ^ (-(2 / 3) : ℝ)) MeasureTheory.volume
      (1 / 2) 1 := by
  have hbase : IntervalIntegrable (fun x : ℝ => x ^ (-(2 / 3) : ℝ)) MeasureTheory.volume
      0 (1 / 2) :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have h := hbase.comp_sub_left (1 : ℝ)
  rw [show (1 : ℝ) - 0 = 1 by norm_num, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at h
  exact h.symm

private theorem int_beta_integrand :
    IntervalIntegrable (fun u : ℝ => u ^ (-(2 / 3) : ℝ) * (1 - u) ^ (-(2 / 3) : ℝ))
      MeasureTheory.volume 0 1 := by
  have hleft : IntervalIntegrable (fun u : ℝ => u ^ (-(2 / 3) : ℝ) * (1 - u) ^ (-(2 / 3) : ℝ))
      MeasureTheory.volume 0 (1 / 2) :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).mul_continuousOn cont_beta_left
  have hright : IntervalIntegrable (fun u : ℝ => u ^ (-(2 / 3) : ℝ) * (1 - u) ^ (-(2 / 3) : ℝ))
      MeasureTheory.volume (1 / 2) 1 := by
    refine IntervalIntegrable.congr (fun u _ => ?_)
      (int_rpow_one_sub_right.mul_continuousOn cont_beta_right)
    exact mul_comm _ _
  exact hleft.trans hright

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
  have hcont_f : ContinuousOn (fun t : ℝ => t ^ 3) (Set.uIcc 0 1) := continuousOn_id.pow 3
  have hderiv : ∀ x ∈ Set.Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1),
      HasDerivWithinAt (fun t : ℝ => t ^ 3) (3 * x ^ 2) (Set.Ioi x) x := by
    intro x _
    simpa using (hasDerivAt_pow 3 x).hasDerivWithinAt
  have hcont_g : ContinuousOn (fun u : ℝ =>
      (1 / 3) * (u ^ (-(2 / 3) : ℝ) * (1 - u) ^ (-(2 / 3) : ℝ)))
      ((fun t : ℝ => t ^ 3) '' Set.Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1)) := by
    refine ContinuousOn.mono (s := Set.Ioo (0 : ℝ) 1) ?_ ?_
    · refine continuousOn_const.mul (ContinuousOn.mul ?_ ?_)
      · exact continuousOn_id.rpow_const (fun u hu => Or.inl (ne_of_gt hu.1))
      · refine ContinuousOn.rpow_const (continuousOn_const.sub continuousOn_id)
          (fun u hu => Or.inl ?_)
        exact ne_of_gt (sub_pos.mpr hu.2)
    · intro y hy
      obtain ⟨t, ht, rfl⟩ := hy
      rw [min_eq_left (by norm_num : (0 : ℝ) ≤ 1), max_eq_right (by norm_num : (0 : ℝ) ≤ 1),
        Set.mem_Ioo] at ht
      obtain ⟨ht0, ht1⟩ := ht
      refine Set.mem_Ioo.mpr ⟨?_, ?_⟩
      · exact pow_pos ht0 3
      · exact pow_lt_one₀ (le_of_lt ht0) ht1 (by norm_num)
  have himg_sub_uIcc : (fun t : ℝ => t ^ 3) '' Set.uIcc 0 1 ⊆ Set.uIcc 0 1 := by
    intro y hy
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hy ⊢
    obtain ⟨t, ht, rfl⟩ := hy
    obtain ⟨ht0, ht1⟩ := Set.mem_Icc.mp ht
    refine Set.mem_Icc.mpr ⟨?_, ?_⟩
    · exact pow_nonneg ht0 3
    · calc t ^ 3 ≤ 1 ^ 3 := pow_le_pow_left₀ ht0 ht1 3
        _ = 1 := one_pow 3
  have hint_g : MeasureTheory.IntegrableOn
      (fun u : ℝ => (1 / 3) * (u ^ (-(2 / 3) : ℝ) * (1 - u) ^ (-(2 / 3) : ℝ)))
      ((fun t : ℝ => t ^ 3) '' Set.uIcc 0 1) MeasureTheory.volume := by
    refine MeasureTheory.IntegrableOn.mono_set ?_ himg_sub_uIcc
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    have hfin : ‖(fun u : ℝ =>
        (1 / 3) * (u ^ (-(2 / 3) : ℝ) * (1 - u) ^ (-(2 / 3) : ℝ))) 0‖ₑ ≠ ⊤ := by
      have hr0 : (-(2 / 3) : ℝ) ≠ 0 := by norm_num
      simp [Real.zero_rpow hr0]
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ 1) hfin).mp
      (int_beta_integrand.const_mul (1 / 3))
  have hne : ∀ᵐ t : ℝ ∂MeasureTheory.volume, t ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simp only [not_ne_iff, Set.ofPred_eq_eq_singleton]
    exact Real.volume_singleton
  have hint_comp : MeasureTheory.IntegrableOn
      (fun x : ℝ => ((fun u : ℝ => (1 / 3) * (u ^ (-(2 / 3) : ℝ) * (1 - u) ^ (-(2 / 3) : ℝ))) ∘
        (fun t : ℝ => t ^ 3)) x * (3 * x ^ 2))
      (Set.uIcc 0 1) MeasureTheory.volume := by
    have hbase : MeasureTheory.IntegrableOn (fun t : ℝ => (1 - t ^ 3) ^ (-(2 / 3) : ℝ))
        (Set.uIcc 0 1) MeasureTheory.volume := by
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      have hfin : ‖(fun t : ℝ => (1 - t ^ 3) ^ (-(2 / 3) : ℝ)) 0‖ₑ ≠ ⊤ := by
        simp
      exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ 1) hfin).mp
        int_eisenstein_integrand
    refine MeasureTheory.Integrable.congr hbase ?_
    refine (MeasureTheory.ae_restrict_iff' measurableSet_uIcc).mpr ?_
    filter_upwards [hne] with t ht0 htU
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at htU
    obtain ⟨ht0', -⟩ := Set.mem_Icc.mp htU
    have htpos : (0 : ℝ) < t := lt_of_le_of_ne' ht0' ht0
    have h1 := rpow_cube_factor t htpos
    change (1 - t ^ 3) ^ (-(2 / 3) : ℝ) = (1 / 3) *
      ((t ^ 3) ^ (-(2 / 3) : ℝ) * (1 - t ^ 3) ^ (-(2 / 3) : ℝ)) * (3 * t ^ 2)
    calc (1 - t ^ 3) ^ (-(2 / 3) : ℝ)
        = ((t ^ 3) ^ (-(2 / 3) : ℝ) * t ^ 2) * (1 - t ^ 3) ^ (-(2 / 3) : ℝ) := by
          rw [h1, one_mul]
      _ = (1 / 3) * ((t ^ 3) ^ (-(2 / 3) : ℝ) * (1 - t ^ 3) ^ (-(2 / 3) : ℝ)) * (3 * t ^ 2) := by
          ring
  have hsub := intervalIntegral.integral_comp_mul_deriv'''
    (f := fun t : ℝ => t ^ 3) (f' := fun t : ℝ => 3 * t ^ 2)
    (g := fun u : ℝ => (1 / 3) * (u ^ (-(2 / 3) : ℝ) * (1 - u) ^ (-(2 / 3) : ℝ)))
    (a := 0) (b := 1) hcont_f hderiv hcont_g hint_g hint_comp
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
