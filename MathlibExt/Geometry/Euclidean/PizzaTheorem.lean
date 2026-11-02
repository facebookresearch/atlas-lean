/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

open scoped BigOperators

namespace MetaMathlibExt

section

private noncomputable def pizza_q (c p : ℝ × ℝ) (φ : ℝ) : ℝ :=
  (p.1 - c.1) * Real.cos φ + (p.2 - c.2) * Real.sin φ

private noncomputable def pizza_rho (c p : ℝ × ℝ) (R φ : ℝ) : ℝ :=
  -(pizza_q c p φ) + Real.sqrt (R ^ 2 - ((p.1 - c.1) ^ 2 + (p.2 - c.2) ^ 2) + (pizza_q c p φ) ^ 2)

private lemma pizza_C_pos (c p : ℝ × ℝ) (R : ℝ)
    (hp : (p.1 - c.1) ^ 2 + (p.2 - c.2) ^ 2 < R ^ 2) :
    0 < R ^ 2 - ((p.1 - c.1) ^ 2 + (p.2 - c.2) ^ 2) := by linarith

private lemma pizza_sqrtArg_pos (c p : ℝ × ℝ) (R φ : ℝ)
    (hp : (p.1 - c.1) ^ 2 + (p.2 - c.2) ^ 2 < R ^ 2) :
    0 < R ^ 2 - ((p.1 - c.1) ^ 2 + (p.2 - c.2) ^ 2) + (pizza_q c p φ) ^ 2 := by
  have hC := pizza_C_pos c p R hp
  have hsq : 0 ≤ (pizza_q c p φ) ^ 2 := sq_nonneg _
  linarith

private lemma pizza_sqrtArg_nonneg (c p : ℝ × ℝ) (R φ : ℝ)
    (hp : (p.1 - c.1) ^ 2 + (p.2 - c.2) ^ 2 < R ^ 2) :
    0 ≤ R ^ 2 - ((p.1 - c.1) ^ 2 + (p.2 - c.2) ^ 2) + (pizza_q c p φ) ^ 2 :=
  le_of_lt (pizza_sqrtArg_pos c p R φ hp)

private lemma pizza_rho_pos (c p : ℝ × ℝ) (R φ : ℝ)
    (hp : (p.1 - c.1) ^ 2 + (p.2 - c.2) ^ 2 < R ^ 2) :
    0 < pizza_rho c p R φ := by
  unfold pizza_rho
  have h1 : (pizza_q c p φ) ^ 2 <
      (Real.sqrt (R ^ 2 - ((p.1 - c.1) ^ 2 + (p.2 - c.2) ^ 2) + (pizza_q c p φ) ^ 2)) ^ 2 := by
    rw [Real.sq_sqrt (pizza_sqrtArg_nonneg c p R φ hp)]
    linarith [pizza_C_pos c p R hp]
  have h2 : |pizza_q c p φ| <
      Real.sqrt (R ^ 2 - ((p.1 - c.1) ^ 2 + (p.2 - c.2) ^ 2)
        + (pizza_q c p φ) ^ 2) :=
    abs_lt_of_sq_lt_sq h1 (Real.sqrt_nonneg _)
  linarith [le_abs_self (pizza_q c p φ)]

private lemma pizza_ray_mem (c p : ℝ × ℝ) (R r φ : ℝ)
    (hp : (p.1 - c.1) ^ 2 + (p.2 - c.2) ^ 2 < R ^ 2) (hr : 0 ≤ r) :
    ((p.1 + r * Real.cos φ - c.1) ^ 2 + (p.2 + r * Real.sin φ - c.2) ^ 2 < R ^ 2) ↔
      r < pizza_rho c p R φ := by
  have harg := pizza_sqrtArg_nonneg c p R φ hp
  have hsq := Real.sq_sqrt harg
  have htrig := Real.cos_sq_add_sin_sq φ
  have hexpand : (p.1 + r * Real.cos φ - c.1) ^ 2 + (p.2 + r * Real.sin φ - c.2) ^ 2 - R ^ 2
      = r ^ 2 + 2 * r * pizza_q c p φ - (R ^ 2 - ((p.1 - c.1) ^ 2 + (p.2 - c.2) ^ 2)) := by
    unfold pizza_q
    nlinarith [htrig, sq_nonneg r, sq_nonneg (Real.cos φ), sq_nonneg (Real.sin φ)]
  set q := pizza_q c p φ with hq
  set S := Real.sqrt (R ^ 2 - ((p.1 - c.1) ^ 2 + (p.2 - c.2) ^ 2) + q ^ 2) with hS
  have hρ : pizza_rho c p R φ = -q + S := rfl
  have hfactor : r ^ 2 + 2 * r * q - (R ^ 2 - ((p.1 - c.1) ^ 2 + (p.2 - c.2) ^ 2))
      = (r - (-q + S)) * (r - (-q - S)) := by
    have hS2 : S ^ 2 = R ^ 2 - ((p.1 - c.1) ^ 2 + (p.2 - c.2) ^ 2) + q ^ 2 := hsq
    nlinarith [hS2]
  have hS_gt : |q| < S := by
    have h1 : q ^ 2 < S ^ 2 := by rw [hsq]; linarith [pizza_C_pos c p R hp]
    exact abs_lt_of_sq_lt_sq h1 (Real.sqrt_nonneg _)
  have hneg : r - (-q - S) > 0 := by
    have habs := abs_lt.mp hS_gt
    linarith [hr]
  constructor
  · intro h
    have hlt : r ^ 2 + 2 * r * q - (R ^ 2 - ((p.1 - c.1) ^ 2 + (p.2 - c.2) ^ 2)) < 0 := by linarith
    rw [hfactor] at hlt
    have hpos : 0 < r - (-q - S) := hneg
    rcases mul_neg_iff.mp hlt with ⟨h1, _⟩ | ⟨_, h2⟩
    · linarith
    · linarith
  · intro h
    have hlt : (r - (-q + S)) * (r - (-q - S)) < 0 := by
      apply mul_neg_of_neg_of_pos
      · rw [hρ] at h; linarith
      · exact hneg
    rw [← hfactor] at hlt
    linarith

private lemma pizza_q_add_pi (c p : ℝ × ℝ) (φ : ℝ) :
    pizza_q c p (φ + Real.pi) = -pizza_q c p φ := by
  unfold pizza_q
  rw [Real.cos_add_pi, Real.sin_add_pi]
  ring

private lemma pizza_rho_add_pi (c p : ℝ × ℝ) (R φ : ℝ) :
    pizza_rho c p R (φ + Real.pi) = pizza_q c p φ +
      Real.sqrt (R ^ 2 - ((p.1 - c.1) ^ 2 + (p.2 - c.2) ^ 2)
        + (pizza_q c p φ) ^ 2) := by
  unfold pizza_rho
  rw [pizza_q_add_pi]
  congr 1
  · ring
  · congr 1
    ring

private lemma pizza_rho_sq_add (c p : ℝ × ℝ) (R φ : ℝ)
    (hp : (p.1 - c.1) ^ 2 + (p.2 - c.2) ^ 2 < R ^ 2) :
    (pizza_rho c p R φ) ^ 2 + (pizza_rho c p R (φ + Real.pi)) ^ 2 =
      2 * (R ^ 2 - ((p.1 - c.1) ^ 2 + (p.2 - c.2) ^ 2)) + 4 * (pizza_q c p φ) ^ 2 := by
  have harg := pizza_sqrtArg_nonneg c p R φ hp
  have hsq := Real.sq_sqrt harg
  rw [pizza_rho_add_pi]
  unfold pizza_rho
  nlinarith [hsq]

-- 2q^2 identity
private lemma pizza_two_q_sq (c p : ℝ × ℝ) (φ : ℝ) :
    2 * (pizza_q c p φ) ^ 2 =
      ((p.1 - c.1) ^ 2 + (p.2 - c.2) ^ 2)
      + ((p.1 - c.1) ^ 2 - (p.2 - c.2) ^ 2) * Real.cos (2 * φ)
      + 2 * (p.1 - c.1) * (p.2 - c.2) * Real.sin (2 * φ) := by
  unfold pizza_q
  rw [Real.cos_two_mul, Real.sin_two_mul]
  have htrig := Real.cos_sq_add_sin_sq φ
  linear_combination 2 * (p.2 - c.2) ^ 2 * htrig

private lemma pizza_zeta_pow (n : ℕ) (hn : 2 ≤ n) :
    (Complex.exp ((2 * Real.pi / (n : ℝ) : ℝ) * Complex.I)) ^ n = 1 := by
  have hnR : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := by omega
    exact Nat.cast_pos.mpr this
  have harg : (n : ℂ) * (((2 * Real.pi / (n : ℝ) : ℝ)) * Complex.I)
      = 2 * (Real.pi : ℂ) * Complex.I := by
    have hnC : (n : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt hnR
    have h1 : (n : ℂ) * ((2 * Real.pi / (n : ℝ) : ℝ) : ℂ) = 2 * (Real.pi : ℂ) := by
      have hcast : ((2 * Real.pi / (n : ℝ) : ℝ) : ℂ) = 2 * (Real.pi : ℂ) / (n : ℂ) := by
        push_cast
        ring
      rw [hcast, mul_div_cancel₀ _ hnC]
    calc (n : ℂ) * (((2 * Real.pi / (n : ℝ) : ℝ)) * Complex.I)
        = ((n : ℂ) * ((2 * Real.pi / (n : ℝ) : ℝ) : ℂ)) * Complex.I := by ring
      _ = (2 * (Real.pi : ℂ)) * Complex.I := by rw [h1]
      _ = 2 * (Real.pi : ℂ) * Complex.I := by ring
  have h2 : Complex.exp ((n : ℂ) * (((2 * Real.pi / (n : ℝ) : ℝ)) * Complex.I)) = 1 := by
    rw [harg]
    exact Complex.exp_two_pi_mul_I
  have h3 := Complex.exp_nat_mul (((2 * Real.pi / (n : ℝ) : ℝ)) * Complex.I) n
  rw [h3] at h2
  simpa using h2

private lemma pizza_zeta_ne_one (n : ℕ) (hn : 2 ≤ n) :
    Complex.exp ((2 * Real.pi / (n : ℝ) : ℝ) * Complex.I) ≠ 1 := by
  intro hcon
  rw [Complex.exp_eq_one_iff] at hcon
  obtain ⟨m, hm⟩ := hcon
  have hnR : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := by omega
    exact Nat.cast_pos.mpr this
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  -- hm : ((2π/n : ℝ)) * I = m * (2 * π * I)  [with casts]
  have hcast : ((2 * Real.pi / (n : ℝ) : ℝ) : ℂ) * Complex.I
      = (((m : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
    have hm2 : (((2 * Real.pi / (n : ℝ) : ℝ)) : ℂ) * Complex.I
        = (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := hm
    have hm3 : (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
        = (((m : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [hm2, hm3]
  have hcancel := mul_right_cancel₀ Complex.I_ne_zero hcast
  have hreal : (2 * Real.pi / (n : ℝ)) = (m : ℝ) * (2 * Real.pi) := by
    exact Complex.ofReal_injective hcancel
  have hpi_ne : (2 : ℝ) * Real.pi ≠ 0 := by positivity
  have hm_eq : (m : ℝ) = 1 / (n : ℝ) := by
    field_simp at hreal ⊢
    nlinarith [hreal, hpi_ne, hnR.ne']
  have hm_pos : (0 : ℝ) < (m : ℝ) := by
    rw [hm_eq]
    positivity
  have hm_lt : (m : ℝ) < 1 := by
    rw [hm_eq]
    rw [div_lt_one hnR]
    have hnR2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hm0 : 0 < m := by exact_mod_cast hm_pos
  have hm1 : m < 1 := by exact_mod_cast hm_lt
  omega

private lemma pizza_geom_sum_zero (n : ℕ) (hn : 2 ≤ n) :
    ∑ j ∈ Finset.range n, (Complex.exp ((2 * Real.pi / (n : ℝ) : ℝ) * Complex.I)) ^ j = 0 := by
  have hne := pizza_zeta_ne_one n hn
  have hpow := pizza_zeta_pow n hn
  rw [geom_sum_eq hne]
  rw [hpow]
  simp

private lemma pizza_exp_term (n : ℕ) (γ : ℝ) (j : ℕ) :
    Complex.exp (((γ + 2 * Real.pi * (j : ℝ) / (n : ℝ) : ℝ)) * Complex.I)
      = Complex.exp (((γ : ℝ)) * Complex.I) *
        (Complex.exp ((2 * Real.pi / (n : ℝ) : ℝ) * Complex.I)) ^ j := by
  have hsplit : ((((γ + 2 * Real.pi * (j : ℝ) / (n : ℝ) : ℝ))) : ℂ) * Complex.I
      = ((γ : ℝ) : ℂ) * Complex.I + (j : ℂ) * ((((2 * Real.pi / (n : ℝ) : ℝ))) * Complex.I) := by
    push_cast
    ring
  rw [hsplit, Complex.exp_add, Complex.exp_nat_mul]

private lemma pizza_sum_cos (n : ℕ) (hn : 2 ≤ n) (γ : ℝ) :
    ∑ j ∈ Finset.range n, Real.cos (γ + 2 * Real.pi * (j : ℝ) / (n : ℝ)) = 0 := by
  have hzero : (∑ j ∈ Finset.range n,
      Complex.exp (((γ + 2 * Real.pi * (j : ℝ) / (n : ℝ) : ℝ)) * Complex.I)).re = 0 := by
    have hfactor : (∑ j ∈ Finset.range n,
        Complex.exp (((γ + 2 * Real.pi * (j : ℝ) / (n : ℝ) : ℝ)) * Complex.I))
        = Complex.exp (((γ : ℝ)) * Complex.I) *
          (∑ j ∈ Finset.range n, (Complex.exp ((2 * Real.pi / (n : ℝ) : ℝ) * Complex.I)) ^ j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [pizza_exp_term]
    rw [hfactor, pizza_geom_sum_zero n hn, mul_zero]
    rfl
  rw [Complex.re_sum] at hzero
  calc ∑ j ∈ Finset.range n, Real.cos (γ + 2 * Real.pi * (j : ℝ) / (n : ℝ))
      = ∑ j ∈ Finset.range n,
        (Complex.exp (((γ + 2 * Real.pi * (j : ℝ) / (n : ℝ) : ℝ)) * Complex.I)).re := by
        apply Finset.sum_congr rfl
        intro j _
        exact (Complex.exp_ofReal_mul_I_re _).symm
    _ = 0 := hzero

private lemma pizza_sum_sin (n : ℕ) (hn : 2 ≤ n) (γ : ℝ) :
    ∑ j ∈ Finset.range n, Real.sin (γ + 2 * Real.pi * (j : ℝ) / (n : ℝ)) = 0 := by
  have hzero : (∑ j ∈ Finset.range n,
      Complex.exp (((γ + 2 * Real.pi * (j : ℝ) / (n : ℝ) : ℝ)) * Complex.I)).im = 0 := by
    have hfactor : (∑ j ∈ Finset.range n,
        Complex.exp (((γ + 2 * Real.pi * (j : ℝ) / (n : ℝ) : ℝ)) * Complex.I))
        = Complex.exp (((γ : ℝ)) * Complex.I) *
          (∑ j ∈ Finset.range n, (Complex.exp ((2 * Real.pi / (n : ℝ) : ℝ) * Complex.I)) ^ j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [pizza_exp_term]
    rw [hfactor, pizza_geom_sum_zero n hn, mul_zero]
    rfl
  rw [Complex.im_sum] at hzero
  calc ∑ j ∈ Finset.range n, Real.sin (γ + 2 * Real.pi * (j : ℝ) / (n : ℝ))
      = ∑ j ∈ Finset.range n,
        (Complex.exp (((γ + 2 * Real.pi * (j : ℝ) / (n : ℝ) : ℝ)) * Complex.I)).im := by
        apply Finset.sum_congr rfl
        intro j _
        exact (Complex.exp_ofReal_mul_I_im _).symm
    _ = 0 := hzero

private lemma pizza_q_continuous (c p : ℝ × ℝ) : Continuous (pizza_q c p) := by
  unfold pizza_q
  fun_prop

private lemma pizza_rho_continuous (c p : ℝ × ℝ) (R : ℝ) :
    Continuous (pizza_rho c p R) := by
  have hq := pizza_q_continuous c p
  have hneg : Continuous (fun φ => -pizza_q c p φ) := hq.neg
  have harg : Continuous (fun φ => R ^ 2
      - ((p.1 - c.1) ^ 2 + (p.2 - c.2) ^ 2) + (pizza_q c p φ) ^ 2) :=
    (continuous_const.add continuous_const).add (hq.pow 2)
  have hsqrt : Continuous (fun φ => Real.sqrt (R ^ 2
      - ((p.1 - c.1) ^ 2 + (p.2 - c.2) ^ 2) + (pizza_q c p φ) ^ 2)) :=
    Real.continuous_sqrt.comp harg
  have := hneg.add hsqrt
  unfold pizza_rho
  exact this

private lemma pizza_integral_cos_two (a b : ℝ) :
    ∫ φ in a..b, Real.cos (2 * φ)
      = (Real.sin (2 * b) - Real.sin (2 * a)) / 2 := by
  have h : ∫ φ in a..b, Real.cos (2 * φ)
      = (2 : ℝ)⁻¹ • ∫ u in a * 2..b * 2, Real.cos u := by
    have h2 := intervalIntegral.integral_comp_mul_right
      (fun u => Real.cos u) (c := 2) (a := a) (b := b) (by norm_num)
    simp only [mul_comm] at h2 ⊢
    exact h2
  rw [h, integral_cos]
  simp [smul_eq_mul, div_eq_mul_inv, mul_comm]

private lemma pizza_integral_sin_two (a b : ℝ) :
    ∫ φ in a..b, Real.sin (2 * φ)
      = (Real.cos (2 * a) - Real.cos (2 * b)) / 2 := by
  have h : ∫ φ in a..b, Real.sin (2 * φ)
      = (2 : ℝ)⁻¹ • ∫ u in a * 2..b * 2, Real.sin u := by
    have h2 := intervalIntegral.integral_comp_mul_right
      (fun u => Real.sin u) (c := 2) (a := a) (b := b) (by norm_num)
    simp only [mul_comm] at h2 ⊢
    exact h2
  rw [h, integral_sin]
  simp [smul_eq_mul, div_eq_mul_inv, mul_comm]

-- Pairing of antipodal sector integrals (pure analysis, no measure theory).
-- For any start `a` and width `L`: the sum of ρ²/2 integrals over [a,a+L) and
-- [a+π,a+π+L) equals the integral of R² + A·cos2φ + B·sin2φ over [a,a+L).
private lemma pizza_pair_integral (c p : ℝ × ℝ) (R a L : ℝ)
    (hp : (p.1 - c.1) ^ 2 + (p.2 - c.2) ^ 2 < R ^ 2) :
    (∫ φ in a..a + L, (pizza_rho c p R φ) ^ 2 / 2)
      + (∫ φ in a + Real.pi..a + Real.pi + L, (pizza_rho c p R φ) ^ 2 / 2)
      = ∫ φ in a..a + L,
        (R ^ 2 + ((p.1 - c.1) ^ 2 - (p.2 - c.2) ^ 2) * Real.cos (2 * φ)
          + 2 * (p.1 - c.1) * (p.2 - c.2) * Real.sin (2 * φ)) := by
  have hcont : Continuous (fun φ => (pizza_rho c p R φ) ^ 2 / 2) :=
    ((pizza_rho_continuous c p R).pow 2).div_const 2
  have hbase := intervalIntegral.integral_comp_add_right
    (fun φ => (pizza_rho c p R φ) ^ 2 / 2) (Real.pi)
    (a := a) (b := a + L)
  have heq : a + L + Real.pi = a + Real.pi + L := by ring
  rw [heq] at hbase
  have hshift : (∫ φ in a + Real.pi..a + Real.pi + L, (pizza_rho c p R φ) ^ 2 / 2)
      = ∫ φ in a..a + L, (pizza_rho c p R (φ + Real.pi)) ^ 2 / 2 :=
    hbase.symm
  have hadd : Continuous (fun φ : ℝ => φ + Real.pi) :=
    continuous_id.add continuous_const
  have hcont2 : Continuous (fun φ => (pizza_rho c p R (φ + Real.pi)) ^ 2 / 2) :=
    hcont.comp hadd
  rw [hshift, ← intervalIntegral.integral_add]
  · apply intervalIntegral.integral_congr
    intro φ _
    have h1 := pizza_rho_sq_add c p R φ hp
    have h2 := pizza_two_q_sq c p φ
    have hC : R ^ 2 - ((p.1 - c.1) ^ 2 + (p.2 - c.2) ^ 2)
        + 2 * (pizza_q c p φ) ^ 2
        = R ^ 2 + ((p.1 - c.1) ^ 2 - (p.2 - c.2) ^ 2) * Real.cos (2 * φ)
          + 2 * (p.1 - c.1) * (p.2 - c.2) * Real.sin (2 * φ) := by
      linarith [h2]
    nlinarith [h1, hC]
  · exact hcont.intervalIntegrable a (a + L)
  · exact hcont2.intervalIntegrable a (a + L)

private lemma pizza_sum_even {M : Type*} [AddCommMonoid M]
    (n : ℕ) (f : ℕ → M) :
    ∑ k ∈ Finset.filter (fun k => k % 2 = 0)
      (Finset.range (4 * n)), f k
      = ∑ j ∈ Finset.range (2 * n), f (2 * j) := by
  apply Finset.sum_bij (fun k _ => k / 2)
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
    omega
  · intro k1 hk1 k2 hk2 h
    simp only [Finset.mem_filter, Finset.mem_range] at hk1 hk2
    omega
  · intro j hj
    simp only [Finset.mem_range] at hj
    refine ⟨2 * j, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_range]
      constructor <;> omega
    · omega
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    have hk2 : 2 * (k / 2) = k := by omega
    rw [hk2]

private lemma pizza_sum_odd {M : Type*} [AddCommMonoid M]
    (n : ℕ) (f : ℕ → M) :
    ∑ k ∈ Finset.filter (fun k => k % 2 = 1)
      (Finset.range (4 * n)), f k
      = ∑ j ∈ Finset.range (2 * n), f (2 * j + 1) := by
  apply Finset.sum_bij (fun k _ => k / 2)
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
    omega
  · intro k1 hk1 k2 hk2 h
    simp only [Finset.mem_filter, Finset.mem_range] at hk1 hk2
    omega
  · intro j hj
    simp only [Finset.mem_range] at hj
    refine ⟨2 * j + 1, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_range]
      constructor <;> omega
    · omega
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    have hk2 : 2 * (k / 2) + 1 = k := by omega
    rw [hk2]

private lemma pizza_smul_eq_mul (r : ℝ) (z : ℂ) :
    r • z = (r : ℂ) * z := by
  apply Complex.ext
  · simp
  · simp

private lemma pizza_polar_re (r φ : ℝ) :
    (Complex.polarCoord.symm (r, φ)).re = r * Real.cos φ := by
  rw [Complex.polarCoord_symm_apply]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero]
  ring

private lemma pizza_polar_im (r φ : ℝ) :
    (Complex.polarCoord.symm (r, φ)).im = r * Real.sin φ := by
  rw [Complex.polarCoord_symm_apply]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.ofReal_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, zero_add]
  ring

private lemma pizza_arg_eq (r φ : ℝ) (hr : 0 < r)
    (hφ : φ ∈ Set.Ioc (-Real.pi) Real.pi) :
    Complex.arg ((r : ℂ) * ((Real.cos φ : ℂ)
      + (Real.sin φ : ℂ) * Complex.I)) = φ := by
  have hcos : ((Real.cos φ : ℂ)) = Complex.cos (φ : ℂ) :=
    Complex.ofReal_cos φ
  have hsin : ((Real.sin φ : ℂ)) = Complex.sin (φ : ℂ) :=
    Complex.ofReal_sin φ
  rw [hcos, hsin]
  exact Complex.arg_mul_cos_add_sin_mul_I hr hφ

private lemma pizza_arg_neg_pi (r : ℝ) (hr : 0 < r) :
    Complex.arg ((r : ℂ) * (((Real.cos (-Real.pi)) : ℂ)
      + ((Real.sin (-Real.pi)) : ℂ) * Complex.I)) = Real.pi := by
  have hcos : Real.cos (-Real.pi) = -1 := by
    rw [Real.cos_neg, Real.cos_pi]
  have hsin : Real.sin (-Real.pi) = 0 := by
    rw [Real.sin_neg, Real.sin_pi, neg_zero]
  rw [hcos, hsin]
  simp only [Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_zero,
    zero_mul, add_zero]
  rw [Complex.arg_real_mul (-1 : ℂ) hr, Complex.arg_neg_one]

private lemma pizza_norm_arg_eq (z : ℂ) :
    z = ((‖z‖ : ℝ) : ℂ) * (((Real.cos (Complex.arg z)) : ℂ)
      + ((Real.sin (Complex.arg z)) : ℂ) * Complex.I) := by
  have h := Complex.norm_mul_cos_add_sin_mul_I z
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin] at h
  exact h.symm

private lemma pizza_cone_eq (L : ℝ) (hL1 : 0 < L) (hL2 : L ≤ 2 * Real.pi) :
    {v : ℂ | ∃ r φ : ℝ, 0 ≤ r ∧ -Real.pi ≤ φ ∧ φ < -Real.pi + L ∧
      v = (r : ℂ) * ((Real.cos φ : ℂ) + (Real.sin φ : ℂ) * Complex.I)}
    = {z : ℂ | z = 0 ∨ Complex.arg z < -Real.pi + L ∨ Complex.arg z = Real.pi} := by
  ext z
  constructor
  · rintro ⟨r, φ, hr, h1, h2, rfl⟩
    rcases eq_or_ne r 0 with rfl | hrne
    · left
      simp only [Complex.ofReal_zero, zero_mul]
    · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hrne)
      rcases lt_or_eq_of_le h1 with hlt | heq
      · have hLe : -Real.pi + L ≤ Real.pi := by linarith [hL2]
        have hφ_lt : φ < Real.pi := lt_of_lt_of_le h2 hLe
        have hIoc : φ ∈ Set.Ioc (-Real.pi) Real.pi := ⟨hlt, le_of_lt hφ_lt⟩
        have harg := pizza_arg_eq r φ hrpos hIoc
        right
        left
        rw [harg]
        exact h2
      · have hφ_eq : φ = -Real.pi := heq.symm
        rw [hφ_eq] at h2 ⊢
        have harg := pizza_arg_neg_pi r hrpos
        right
        right
        exact harg
  · rintro (rfl | hlt | heq)
    · refine ⟨0, -Real.pi, le_rfl, le_rfl, by linarith [hL1], by simp⟩
    · refine ⟨‖z‖, Complex.arg z, norm_nonneg _,
        le_of_lt (Complex.neg_pi_lt_arg z), hlt, pizza_norm_arg_eq z⟩
    · have hcos_pi : Real.cos Real.pi = -1 := Real.cos_pi
      have hsin_pi : Real.sin Real.pi = 0 := Real.sin_pi
      have hcos_neg : Real.cos (-Real.pi) = -1 := by
        rw [Real.cos_neg, Real.cos_pi]
      have hsin_neg : Real.sin (-Real.pi) = 0 := by
        rw [Real.sin_neg, Real.sin_pi, neg_zero]
      have hfactor : (((Real.cos (Complex.arg z)) : ℂ)
          + ((Real.sin (Complex.arg z)) : ℂ) * Complex.I)
          = (((Real.cos (-Real.pi)) : ℂ)
            + ((Real.sin (-Real.pi)) : ℂ) * Complex.I) := by
        rw [heq, hcos_pi, hsin_pi, hcos_neg, hsin_neg]
      have hz := pizza_norm_arg_eq z
      rw [hfactor] at hz
      refine ⟨‖z‖, -Real.pi, norm_nonneg _, le_rfl, by linarith [hL1], hz⟩

private lemma pizza_cone_measurable (L : ℝ) (hL1 : 0 < L)
    (hL2 : L ≤ 2 * Real.pi) :
    MeasurableSet {v : ℂ | ∃ r φ : ℝ, 0 ≤ r ∧ -Real.pi ≤ φ ∧ φ < -Real.pi + L ∧
      v = (r : ℂ) * ((Real.cos φ : ℂ) + (Real.sin φ : ℂ) * Complex.I)} := by
  rw [pizza_cone_eq L hL1 hL2]
  have h0 : MeasurableSet ({0} : Set ℂ) := measurableSet_singleton 0
  have h1 : MeasurableSet {z : ℂ | Complex.arg z < -Real.pi + L} :=
    measurableSet_lt Complex.measurable_arg measurable_const
  have h2 : MeasurableSet {z : ℂ | Complex.arg z = Real.pi} :=
    measurableSet_eq_fun Complex.measurable_arg measurable_const
  have h_eq : {z : ℂ | z = 0 ∨ Complex.arg z < -Real.pi + L ∨ Complex.arg z = Real.pi}
      = (({0} ∪ {z : ℂ | Complex.arg z < -Real.pi + L})
        ∪ {z : ℂ | Complex.arg z = Real.pi}) := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_singleton_iff]
    constructor
    · intro h
      rcases h with rfl | hlt | heq
      · exact Or.inl (Or.inl rfl)
      · exact Or.inl (Or.inr hlt)
      · exact Or.inr heq
    · intro h
      rcases h with (rfl | hlt) | heq
      · exact Or.inl rfl
      · exact Or.inr (Or.inl hlt)
      · exact Or.inr (Or.inr heq)
  rw [h_eq]
  exact (h0.union h1).union h2

private lemma pizza_cone_mem_target (L : ℝ) (hL1 : 0 < L) (hL2 : L ≤ 2 * Real.pi)
    (r φ : ℝ) (hr : 0 < r) (hφ : φ ∈ Set.Ioo (-Real.pi) Real.pi) :
    (Complex.polarCoord.symm (r, φ) ∈ {v : ℂ | ∃ r φ : ℝ,
      0 ≤ r ∧ -Real.pi ≤ φ ∧ φ < -Real.pi + L ∧
      v = (r : ℂ) * ((Real.cos φ : ℂ) + (Real.sin φ : ℂ) * Complex.I)}
      ↔ φ < -Real.pi + L) := by
  rw [pizza_cone_eq L hL1 hL2]
  have hne : Complex.polarCoord.symm (r, φ) ≠ 0 := by
    have hnorm := Complex.norm_polarCoord_symm (r, φ)
    dsimp only at hnorm
    have habs : |r| = r := abs_of_pos hr
    rw [habs] at hnorm
    intro hzero
    rw [hzero] at hnorm
    simp only [norm_zero] at hnorm
    linarith [hr]
  have hIoc : φ ∈ Set.Ioc (-Real.pi) Real.pi :=
    ⟨hφ.1, le_of_lt hφ.2⟩
  have harg : Complex.arg (Complex.polarCoord.symm (r, φ)) = φ := by
    rw [Complex.polarCoord_symm_apply]
    have hcos : ((Real.cos φ : ℂ)) = Complex.cos (φ : ℂ) :=
      Complex.ofReal_cos φ
    have hsin : ((Real.sin φ : ℂ)) = Complex.sin (φ : ℂ) :=
      Complex.ofReal_sin φ
    rw [hcos, hsin]
    exact Complex.arg_mul_cos_add_sin_mul_I hr hIoc
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro h
    rcases h with h0 | hlt | heq
    · exact absurd h0 hne
    · rw [harg] at hlt
      exact hlt
    · rw [harg] at heq
      have hlt_pi : φ < Real.pi := hφ.2
      linarith [heq, hlt_pi, Real.pi_pos]
  · intro h
    right
    left
    rw [harg]
    exact h

private lemma pizza_ofReal_Ioo (f : ℝ → ℝ) (hf : Continuous f)
    (hnn : ∀ x, 0 ≤ f x) (a b : ℝ) (hab : a ≤ b) :
    (∫⁻ x in Set.Ioo a b, ENNReal.ofReal (f x))
      = ENNReal.ofReal (∫ x in a..b, f x) := by
  rw [MeasureTheory.setLIntegral_congr (α := ℝ) (μ := MeasureTheory.volume)
    (f := fun x => ENNReal.ofReal (f x)) (s := Set.Ioo a b) (t := Set.Ioc a b)
    MeasureTheory.Ioo_ae_eq_Ioc]
  have hInt : IntervalIntegrable f MeasureTheory.volume a b :=
    hf.intervalIntegrable a b
  have hInteg : MeasureTheory.IntegrableOn f (Set.Ioc a b) MeasureTheory.volume := by
    have hiff := intervalIntegrable_iff_integrableOn_Ioc_of_le hab
      (f := f) (μ := MeasureTheory.volume)
    exact hiff.mp hInt
  have hnn_ae : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioc a b)] f :=
    Filter.Eventually.of_forall (fun x => hnn x)
  have hconv := MeasureTheory.ofReal_integral_eq_lintegral_ofReal (μ :=
      MeasureTheory.volume.restrict (Set.Ioc a b)) (f := f) hInteg hnn_ae
  have hIoc_eq : (∫ x in Set.Ioc a b, f x ∂MeasureTheory.volume)
      = ∫ x in a..b, f x := by
    rw [intervalIntegral.integral_of_le hab]
  have hset : (∫ x, f x ∂(MeasureTheory.volume.restrict (Set.Ioc a b)))
      = ∫ x in a..b, f x := by
    have : (∫ x, f x ∂(MeasureTheory.volume.restrict (Set.Ioc a b)))
        = ∫ x in Set.Ioc a b, f x ∂MeasureTheory.volume := rfl
    rw [this, hIoc_eq]
  rw [hset] at hconv
  exact hconv.symm

private lemma pizza_inner_r (ρ : ℝ) (hρ : 0 < ρ) :
    (∫⁻ r in Set.Ioi (0 : ℝ), (Set.Iio ρ).indicator
      (fun r => ENNReal.ofReal r) r) = ENNReal.ofReal (ρ ^ 2 / 2) := by
  have hIoo : Set.Iio ρ ∩ Set.Ioi (0 : ℝ) = Set.Ioo 0 ρ := by
    ext r
    simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioi, Set.mem_Ioo]
    constructor
    · intro h
      exact ⟨h.2, h.1⟩
    · intro h
      exact ⟨h.2, h.1⟩
  rw [MeasureTheory.setLIntegral_indicator measurableSet_Iio, hIoo]
  rw [MeasureTheory.setLIntegral_congr (α := ℝ) (μ := MeasureTheory.volume)
    (f := fun r => ENNReal.ofReal r) (s := Set.Ioo 0 ρ) (t := Set.Ioc 0 ρ)
    MeasureTheory.Ioo_ae_eq_Ioc]
  have hcont : Continuous (fun r : ℝ => r) := continuous_id
  have hInt : IntervalIntegrable (fun r : ℝ => r) MeasureTheory.volume 0 ρ :=
    hcont.intervalIntegrable 0 ρ
  have hle : (0 : ℝ) ≤ ρ := le_of_lt hρ
  have hInteg : MeasureTheory.IntegrableOn (fun r : ℝ => r) (Set.Ioc 0 ρ)
      MeasureTheory.volume := by
    have hiff := intervalIntegrable_iff_integrableOn_Ioc_of_le hle
      (f := fun r : ℝ => r) (μ := MeasureTheory.volume)
    exact hiff.mp hInt
  have hnn : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioc 0 ρ)] (fun r : ℝ => r) := by
    have hmem : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioc 0 ρ)),
        r ∈ Set.Ioc (0 : ℝ) ρ :=
      MeasureTheory.ae_restrict_mem measurableSet_Ioc
    filter_upwards [hmem] with r hr
    simp only [Set.mem_Ioc] at hr
    exact le_of_lt hr.1
  have hconv := MeasureTheory.ofReal_integral_eq_lintegral_ofReal (μ :=
      MeasureTheory.volume.restrict (Set.Ioc 0 ρ)) (f := fun r : ℝ => r) hInteg hnn
  have hIoc_eq : (∫ r in Set.Ioc (0 : ℝ) ρ, r ∂MeasureTheory.volume)
      = ∫ r in (0 : ℝ)..ρ, r := by
    rw [intervalIntegral.integral_of_le hle]
  have hid : (∫ r in (0 : ℝ)..ρ, r) = ρ ^ 2 / 2 := by
    rw [integral_id]
    ring
  have hset : (∫ r, r ∂(MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) ρ)))
      = ρ ^ 2 / 2 := by
    have : (∫ r, r ∂(MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) ρ)))
        = ∫ r in Set.Ioc (0 : ℝ) ρ, r ∂MeasureTheory.volume := rfl
    rw [this, hIoc_eq, hid]
  rw [hset] at hconv
  exact hconv.symm

/-- Sector area lemma (Step 2 of the hint; the missing measure-theory piece).
For any start angle `a` and width `0 < L ≤ 2π`: the volume of the disc sector
`D ∩ Cone(p, a, L)` equals `ofReal` of the polar integral of `ρ²/2`.
Proved via ℂ transfer, translation, rotation (to dodge the polar branch cut),
`Complex.lintegral_comp_polarCoord_symm`, and Tonelli. -/
private lemma pizza_sector_area (c p : ℝ × ℝ) (R : ℝ) (hR : 0 < R)
    (hp : p ∈ {x : ℝ × ℝ | (x.1 - c.1) ^ 2 + (x.2 - c.2) ^ 2 < R ^ 2})
    (a L : ℝ) (hL1 : 0 < L) (hL2 : L ≤ 2 * Real.pi) :
    MeasureTheory.volume ({x : ℝ × ℝ | (x.1 - c.1) ^ 2 + (x.2 - c.2) ^ 2 < R ^ 2} ∩
      {x | ∃ r θ : ℝ, 0 ≤ r ∧ a ≤ θ ∧ θ < a + L ∧
        x = p + r • (Real.cos θ, Real.sin θ)})
    = ENNReal.ofReal (∫ φ in a..a + L, (pizza_rho c p R φ) ^ 2 / 2) := by
  have hp' : (p.1 - c.1) ^ 2 + (p.2 - c.2) ^ 2 < R ^ 2 := hp
  let P : ℂ := Complex.measurableEquivRealProd.symm p
  have hP_re : P.re = p.1 := rfl
  have hP_im : P.im = p.2 := rfl
  have hvol1 : MeasureTheory.volume
      ({x : ℝ × ℝ | (x.1 - c.1) ^ 2 + (x.2 - c.2) ^ 2 < R ^ 2} ∩
        {x | ∃ r θ : ℝ, 0 ≤ r ∧ a ≤ θ ∧ θ < a + L ∧
          x = p + r • (Real.cos θ, Real.sin θ)})
      = MeasureTheory.volume
        (Complex.measurableEquivRealProd ⁻¹'
          ({x : ℝ × ℝ | (x.1 - c.1) ^ 2 + (x.2 - c.2) ^ 2 < R ^ 2} ∩
            {x | ∃ r θ : ℝ, 0 ≤ r ∧ a ≤ θ ∧ θ < a + L ∧
              x = p + r • (Real.cos θ, Real.sin θ)})) :=
    (Complex.volume_preserving_equiv_real_prod.measure_preimage_equiv
      _).symm
  have hpre_inter : Complex.measurableEquivRealProd ⁻¹'
      ({x : ℝ × ℝ | (x.1 - c.1) ^ 2 + (x.2 - c.2) ^ 2 < R ^ 2} ∩
        {x | ∃ r θ : ℝ, 0 ≤ r ∧ a ≤ θ ∧ θ < a + L ∧
          x = p + r • (Real.cos θ, Real.sin θ)})
      = (Complex.measurableEquivRealProd ⁻¹'
        {x : ℝ × ℝ | (x.1 - c.1) ^ 2 + (x.2 - c.2) ^ 2 < R ^ 2})
        ∩ (Complex.measurableEquivRealProd ⁻¹'
          {x | ∃ r θ : ℝ, 0 ≤ r ∧ a ≤ θ ∧ θ < a + L ∧
            x = p + r • (Real.cos θ, Real.sin θ)}) := by
    rw [Set.preimage_inter]
  have hpre_disc : Complex.measurableEquivRealProd ⁻¹'
      {x : ℝ × ℝ | (x.1 - c.1) ^ 2 + (x.2 - c.2) ^ 2 < R ^ 2}
      = {z : ℂ | (z.re - c.1) ^ 2 + (z.im - c.2) ^ 2 < R ^ 2} := by
    ext z
    simp [Complex.measurableEquivRealProd_apply]
  have hsymm_dir : ∀ θ : ℝ,
      Complex.measurableEquivRealProd.symm
        (Real.cos θ, Real.sin θ)
        = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
    intro θ
    apply Complex.ext
    · simp only [Complex.measurableEquivRealProd_symm_apply,
        Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.mul_re, Complex.I_re, Complex.I_im]
      ring
    · simp only [Complex.measurableEquivRealProd_symm_apply,
        Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.mul_im, Complex.I_re, Complex.I_im]
      ring
  have hpre_cone : Complex.measurableEquivRealProd ⁻¹'
      {x | ∃ r θ : ℝ, 0 ≤ r ∧ a ≤ θ ∧ θ < a + L ∧
        x = p + r • (Real.cos θ, Real.sin θ)}
      = {z : ℂ | ∃ r θ : ℝ, 0 ≤ r ∧ a ≤ θ ∧ θ < a + L ∧
        z = P + (r : ℂ)
          * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I)} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨r, θ, hr, ha, hL, hx⟩
      refine ⟨r, θ, hr, ha, hL, ?_⟩
      have hz : z = Complex.measurableEquivRealProd.symm
          (Complex.measurableEquivRealProd z) := by simp
      rw [hx] at hz
      have hlin : Complex.measurableEquivRealProd.symm
          (p + r • (Real.cos θ, Real.sin θ))
          = P + r • Complex.measurableEquivRealProd.symm
            (Real.cos θ, Real.sin θ) := by
        change Complex.equivRealProdCLM.symm _ = _
        rw [map_add, map_smul]
        rfl
      rw [hlin, hsymm_dir, pizza_smul_eq_mul] at hz
      exact hz
    · rintro ⟨r, θ, hr, ha, hL, hz⟩
      refine ⟨r, θ, hr, ha, hL, ?_⟩
      have hP : Complex.measurableEquivRealProd P = p := by simp [P]
      have hdir : Complex.measurableEquivRealProd
          (((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I))
          = (Real.cos θ, Real.sin θ) := by
        ext
        · simp only [Complex.measurableEquivRealProd_apply,
            Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
            Complex.mul_re, Complex.I_re, Complex.I_im]
          ring
        · simp only [Complex.measurableEquivRealProd_apply,
            Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
            Complex.mul_im, Complex.I_re, Complex.I_im]
          ring
      have hlin : ∀ w1 w2 : ℂ,
          Complex.measurableEquivRealProd (w1 + w2)
            = Complex.measurableEquivRealProd w1
              + Complex.measurableEquivRealProd w2 := by
        intro w1 w2
        change Complex.equivRealProdCLM (w1 + w2) = _
        rw [map_add]
        rfl
      have hsmul : ∀ (rr : ℝ) (w : ℂ),
          Complex.measurableEquivRealProd (rr • w)
            = rr • Complex.measurableEquivRealProd w := by
        intro rr w
        change Complex.equivRealProdCLM (rr • w) = _
        rw [map_smul]
        rfl
      have hmul : (r : ℂ)
          * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I)
          = r • ((Real.cos θ : ℂ)
            + (Real.sin θ : ℂ) * Complex.I) := by
        rw [pizza_smul_eq_mul]
      rw [hz, hlin, hP, hmul, hsmul, hdir]
  rw [hvol1, hpre_inter, hpre_disc, hpre_cone]
  have hvol2 : MeasureTheory.volume
      ({z : ℂ | (z.re - c.1) ^ 2 + (z.im - c.2) ^ 2 < R ^ 2} ∩
        {z : ℂ | ∃ r θ : ℝ, 0 ≤ r ∧ a ≤ θ ∧ θ < a + L ∧
          z = P + (r : ℂ)
            * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I)})
      = MeasureTheory.volume
        ((fun w : ℂ => w + P) ⁻¹'
          ({z : ℂ | (z.re - c.1) ^ 2 + (z.im - c.2) ^ 2 < R ^ 2} ∩
            {z : ℂ | ∃ r θ : ℝ, 0 ≤ r ∧ a ≤ θ ∧ θ < a + L ∧
              z = P + (r : ℂ)
                * ((Real.cos θ : ℂ)
                  + (Real.sin θ : ℂ) * Complex.I)})) :=
    (MeasureTheory.measure_preimage_add_right
      MeasureTheory.volume P _).symm
  rw [hvol2]
  have htrans_inter : (fun w : ℂ => w + P) ⁻¹'
      ({z : ℂ | (z.re - c.1) ^ 2 + (z.im - c.2) ^ 2 < R ^ 2} ∩
        {z : ℂ | ∃ r θ : ℝ, 0 ≤ r ∧ a ≤ θ ∧ θ < a + L ∧
          z = P + (r : ℂ)
            * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I)})
      = ((fun w : ℂ => w + P) ⁻¹'
        {z : ℂ | (z.re - c.1) ^ 2 + (z.im - c.2) ^ 2 < R ^ 2})
        ∩ ((fun w : ℂ => w + P) ⁻¹'
          {z : ℂ | ∃ r θ : ℝ, 0 ≤ r ∧ a ≤ θ ∧ θ < a + L ∧
            z = P + (r : ℂ)
              * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I)}) := by
    rw [Set.preimage_inter]
  rw [htrans_inter]
  have htrans_disc : (fun w : ℂ => w + P) ⁻¹'
      {z : ℂ | (z.re - c.1) ^ 2 + (z.im - c.2) ^ 2 < R ^ 2}
      = {w : ℂ | (w.re + p.1 - c.1) ^ 2
        + (w.im + p.2 - c.2) ^ 2 < R ^ 2} := by
    ext w
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    have hre : (w + P).re = w.re + p.1 := by
      rw [Complex.add_re, hP_re]
    have him : (w + P).im = w.im + p.2 := by
      rw [Complex.add_im, hP_im]
    rw [hre, him]
  have htrans_cone : (fun w : ℂ => w + P) ⁻¹'
      {z : ℂ | ∃ r θ : ℝ, 0 ≤ r ∧ a ≤ θ ∧ θ < a + L ∧
        z = P + (r : ℂ)
          * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I)}
      = {w : ℂ | ∃ r θ : ℝ, 0 ≤ r ∧ a ≤ θ ∧ θ < a + L ∧
        w = (r : ℂ)
          * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I)} := by
    ext w
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨r, θ, hr, ha, hL, hz⟩
      refine ⟨r, θ, hr, ha, hL, ?_⟩
      have : w + P = P + (r : ℂ)
          * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I) := hz
      have hcomm : P + (r : ℂ)
          * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I)
          = (r : ℂ) * ((Real.cos θ : ℂ)
            + (Real.sin θ : ℂ) * Complex.I) + P := by
        ring
      rw [hcomm] at this
      exact add_right_cancel this
    · rintro ⟨r, θ, hr, ha, hL, hw⟩
      refine ⟨r, θ, hr, ha, hL, ?_⟩
      rw [hw]
      ring
  rw [htrans_disc, htrans_cone]
  let β : ℝ := a + Real.pi
  let u : Circle := Circle.exp (-β)
  have hu_coe : (u : ℂ) = Complex.exp ((-β : ℝ) * Complex.I) := rfl
  have hu_eq : (u : ℂ)
      = (Real.cos β : ℂ) - (Real.sin β : ℂ) * Complex.I := by
    rw [hu_coe, Complex.exp_ofReal_mul_I]
    simp [Real.cos_neg, Real.sin_neg, sub_eq_add_neg]
  have hu_norm : ‖(u : ℂ)‖ = 1 := Circle.norm_coe u
  let rot : ℂ ≃ₗᵢ[ℝ] ℂ := rotation u
  have hrot_apply : ∀ z : ℂ, rot z = (u : ℂ) * z := by
    intro z
    rfl
  let C : ℂ := Complex.measurableEquivRealProd.symm c
  have hC_re : C.re = c.1 := rfl
  have hC_im : C.im = c.2 := rfl
  let C2 : ℂ := (C - P) * (u : ℂ)
  have hnorm_eq : ∀ z : ℂ, ‖z‖ < R
      ↔ z.re ^ 2 + z.im ^ 2 < R ^ 2 := by
    intro z
    rw [Complex.norm_eq_sqrt_sq_add_sq]
    rw [Real.sqrt_lt (by positivity) (le_of_lt hR)]
  have hCP_re : (C - P).re = c.1 - p.1 := by
    simp [hC_re, hP_re, Complex.sub_re]
  have hCP_im : (C - P).im = c.2 - p.2 := by
    simp [hC_im, hP_im, Complex.sub_im]
  have hD1_eq : {w : ℂ | (w.re + p.1 - c.1) ^ 2
      + (w.im + p.2 - c.2) ^ 2 < R ^ 2}
      = Metric.ball (C - P) R := by
    ext w
    simp only [Set.mem_ofPred_eq, Metric.mem_ball, dist_eq_norm]
    rw [hnorm_eq]
    have hre : (w - (C - P)).re = w.re + p.1 - c.1 := by
      simp [Complex.sub_re, hCP_re]
      ring
    have him : (w - (C - P)).im = w.im + p.2 - c.2 := by
      simp [Complex.sub_im, hCP_im]
      ring
    rw [hre, him]
  have hD2_eq : {v : ℂ | (v.re - C2.re) ^ 2
      + (v.im - C2.im) ^ 2 < R ^ 2}
      = Metric.ball C2 R := by
    ext v
    simp only [Set.mem_ofPred_eq, Metric.mem_ball, dist_eq_norm]
    rw [hnorm_eq]
    have hre : (v - C2).re = v.re - C2.re := by
      simp [Complex.sub_re]
    have him : (v - C2).im = v.im - C2.im := by
      simp [Complex.sub_im]
    rw [hre, him]
  have hrot_disc : ∀ w : ℂ, w ∈ Metric.ball (C - P) R
      ↔ rot w ∈ Metric.ball C2 R := by
    intro w
    simp only [Metric.mem_ball, dist_eq_norm]
    have heq : rot w - C2 = (u : ℂ) * (w - (C - P)) := by
      rw [hrot_apply]
      simp only [C2]
      ring
    rw [heq, Complex.norm_mul, hu_norm, one_mul]
  have hrot_dir : ∀ θ : ℝ,
      (((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I) * (u : ℂ))
        = (Real.cos (θ - β) : ℂ)
          + (Real.sin (θ - β) : ℂ) * Complex.I := by
    intro θ
    rw [hu_eq]
    apply Complex.ext
    · simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
        Complex.I_re, Complex.I_im, Complex.sub_re, Complex.sub_im]
      rw [Real.cos_sub]
      ring
    · simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
        Complex.I_re, Complex.I_im, Complex.sub_re, Complex.sub_im]
      rw [Real.sin_sub]
      ring
  let u_inv : Circle := Circle.exp β
  have hu_inv_coe : (u_inv : ℂ)
      = (Real.cos β : ℂ) + (Real.sin β : ℂ) * Complex.I := by
    have h1 : (u_inv : ℂ) = Complex.exp ((β : ℝ) * Complex.I) := rfl
    rw [h1, Complex.exp_ofReal_mul_I]
  have hrot_dir_inv : ∀ φ : ℝ,
      (((Real.cos φ : ℂ) + (Real.sin φ : ℂ) * Complex.I)
        * (u_inv : ℂ))
        = (Real.cos (φ + β) : ℂ)
          + (Real.sin (φ + β) : ℂ) * Complex.I := by
    intro φ
    rw [hu_inv_coe]
    apply Complex.ext
    · simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
        Complex.I_re, Complex.I_im]
      rw [Real.cos_add φ β]
      ring
    · simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
        Complex.I_re, Complex.I_im]
      rw [Real.sin_add φ β]
      ring
  have hu_mul : (u_inv : ℂ) * (u : ℂ) = 1 := by
    have h1 : u_inv * u = 1 := by
      simp only [u_inv, u]
      rw [← Circle.exp_add]
      simp
    have h2 : ((u_inv * u : Circle) : ℂ) = (1 : Circle) := by
      rw [h1]
    simp only [Circle.coe_mul, Circle.coe_one] at h2
    exact h2
  have hβ_eq : β = a + Real.pi := rfl
  have hcone_corr : ∀ w : ℂ,
      (∃ r θ : ℝ, 0 ≤ r ∧ a ≤ θ ∧ θ < a + L ∧
        w = (r : ℂ)
          * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I))
      ↔ (∃ r φ : ℝ, 0 ≤ r ∧ -Real.pi ≤ φ ∧ φ < -Real.pi + L ∧
        rot w = (r : ℂ)
          * ((Real.cos φ : ℂ) + (Real.sin φ : ℂ) * Complex.I)) := by
    intro w
    constructor
    · rintro ⟨r, θ, hr, ha, hL, hw⟩
      refine ⟨r, θ - β, hr, ?_, ?_, ?_⟩
      · have : -Real.pi ≤ θ - β := by
          rw [hβ_eq]
          linarith [ha]
        exact this
      · have : θ - β < -Real.pi + L := by
          rw [hβ_eq]
          linarith [hL]
        exact this
      · rw [hw, hrot_apply]
        have h1 : (u : ℂ) * ((r : ℂ)
            * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I))
            = (r : ℂ) * ((((Real.cos θ : ℂ)
              + (Real.sin θ : ℂ) * Complex.I) * (u : ℂ))) := by
          ring
        rw [h1, hrot_dir]
    · rintro ⟨r, φ, hr, h1, h2, hw⟩
      have hθ1 : a ≤ φ + β := by
        rw [hβ_eq] at *
        linarith [h1]
      have hθ2 : φ + β < a + L := by
        rw [hβ_eq] at *
        linarith [h2]
      have hw_eq : w = (r : ℂ)
          * ((Real.cos (φ + β) : ℂ)
            + (Real.sin (φ + β) : ℂ) * Complex.I) := by
        have h2 : (u_inv : ℂ) * (rot w)
            = (r : ℂ) * ((((Real.cos φ : ℂ)
              + (Real.sin φ : ℂ) * Complex.I) * (u_inv : ℂ))) := by
          rw [hw]
          ring
        rw [hrot_dir_inv] at h2
        have h3 : (u_inv : ℂ) * (rot w) = w := by
          rw [hrot_apply]
          have : (u_inv : ℂ) * ((u : ℂ) * w)
              = ((u_inv : ℂ) * (u : ℂ)) * w := by ring
          rw [this, hu_mul, one_mul]
        rw [h3] at h2
        exact h2
      exact ⟨r, φ + β, hr, hθ1, hθ2, hw_eq⟩
  have hT_eq : ({w : ℂ | (w.re + p.1 - c.1) ^ 2
      + (w.im + p.2 - c.2) ^ 2 < R ^ 2} ∩
      {w : ℂ | ∃ r θ : ℝ, 0 ≤ r ∧ a ≤ θ ∧ θ < a + L ∧
        w = (r : ℂ)
          * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I)})
      = rot.toMeasurableEquiv ⁻¹'
        ({v : ℂ | (v.re - C2.re) ^ 2 + (v.im - C2.im) ^ 2 < R ^ 2} ∩
          {v : ℂ | ∃ r φ : ℝ, 0 ≤ r ∧ -Real.pi ≤ φ ∧ φ < -Real.pi + L ∧
            v = (r : ℂ)
              * ((Real.cos φ : ℂ)
                + (Real.sin φ : ℂ) * Complex.I)}) := by
    ext w
    simp only [Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_ofPred_eq,
      LinearIsometryEquiv.coe_toMeasurableEquiv]
    constructor
    · rintro ⟨hd, hc⟩
      have hd_ball : w ∈ Metric.ball (C - P) R := by
        rw [← hD1_eq]
        exact hd
      have hd2 : rot w ∈ Metric.ball C2 R :=
        (hrot_disc w).mp hd_ball
      have hd2_coord : ((rot w).re - C2.re) ^ 2
          + ((rot w).im - C2.im) ^ 2 < R ^ 2 := by
        have : rot w ∈ {v : ℂ | (v.re - C2.re) ^ 2
            + (v.im - C2.im) ^ 2 < R ^ 2} := by
          rw [hD2_eq]
          exact hd2
        exact this
      have hc2 : ∃ r φ : ℝ, 0 ≤ r ∧ -Real.pi ≤ φ ∧ φ < -Real.pi + L ∧
          rot w = (r : ℂ)
            * ((Real.cos φ : ℂ) + (Real.sin φ : ℂ) * Complex.I) :=
        (hcone_corr w).mp hc
      exact ⟨hd2_coord, hc2⟩
    · rintro ⟨hd, hc⟩
      have hd_ball : rot w ∈ Metric.ball C2 R := by
        have : rot w ∈ {v : ℂ | (v.re - C2.re) ^ 2
            + (v.im - C2.im) ^ 2 < R ^ 2} := hd
        rw [hD2_eq] at this
        exact this
      have hd1_ball : w ∈ Metric.ball (C - P) R :=
        (hrot_disc w).mpr hd_ball
      have hd1 : (w.re + p.1 - c.1) ^ 2
          + (w.im + p.2 - c.2) ^ 2 < R ^ 2 := by
        have : w ∈ {w : ℂ | (w.re + p.1 - c.1) ^ 2
            + (w.im + p.2 - c.2) ^ 2 < R ^ 2} := by
          rw [hD1_eq]
          exact hd1_ball
        exact this
      have hc1 : ∃ r θ : ℝ, 0 ≤ r ∧ a ≤ θ ∧ θ < a + L ∧
          w = (r : ℂ)
            * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I) :=
        (hcone_corr w).mpr hc
      exact ⟨hd1, hc1⟩
  have hmp : MeasureTheory.MeasurePreserving
      ⇑(rot.toMeasurableEquiv)
      MeasureTheory.volume MeasureTheory.volume :=
    LinearIsometryEquiv.measurePreserving rot
  have hvol3 : MeasureTheory.volume
      ({w : ℂ | (w.re + p.1 - c.1) ^ 2
        + (w.im + p.2 - c.2) ^ 2 < R ^ 2} ∩
        {w : ℂ | ∃ r θ : ℝ, 0 ≤ r ∧ a ≤ θ ∧ θ < a + L ∧
          w = (r : ℂ)
            * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I)})
      = MeasureTheory.volume
        ({v : ℂ | (v.re - C2.re) ^ 2 + (v.im - C2.im) ^ 2 < R ^ 2} ∩
          {v : ℂ | ∃ r φ : ℝ, 0 ≤ r ∧ -Real.pi ≤ φ ∧ φ < -Real.pi + L ∧
            v = (r : ℂ)
              * ((Real.cos φ : ℂ)
                + (Real.sin φ : ℂ) * Complex.I)}) := by
    rw [hT_eq]
    exact hmp.measure_preimage_equiv _
  rw [hvol3]
  have hDisc_meas : MeasurableSet
      {v : ℂ | (v.re - C2.re) ^ 2 + (v.im - C2.im) ^ 2 < R ^ 2} := by
    rw [hD2_eq]
    exact IsOpen.measurableSet Metric.isOpen_ball
  have hCone_meas : MeasurableSet
      {v : ℂ | ∃ r φ : ℝ, 0 ≤ r ∧ -Real.pi ≤ φ ∧ φ < -Real.pi + L ∧
        v = (r : ℂ) * ((Real.cos φ : ℂ) + (Real.sin φ : ℂ) * Complex.I)} :=
    pizza_cone_measurable L hL1 hL2
  have hT_meas : MeasurableSet
      ({v : ℂ | (v.re - C2.re) ^ 2 + (v.im - C2.im) ^ 2 < R ^ 2} ∩
        {v : ℂ | ∃ r φ : ℝ, 0 ≤ r ∧ -Real.pi ≤ φ ∧ φ < -Real.pi + L ∧
          v = (r : ℂ) * ((Real.cos φ : ℂ) + (Real.sin φ : ℂ) * Complex.I)}) :=
    hDisc_meas.inter hCone_meas
  set T : Set ℂ := ({v : ℂ | (v.re - C2.re) ^ 2 + (v.im - C2.im) ^ 2 < R ^ 2} ∩
      {v : ℂ | ∃ r φ : ℝ, 0 ≤ r ∧ -Real.pi ≤ φ ∧ φ < -Real.pi + L ∧
        v = (r : ℂ) * ((Real.cos φ : ℂ) + (Real.sin φ : ℂ) * Complex.I)})
    with hT_def
  have hvol_eq : MeasureTheory.volume T = ∫⁻ _, T.indicator 1 _ :=
    (MeasureTheory.lintegral_indicator_one hT_meas).symm
  have hpolar := Complex.lintegral_comp_polarCoord_symm (T.indicator 1)
  have hvol_target : MeasureTheory.volume T =
      ∫⁻ p in polarCoord.target,
        ENNReal.ofReal p.1 • T.indicator 1 (Complex.polarCoord.symm p) := by
    rw [hvol_eq, ← hpolar]
  have hdisc : ∀ r φ : ℝ, 0 ≤ r →
      (Complex.polarCoord.symm (r, φ) ∈
        {v : ℂ | (v.re - C2.re) ^ 2 + (v.im - C2.im) ^ 2 < R ^ 2}
        ↔ r < pizza_rho c p R (φ + β)) := by
    intro r φ hr
    have hrot_w : rot (Complex.polarCoord.symm (r, φ + β))
        = Complex.polarCoord.symm (r, φ) := by
      rw [hrot_apply, Complex.polarCoord_symm_apply,
        Complex.polarCoord_symm_apply]
      have hdir := hrot_dir (φ + β)
      have hψβ : φ + β - β = φ := by ring
      rw [hψβ] at hdir
      have hcomm : (u : ℂ) * ((r : ℂ) *
          (((Real.cos (φ + β)) : ℂ) + ((Real.sin (φ + β)) : ℂ) * Complex.I))
          = (r : ℂ) * (((((Real.cos (φ + β)) : ℂ)
            + ((Real.sin (φ + β)) : ℂ) * Complex.I)) * (u : ℂ)) := by
        ring
      rw [hcomm, hdir]
    have h1 : (Complex.polarCoord.symm (r, φ) ∈
        {v : ℂ | (v.re - C2.re) ^ 2 + (v.im - C2.im) ^ 2 < R ^ 2})
        ↔ (Complex.polarCoord.symm (r, φ) ∈ Metric.ball C2 R) := by
      rw [hD2_eq]
    have h3 : (Complex.polarCoord.symm (r, φ) ∈ Metric.ball C2 R)
        ↔ (Complex.polarCoord.symm (r, φ + β) ∈ Metric.ball (C - P) R) := by
      have h := hrot_disc (Complex.polarCoord.symm (r, φ + β))
      rw [hrot_w] at h
      exact h.symm
    have h2 : (Complex.polarCoord.symm (r, φ + β) ∈ Metric.ball (C - P) R)
        ↔ (Complex.polarCoord.symm (r, φ + β) ∈
          {w : ℂ | (w.re + p.1 - c.1) ^ 2 + (w.im + p.2 - c.2) ^ 2 < R ^ 2}) := by
      rw [hD1_eq]
    have hw_re : (Complex.polarCoord.symm (r, φ + β)).re
        = r * Real.cos (φ + β) :=
      pizza_polar_re r (φ + β)
    have hw_im : (Complex.polarCoord.symm (r, φ + β)).im
        = r * Real.sin (φ + β) :=
      pizza_polar_im r (φ + β)
    have h4 : (Complex.polarCoord.symm (r, φ + β) ∈
        {w : ℂ | (w.re + p.1 - c.1) ^ 2 + (w.im + p.2 - c.2) ^ 2 < R ^ 2})
        ↔ r < pizza_rho c p R (φ + β) := by
      simp only [Set.mem_ofPred_eq]
      rw [hw_re, hw_im]
      have heq1 : r * Real.cos (φ + β) + p.1 - c.1
          = p.1 + r * Real.cos (φ + β) - c.1 := by ring
      have heq2 : r * Real.sin (φ + β) + p.2 - c.2
          = p.2 + r * Real.sin (φ + β) - c.2 := by ring
      rw [heq1, heq2]
      exact pizza_ray_mem c p R r (φ + β) hp' hr
    exact h1.trans (h3.trans (h2.trans h4))
  set s : Set (ℝ × ℝ) :=
      {q : ℝ × ℝ | q.1 < pizza_rho c p R (q.2 + β)} ∩
        {q : ℝ × ℝ | q.2 < -Real.pi + L} with hs_def
  set H : (ℝ × ℝ) → ENNReal :=
    s.indicator (fun q => ENNReal.ofReal q.1) with hH_def
  have hs_meas : MeasurableSet s := by
    rw [hs_def]
    apply MeasurableSet.inter
    · have hf1 : Measurable (fun q : ℝ × ℝ => q.1) := measurable_fst
      have hf2 : Measurable (fun q : ℝ × ℝ => pizza_rho c p R (q.2 + β)) := by
        have hcont : Continuous (fun q : ℝ × ℝ => pizza_rho c p R (q.2 + β)) := by
          unfold pizza_rho pizza_q
          fun_prop
        exact hcont.measurable
      exact measurableSet_lt hf1 hf2
    · exact measurableSet_lt measurable_snd measurable_const
  have hH_meas : Measurable H := by
    rw [hH_def]
    exact Measurable.indicator measurable_fst.ennreal_ofReal hs_meas
  have htarget_eq : ∀ p ∈ polarCoord.target,
      ENNReal.ofReal p.1 • T.indicator 1 (Complex.polarCoord.symm p) = H p := by
    intro p hp
    have htarget : polarCoord.target
        = Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi := rfl
    rw [htarget] at hp
    obtain ⟨r, φ⟩ := p
    have hmem := Set.mem_prod.mp hp
    have hr : 0 < r := hmem.1
    have hφ : φ ∈ Set.Ioo (-Real.pi) Real.pi := hmem.2
    have hr_le : 0 ≤ r := le_of_lt hr
    have hdisc_mem := hdisc r φ hr_le
    have hcone_mem := pizza_cone_mem_target L hL1 hL2 r φ hr hφ
    have hT_mem : (Complex.polarCoord.symm (r, φ) ∈ T)
        ↔ (r < pizza_rho c p R (φ + β) ∧ φ < -Real.pi + L) := by
      rw [hT_def]
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
      constructor
      · intro h
        exact ⟨hdisc_mem.mp h.1, hcone_mem.mp h.2⟩
      · intro h
        exact ⟨hdisc_mem.mpr h.1, hcone_mem.mpr h.2⟩
    have hs_mem : ((r, φ) ∈ s)
        ↔ (r < pizza_rho c p R (φ + β) ∧ φ < -Real.pi + L) := by
      rw [hs_def]
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    have hequiv : (Complex.polarCoord.symm (r, φ) ∈ T) ↔ ((r, φ) ∈ s) := by
      rw [hT_mem, hs_mem]
    rw [hH_def]
    simp only [smul_eq_mul]
    by_cases hT : Complex.polarCoord.symm (r, φ) ∈ T
    · have hs : (r, φ) ∈ s := hequiv.mp hT
      rw [Set.indicator_of_mem hT, Set.indicator_of_mem hs]
      simp only [Pi.one_apply, mul_one]
    · have hs : (r, φ) ∉ s := fun h => hT (hequiv.mpr h)
      rw [Set.indicator_of_notMem hT, Set.indicator_of_notMem hs]
      simp only [mul_zero]
  have htarget_meas : MeasurableSet polarCoord.target :=
    polarCoord.open_target.measurableSet
  have hvol_H : (∫⁻ p in polarCoord.target,
      ENNReal.ofReal p.1 • T.indicator 1 (Complex.polarCoord.symm p))
      = ∫⁻ p in polarCoord.target, H p := by
    apply MeasureTheory.setLIntegral_congr_fun htarget_meas
    exact htarget_eq
  have hvol_H2 : MeasureTheory.volume T = ∫⁻ p in polarCoord.target, H p :=
    hvol_target.trans hvol_H
  have htarget_prod : polarCoord.target
      = Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi := rfl
  have hTonelli : (∫⁻ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi, H p
      ∂MeasureTheory.volume)
      = (∫⁻ φ in Set.Ioo (-Real.pi) Real.pi,
        ∫⁻ r in Set.Ioi (0 : ℝ), H (r, φ)
        ∂MeasureTheory.volume ∂MeasureTheory.volume) := by
    rw [MeasureTheory.Measure.volume_eq_prod]
    exact MeasureTheory.setLIntegral_prod_symm H hH_meas.aemeasurable
  have hvol_iter : MeasureTheory.volume T =
      (∫⁻ φ in Set.Ioo (-Real.pi) Real.pi,
        ∫⁻ r in Set.Ioi (0 : ℝ), H (r, φ)
        ∂MeasureTheory.volume ∂MeasureTheory.volume) := by
    rw [hvol_H2, htarget_prod]
    exact hTonelli
  have hinner : ∀ φ : ℝ, (∫⁻ r in Set.Ioi (0 : ℝ), H (r, φ)
      ∂MeasureTheory.volume)
      = (Set.Iio (-Real.pi + L)).indicator
        (fun φ => ENNReal.ofReal ((pizza_rho c p R (φ + β)) ^ 2 / 2)) φ := by
    intro φ
    by_cases hφ : φ < -Real.pi + L
    · have hρ_pos : 0 < pizza_rho c p R (φ + β) :=
        pizza_rho_pos c p R (φ + β) hp'
      have hH_eq : ∀ r : ℝ, H (r, φ)
          = (Set.Iio (pizza_rho c p R (φ + β))).indicator
            (fun r => ENNReal.ofReal r) r := by
        intro r
        rw [hH_def]
        have hs_iff : ((r, φ) ∈ s)
            ↔ (r < pizza_rho c p R (φ + β)) := by
          rw [hs_def]
          simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
          constructor
          · intro h
            exact h.1
          · intro h
            exact ⟨h, hφ⟩
        by_cases hr : r < pizza_rho c p R (φ + β)
        · have hs : (r, φ) ∈ s := hs_iff.mpr hr
          have hr_mem : r ∈ Set.Iio (pizza_rho c p R (φ + β)) := hr
          rw [Set.indicator_of_mem hs, Set.indicator_of_mem hr_mem]
        · have hs : (r, φ) ∉ s := fun h => hr (hs_iff.mp h)
          have hr_mem : r ∉ Set.Iio (pizza_rho c p R (φ + β)) := hr
          rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hr_mem]
      have hInt_eq : (∫⁻ r in Set.Ioi (0 : ℝ), H (r, φ)
          ∂MeasureTheory.volume)
          = (∫⁻ r in Set.Ioi (0 : ℝ),
            (Set.Iio (pizza_rho c p R (φ + β))).indicator
              (fun r => ENNReal.ofReal r) r ∂MeasureTheory.volume) := by
        apply MeasureTheory.setLIntegral_congr_fun measurableSet_Ioi
        intro r _
        exact hH_eq r
      rw [hInt_eq, pizza_inner_r _ hρ_pos]
      have hφ_mem : φ ∈ Set.Iio (-Real.pi + L) := hφ
      rw [Set.indicator_of_mem hφ_mem]
    · have hH_zero : ∀ r : ℝ, H (r, φ) = 0 := by
        intro r
        rw [hH_def]
        have hs : (r, φ) ∉ s := by
          rw [hs_def]
          simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, not_and]
          intro _
          exact hφ
        rw [Set.indicator_of_notMem hs]
      have hInt_zero : (∫⁻ r in Set.Ioi (0 : ℝ), H (r, φ)
          ∂MeasureTheory.volume) = 0 := by
        simp [hH_zero]
      rw [hInt_zero]
      have hφ_mem : φ ∉ Set.Iio (-Real.pi + L) := hφ
      rw [Set.indicator_of_notMem hφ_mem]
  have hvol_outer : MeasureTheory.volume T =
      (∫⁻ φ in Set.Ioo (-Real.pi) Real.pi,
        (Set.Iio (-Real.pi + L)).indicator
          (fun φ => ENNReal.ofReal ((pizza_rho c p R (φ + β)) ^ 2 / 2)) φ
        ∂MeasureTheory.volume) := by
    rw [hvol_iter]
    apply MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo
    intro φ _
    exact hinner φ
  have hIoo_inter : Set.Iio (-Real.pi + L) ∩ Set.Ioo (-Real.pi) Real.pi
      = Set.Ioo (-Real.pi) (-Real.pi + L) := by
    ext φ
    simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioo]
    constructor
    · intro h
      exact ⟨h.2.1, h.1⟩
    · intro h
      have hLe : -Real.pi + L ≤ Real.pi := by linarith [hL2]
      have hφπ : φ < Real.pi := lt_of_lt_of_le h.2 hLe
      exact ⟨h.2, h.1, hφπ⟩
  have hvol_Ioo : MeasureTheory.volume T =
      (∫⁻ φ in Set.Ioo (-Real.pi) (-Real.pi + L),
        ENNReal.ofReal ((pizza_rho c p R (φ + β)) ^ 2 / 2)
        ∂MeasureTheory.volume) := by
    rw [hvol_outer,
      MeasureTheory.setLIntegral_indicator measurableSet_Iio, hIoo_inter]
  have hcont_ρ : Continuous
      (fun φ : ℝ => (pizza_rho c p R (φ + β)) ^ 2 / 2) := by
    unfold pizza_rho pizza_q
    fun_prop
  have hnn_ρ : ∀ φ : ℝ, 0 ≤ (pizza_rho c p R (φ + β)) ^ 2 / 2 := by
    intro φ
    apply div_nonneg (sq_nonneg _) (by norm_num)
  have hab : -Real.pi ≤ -Real.pi + L := by linarith [hL1]
  have hvol_ofReal : MeasureTheory.volume T =
      ENNReal.ofReal
        (∫ φ in (-Real.pi)..(-Real.pi + L),
          (pizza_rho c p R (φ + β)) ^ 2 / 2) := by
    rw [hvol_Ioo]
    exact pizza_ofReal_Ioo _ hcont_ρ hnn_ρ _ _ hab
  have hshift : (∫ φ in (-Real.pi)..(-Real.pi + L),
        (pizza_rho c p R (φ + β)) ^ 2 / 2)
      = ∫ φ in a..a + L, (pizza_rho c p R φ) ^ 2 / 2 := by
    have hcomp := intervalIntegral.integral_comp_add_right
      (fun ψ : ℝ => (pizza_rho c p R ψ) ^ 2 / 2) β
      (a := -Real.pi) (b := -Real.pi + L)
    have h1 : -Real.pi + β = a := by rw [hβ_eq]; ring
    have h2 : -Real.pi + L + β = a + L := by rw [hβ_eq]; ring
    rw [h1, h2] at hcomp
    exact hcomp
  rw [hvol_ofReal, hshift]

/-- **Pizza theorem.** Let $n \ge 2$ be a natural number, let $D$ be the open disk of radius
$R > 0$ centered at a point $c$ of $\mathbb{R}^2$, let $p$ be a point of $D$, and let $\theta_0$
be a real number. Put $\alpha = \pi / (2n)$ and, for $k = 0, 1, \dots, 4n - 1$, let $S_k$ be the
set of points of $D$ of the form $p + r(\cos\theta, \sin\theta)$ with $r \ge 0$ and
$\theta_0 + k\alpha \le \theta < \theta_0 + (k + 1)\alpha$. Then the sum of the Lebesgue measures
of the $S_k$ with $k$ even equals the sum of the Lebesgue measures of the $S_k$ with $k$ odd.

The $4n$ sectors $S_k$ are the slices cut from the disk by $2n$ lines through $p$ at equal
angles, so alternately shading the slices gives equal shaded and unshaded areas.

Proves `Wanted` entry `pizza_theorem`.

Source: *Pizza theorem*, Wikipedia, https://en.wikipedia.org/wiki/Pizza_theorem.
-/
theorem pizza_theorem (n : ℕ) (hn : 2 ≤ n)
    (c p : ℝ × ℝ) (R : ℝ) (hR : 0 < R)
    (hp : p ∈ {x : ℝ × ℝ | (x.1 - c.1) ^ 2 + (x.2 - c.2) ^ 2 < R ^ 2}) (θ₀ : ℝ) :
    ∑ k ∈ Finset.filter (fun k => k % 2 = 0) (Finset.range (4 * n)),
      MeasureTheory.volume ({x : ℝ × ℝ | (x.1 - c.1) ^ 2 + (x.2 - c.2) ^ 2 < R ^ 2} ∩
        {x | ∃ r θ : ℝ, 0 ≤ r ∧
          θ₀ + (k : ℝ) * (Real.pi / (2 * (n : ℝ))) ≤ θ ∧
          θ < θ₀ + ((k : ℝ) + 1) * (Real.pi / (2 * (n : ℝ))) ∧
          x = p + r • (Real.cos θ, Real.sin θ)}) =
    ∑ k ∈ Finset.filter (fun k => k % 2 = 1) (Finset.range (4 * n)),
      MeasureTheory.volume ({x : ℝ × ℝ | (x.1 - c.1) ^ 2 + (x.2 - c.2) ^ 2 < R ^ 2} ∩
        {x | ∃ r θ : ℝ, 0 ≤ r ∧
          θ₀ + (k : ℝ) * (Real.pi / (2 * (n : ℝ))) ≤ θ ∧
          θ < θ₀ + ((k : ℝ) + 1) * (Real.pi / (2 * (n : ℝ))) ∧
          x = p + r • (Real.cos θ, Real.sin θ)}) := by
  have hn_pos : 0 < (n : ℝ) := by
    have h0 : 0 < n := by omega
    exact Nat.cast_pos.mpr h0
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
  set α : ℝ := Real.pi / (2 * (n : ℝ)) with hα
  have hpi : 0 < Real.pi := Real.pi_pos
  have hα_pos : 0 < α := by
    rw [hα]
    positivity
  have hα_le : α ≤ 2 * Real.pi := by
    rw [hα]
    have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h2n : 0 < 2 * (n : ℝ) := by positivity
    rw [div_le_iff₀ h2n]
    nlinarith [hpi, hn2]
  have hp' : (p.1 - c.1) ^ 2 + (p.2 - c.2) ^ 2 < R ^ 2 := hp
  have hsec : ∀ k : ℕ,
      MeasureTheory.volume
        ({x : ℝ × ℝ | (x.1 - c.1) ^ 2 + (x.2 - c.2) ^ 2 < R ^ 2} ∩
        {x | ∃ r θ : ℝ, 0 ≤ r ∧ θ₀ + (k : ℝ) * α ≤ θ ∧
          θ < θ₀ + ((k : ℝ) + 1) * α ∧
          x = p + r • (Real.cos θ, Real.sin θ)})
      = ENNReal.ofReal
        (∫ φ in θ₀ + (k : ℝ) * α..θ₀ + ((k : ℝ) + 1) * α,
          (pizza_rho c p R φ) ^ 2 / 2) := by
    intro k
    have hvol := pizza_sector_area c p R hR hp
      (θ₀ + (k : ℝ) * α) α hα_pos hα_le
    have heq : θ₀ + (k : ℝ) * α + α
        = θ₀ + ((k : ℝ) + 1) * α := by ring
    rw [heq] at hvol
    exact hvol
  have hI_nonneg : ∀ k : ℕ,
      0 ≤ ∫ φ in θ₀ + (k : ℝ) * α..θ₀ + ((k : ℝ) + 1) * α,
        (pizza_rho c p R φ) ^ 2 / 2 := by
    intro k
    apply intervalIntegral.integral_nonneg
    · have : (θ₀ + (k : ℝ) * α)
          ≤ θ₀ + ((k : ℝ) + 1) * α := by
        have : (k : ℝ) * α ≤ ((k : ℝ) + 1) * α := by
          apply mul_le_mul_of_nonneg_right
          · linarith
          · exact le_of_lt hα_pos
        linarith
      exact this
    · intro u _
      apply div_nonneg (sq_nonneg _) (by norm_num)
  have heven : (∑ k ∈ Finset.filter (fun k => k % 2 = 0)
      (Finset.range (4 * n)),
      MeasureTheory.volume
        ({x : ℝ × ℝ | (x.1 - c.1) ^ 2 + (x.2 - c.2) ^ 2 < R ^ 2} ∩
        {x | ∃ r θ : ℝ, 0 ≤ r ∧ θ₀ + (k : ℝ) * α ≤ θ ∧
          θ < θ₀ + ((k : ℝ) + 1) * α ∧
          x = p + r • (Real.cos θ, Real.sin θ)}))
      = ∑ k ∈ Finset.filter (fun k => k % 2 = 0)
        (Finset.range (4 * n)),
        ENNReal.ofReal
          (∫ φ in θ₀ + (k : ℝ) * α..θ₀ + ((k : ℝ) + 1) * α,
            (pizza_rho c p R φ) ^ 2 / 2) :=
    Finset.sum_congr rfl (fun k _ => hsec k)
  have hodd : (∑ k ∈ Finset.filter (fun k => k % 2 = 1)
      (Finset.range (4 * n)),
      MeasureTheory.volume
        ({x : ℝ × ℝ | (x.1 - c.1) ^ 2 + (x.2 - c.2) ^ 2 < R ^ 2} ∩
        {x | ∃ r θ : ℝ, 0 ≤ r ∧ θ₀ + (k : ℝ) * α ≤ θ ∧
          θ < θ₀ + ((k : ℝ) + 1) * α ∧
          x = p + r • (Real.cos θ, Real.sin θ)}))
      = ∑ k ∈ Finset.filter (fun k => k % 2 = 1)
        (Finset.range (4 * n)),
        ENNReal.ofReal
          (∫ φ in θ₀ + (k : ℝ) * α..θ₀ + ((k : ℝ) + 1) * α,
            (pizza_rho c p R φ) ^ 2 / 2) :=
    Finset.sum_congr rfl (fun k _ => hsec k)
  rw [heven, hodd]
  rw [← ENNReal.ofReal_sum_of_nonneg
    (fun k _ => hI_nonneg k)]
  rw [← ENNReal.ofReal_sum_of_nonneg
    (fun k _ => hI_nonneg k)]
  congr 1
  have h2n : 2 * n = n + n := by ring
  have hevenR := pizza_sum_even n (fun k : ℕ =>
    ∫ φ in θ₀ + (k : ℝ) * α..θ₀ + ((k : ℝ) + 1) * α,
      (pizza_rho c p R φ) ^ 2 / 2)
  have hoddR := pizza_sum_odd n (fun k : ℕ =>
    ∫ φ in θ₀ + (k : ℝ) * α..θ₀ + ((k : ℝ) + 1) * α,
      (pizza_rho c p R φ) ^ 2 / 2)
  rw [hevenR, hoddR]
  rw [h2n, Finset.sum_range_add, Finset.sum_range_add]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  have hpi_eq : 2 * (n : ℝ) * α = Real.pi := by
    rw [hα]
    field_simp
  have hcast_even : ∀ j : ℕ,
      ((2 * (n + j) : ℕ) : ℝ) = ((2 * j : ℕ) : ℝ) + 2 * (n : ℝ) := by
    intro j
    push_cast
    ring
  have hcast_odd : ∀ j : ℕ,
      ((2 * (n + j) + 1 : ℕ) : ℝ)
        = ((2 * j + 1 : ℕ) : ℝ) + 2 * (n : ℝ) := by
    intro j
    push_cast
    ring
  have hpair_even : ∀ j : ℕ,
      (∫ φ in (θ₀ + ((2 * j : ℕ) : ℝ) * α)..
          (θ₀ + (((2 * j : ℕ) : ℝ) + 1) * α),
          (pizza_rho c p R φ) ^ 2 / 2)
        + (∫ φ in (θ₀ + ((2 * (n + j) : ℕ) : ℝ) * α)..
          (θ₀ + (((2 * (n + j) : ℕ) : ℝ) + 1) * α),
          (pizza_rho c p R φ) ^ 2 / 2)
      = ∫ φ in (θ₀ + ((2 * j : ℕ) : ℝ) * α)..
          (θ₀ + ((2 * j : ℕ) : ℝ) * α + α),
          (R ^ 2 + ((p.1 - c.1) ^ 2 - (p.2 - c.2) ^ 2)
            * Real.cos (2 * φ)
            + 2 * (p.1 - c.1) * (p.2 - c.2)
              * Real.sin (2 * φ)) := by
    intro j
    have h1 : θ₀ + ((2 * (n + j) : ℕ) : ℝ) * α
        = θ₀ + ((2 * j : ℕ) : ℝ) * α + Real.pi := by
      rw [hcast_even j]
      have : (((2 * j : ℕ) : ℝ) + 2 * (n : ℝ)) * α
          = ((2 * j : ℕ) : ℝ) * α + Real.pi := by
        have h2 : (2 * (n : ℝ)) * α = Real.pi := by
          linarith [hpi_eq]
        linarith [h2]
      linarith [this]
    have h2 : θ₀ + (((2 * (n + j) : ℕ) : ℝ) + 1) * α
        = θ₀ + ((2 * j : ℕ) : ℝ) * α + Real.pi + α := by
      rw [hcast_even j]
      have : ((((2 * j : ℕ) : ℝ) + 2 * (n : ℝ)) + 1) * α
          = ((2 * j : ℕ) : ℝ) * α + Real.pi + α := by
        have h3 : (2 * (n : ℝ)) * α = Real.pi := by
          linarith [hpi_eq]
        linarith [h3]
      linarith [this]
    have h3 : θ₀ + (((2 * j : ℕ) : ℝ) + 1) * α
        = θ₀ + ((2 * j : ℕ) : ℝ) * α + α := by ring
    rw [h1, h2, h3]
    exact pizza_pair_integral c p R
      (θ₀ + ((2 * j : ℕ) : ℝ) * α) α hp'
  have hpair_odd : ∀ j : ℕ,
      (∫ φ in (θ₀ + ((2 * j + 1 : ℕ) : ℝ) * α)..
          (θ₀ + (((2 * j + 1 : ℕ) : ℝ) + 1) * α),
          (pizza_rho c p R φ) ^ 2 / 2)
        + (∫ φ in (θ₀ + ((2 * (n + j) + 1 : ℕ) : ℝ) * α)..
          (θ₀ + (((2 * (n + j) + 1 : ℕ) : ℝ) + 1) * α),
          (pizza_rho c p R φ) ^ 2 / 2)
      = ∫ φ in (θ₀ + ((2 * j + 1 : ℕ) : ℝ) * α)..
          (θ₀ + ((2 * j + 1 : ℕ) : ℝ) * α + α),
          (R ^ 2 + ((p.1 - c.1) ^ 2 - (p.2 - c.2) ^ 2)
            * Real.cos (2 * φ)
            + 2 * (p.1 - c.1) * (p.2 - c.2)
              * Real.sin (2 * φ)) := by
    intro j
    have h1 : θ₀ + ((2 * (n + j) + 1 : ℕ) : ℝ) * α
        = θ₀ + ((2 * j + 1 : ℕ) : ℝ) * α + Real.pi := by
      rw [hcast_odd j]
      have : (((2 * j + 1 : ℕ) : ℝ) + 2 * (n : ℝ)) * α
          = ((2 * j + 1 : ℕ) : ℝ) * α + Real.pi := by
        have h2 : (2 * (n : ℝ)) * α = Real.pi := by
          linarith [hpi_eq]
        linarith [h2]
      linarith [this]
    have h2 : θ₀ + (((2 * (n + j) + 1 : ℕ) : ℝ) + 1) * α
        = θ₀ + ((2 * j + 1 : ℕ) : ℝ) * α + Real.pi + α := by
      rw [hcast_odd j]
      have : ((((2 * j + 1 : ℕ) : ℝ) + 2 * (n : ℝ)) + 1) * α
          = ((2 * j + 1 : ℕ) : ℝ) * α + Real.pi + α := by
        have h3 : (2 * (n : ℝ)) * α = Real.pi := by
          linarith [hpi_eq]
        linarith [h3]
      linarith [this]
    have h3 : θ₀ + (((2 * j + 1 : ℕ) : ℝ) + 1) * α
        = θ₀ + ((2 * j + 1 : ℕ) : ℝ) * α + α := by ring
    rw [h1, h2, h3]
    exact pizza_pair_integral c p R
      (θ₀ + ((2 * j + 1 : ℕ) : ℝ) * α) α hp'
  have heq_even : (∑ j ∈ Finset.range n,
      ((∫ φ in (θ₀ + ((2 * j : ℕ) : ℝ) * α)..
        (θ₀ + (((2 * j : ℕ) : ℝ) + 1) * α),
        (pizza_rho c p R φ) ^ 2 / 2)
      + (∫ φ in (θ₀ + ((2 * (n + j) : ℕ) : ℝ) * α)..
        (θ₀ + (((2 * (n + j) : ℕ) : ℝ) + 1) * α),
        (pizza_rho c p R φ) ^ 2 / 2)))
      = ∑ j ∈ Finset.range n,
        ∫ φ in (θ₀ + ((2 * j : ℕ) : ℝ) * α)..
          (θ₀ + ((2 * j : ℕ) : ℝ) * α + α),
          (R ^ 2 + ((p.1 - c.1) ^ 2 - (p.2 - c.2) ^ 2)
            * Real.cos (2 * φ)
            + 2 * (p.1 - c.1) * (p.2 - c.2)
              * Real.sin (2 * φ)) :=
    Finset.sum_congr rfl (fun j _ => hpair_even j)
  have heq_odd : (∑ j ∈ Finset.range n,
      ((∫ φ in (θ₀ + ((2 * j + 1 : ℕ) : ℝ) * α)..
        (θ₀ + (((2 * j + 1 : ℕ) : ℝ) + 1) * α),
        (pizza_rho c p R φ) ^ 2 / 2)
      + (∫ φ in (θ₀ + ((2 * (n + j) + 1 : ℕ) : ℝ) * α)..
        (θ₀ + (((2 * (n + j) + 1 : ℕ) : ℝ) + 1) * α),
        (pizza_rho c p R φ) ^ 2 / 2)))
      = ∑ j ∈ Finset.range n,
        ∫ φ in (θ₀ + ((2 * j + 1 : ℕ) : ℝ) * α)..
          (θ₀ + ((2 * j + 1 : ℕ) : ℝ) * α + α),
          (R ^ 2 + ((p.1 - c.1) ^ 2 - (p.2 - c.2) ^ 2)
            * Real.cos (2 * φ)
            + 2 * (p.1 - c.1) * (p.2 - c.2)
              * Real.sin (2 * φ)) :=
    Finset.sum_congr rfl (fun j _ => hpair_odd j)
  rw [heq_even, heq_odd]
  set A : ℝ := (p.1 - c.1) ^ 2 - (p.2 - c.2) ^ 2 with hA
  set B : ℝ := 2 * (p.1 - c.1) * (p.2 - c.2) with hB
  have hcos_cont : Continuous (fun φ : ℝ => Real.cos (2 * φ)) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id)
  have hsin_cont : Continuous (fun φ : ℝ => Real.sin (2 * φ)) :=
    Real.continuous_sin.comp (continuous_const.mul continuous_id)
  have hsplit : ∀ a : ℝ,
      (∫ φ in a..a + α,
        (R ^ 2 + A * Real.cos (2 * φ)
          + B * Real.sin (2 * φ)))
      = R ^ 2 * α + A * (∫ φ in a..a + α, Real.cos (2 * φ))
        + B * (∫ φ in a..a + α, Real.sin (2 * φ)) := by
    intro a
    have h1 : IntervalIntegrable (fun _ : ℝ => R ^ 2)
        MeasureTheory.volume a (a + α) :=
      continuous_const.intervalIntegrable a (a + α)
    have h2 : IntervalIntegrable
        (fun φ : ℝ => A * Real.cos (2 * φ))
        MeasureTheory.volume a (a + α) :=
      (continuous_const.mul hcos_cont).intervalIntegrable a (a + α)
    have h3 : IntervalIntegrable
        (fun φ : ℝ => B * Real.sin (2 * φ))
        MeasureTheory.volume a (a + α) :=
      (continuous_const.mul hsin_cont).intervalIntegrable a (a + α)
    have heq1 : (fun φ : ℝ => R ^ 2 + A * Real.cos (2 * φ)
        + B * Real.sin (2 * φ))
        = fun φ => (R ^ 2 + A * Real.cos (2 * φ))
          + B * Real.sin (2 * φ) := rfl
    have heq2 : (fun φ : ℝ => R ^ 2 + A * Real.cos (2 * φ))
        = fun φ => R ^ 2 + A * Real.cos (2 * φ) := rfl
    rw [heq1, intervalIntegral.integral_add
      ((h1.add h2)) h3]
    rw [heq2, intervalIntegral.integral_add h1 h2]
    rw [intervalIntegral.integral_const]
    rw [intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_const_mul]
    simp [smul_eq_mul]
    ring
  have heven_split : (∑ j ∈ Finset.range n,
      ∫ φ in (θ₀ + ((2 * j : ℕ) : ℝ) * α)..
        (θ₀ + ((2 * j : ℕ) : ℝ) * α + α),
        (R ^ 2 + A * Real.cos (2 * φ)
          + B * Real.sin (2 * φ)))
      = ∑ j ∈ Finset.range n,
        (R ^ 2 * α + A * (∫ φ in (θ₀ + ((2 * j : ℕ) : ℝ) * α)..
          (θ₀ + ((2 * j : ℕ) : ℝ) * α + α), Real.cos (2 * φ))
          + B * (∫ φ in (θ₀ + ((2 * j : ℕ) : ℝ) * α)..
            (θ₀ + ((2 * j : ℕ) : ℝ) * α + α), Real.sin (2 * φ))) :=
    Finset.sum_congr rfl (fun j _ => hsplit _)
  have hodd_split : (∑ j ∈ Finset.range n,
      ∫ φ in (θ₀ + ((2 * j + 1 : ℕ) : ℝ) * α)..
        (θ₀ + ((2 * j + 1 : ℕ) : ℝ) * α + α),
        (R ^ 2 + A * Real.cos (2 * φ)
          + B * Real.sin (2 * φ)))
      = ∑ j ∈ Finset.range n,
        (R ^ 2 * α + A * (∫ φ in (θ₀ + ((2 * j + 1 : ℕ) : ℝ) * α)..
          (θ₀ + ((2 * j + 1 : ℕ) : ℝ) * α + α), Real.cos (2 * φ))
          + B * (∫ φ in (θ₀ + ((2 * j + 1 : ℕ) : ℝ) * α)..
            (θ₀ + ((2 * j + 1 : ℕ) : ℝ) * α + α), Real.sin (2 * φ))) :=
    Finset.sum_congr rfl (fun j _ => hsplit _)
  rw [heven_split, hodd_split]
  have hang_even_a : ∀ j : ℕ,
      2 * (θ₀ + ((2 * j : ℕ) : ℝ) * α)
        = 2 * θ₀ + 2 * Real.pi * (j : ℝ) / (n : ℝ) := by
    intro j
    rw [hα]
    push_cast
    field_simp
    try ring
  have hang_even_b : ∀ j : ℕ,
      2 * (θ₀ + ((2 * j : ℕ) : ℝ) * α + α)
        = (2 * θ₀ + Real.pi / (n : ℝ))
          + 2 * Real.pi * (j : ℝ) / (n : ℝ) := by
    intro j
    rw [hα]
    push_cast
    field_simp
    try ring
  have hang_odd_a : ∀ j : ℕ,
      2 * (θ₀ + ((2 * j + 1 : ℕ) : ℝ) * α)
        = (2 * θ₀ + Real.pi / (n : ℝ))
          + 2 * Real.pi * (j : ℝ) / (n : ℝ) := by
    intro j
    rw [hα]
    push_cast
    field_simp
    try ring
  have hang_odd_b : ∀ j : ℕ,
      2 * (θ₀ + ((2 * j + 1 : ℕ) : ℝ) * α + α)
        = (2 * θ₀ + 2 * Real.pi / (n : ℝ))
          + 2 * Real.pi * (j : ℝ) / (n : ℝ) := by
    intro j
    rw [hα]
    push_cast
    field_simp
    try ring
  have hsin_even_a : ∑ j ∈ Finset.range n,
      Real.sin (2 * (θ₀ + ((2 * j : ℕ) : ℝ) * α)) = 0 := by
    have h1 : ∀ j : ℕ,
        Real.sin (2 * (θ₀ + ((2 * j : ℕ) : ℝ) * α))
          = Real.sin
            (2 * θ₀ + 2 * Real.pi * (j : ℝ) / (n : ℝ)) := by
      intro j
      rw [hang_even_a j]
    simp only [h1]
    exact pizza_sum_sin n hn (2 * θ₀)
  have hsin_even_b : ∑ j ∈ Finset.range n,
      Real.sin (2 * (θ₀ + ((2 * j : ℕ) : ℝ) * α + α)) = 0 := by
    have h1 : ∀ j : ℕ,
        Real.sin (2 * (θ₀ + ((2 * j : ℕ) : ℝ) * α + α))
          = Real.sin
            ((2 * θ₀ + Real.pi / (n : ℝ))
              + 2 * Real.pi * (j : ℝ) / (n : ℝ)) := by
      intro j
      rw [hang_even_b j]
    simp only [h1]
    exact pizza_sum_sin n hn (2 * θ₀ + Real.pi / (n : ℝ))
  have hsin_odd_a : ∑ j ∈ Finset.range n,
      Real.sin (2 * (θ₀ + ((2 * j + 1 : ℕ) : ℝ) * α)) = 0 := by
    have h1 : ∀ j : ℕ,
        Real.sin (2 * (θ₀ + ((2 * j + 1 : ℕ) : ℝ) * α))
          = Real.sin
            ((2 * θ₀ + Real.pi / (n : ℝ))
              + 2 * Real.pi * (j : ℝ) / (n : ℝ)) := by
      intro j
      rw [hang_odd_a j]
    simp only [h1]
    exact pizza_sum_sin n hn (2 * θ₀ + Real.pi / (n : ℝ))
  have hsin_odd_b : ∑ j ∈ Finset.range n,
      Real.sin (2 * (θ₀ + ((2 * j + 1 : ℕ) : ℝ) * α + α)) = 0 := by
    have h1 : ∀ j : ℕ,
        Real.sin (2 * (θ₀ + ((2 * j + 1 : ℕ) : ℝ) * α + α))
          = Real.sin
            ((2 * θ₀ + 2 * Real.pi / (n : ℝ))
              + 2 * Real.pi * (j : ℝ) / (n : ℝ)) := by
      intro j
      rw [hang_odd_b j]
    simp only [h1]
    exact pizza_sum_sin n hn (2 * θ₀ + 2 * Real.pi / (n : ℝ))
  have hcos_even_a : ∑ j ∈ Finset.range n,
      Real.cos (2 * (θ₀ + ((2 * j : ℕ) : ℝ) * α)) = 0 := by
    have h1 : ∀ j : ℕ,
        Real.cos (2 * (θ₀ + ((2 * j : ℕ) : ℝ) * α))
          = Real.cos
            (2 * θ₀ + 2 * Real.pi * (j : ℝ) / (n : ℝ)) := by
      intro j
      rw [hang_even_a j]
    simp only [h1]
    exact pizza_sum_cos n hn (2 * θ₀)
  have hcos_even_b : ∑ j ∈ Finset.range n,
      Real.cos (2 * (θ₀ + ((2 * j : ℕ) : ℝ) * α + α)) = 0 := by
    have h1 : ∀ j : ℕ,
        Real.cos (2 * (θ₀ + ((2 * j : ℕ) : ℝ) * α + α))
          = Real.cos
            ((2 * θ₀ + Real.pi / (n : ℝ))
              + 2 * Real.pi * (j : ℝ) / (n : ℝ)) := by
      intro j
      rw [hang_even_b j]
    simp only [h1]
    exact pizza_sum_cos n hn (2 * θ₀ + Real.pi / (n : ℝ))
  have hcos_odd_a : ∑ j ∈ Finset.range n,
      Real.cos (2 * (θ₀ + ((2 * j + 1 : ℕ) : ℝ) * α)) = 0 := by
    have h1 : ∀ j : ℕ,
        Real.cos (2 * (θ₀ + ((2 * j + 1 : ℕ) : ℝ) * α))
          = Real.cos
            ((2 * θ₀ + Real.pi / (n : ℝ))
              + 2 * Real.pi * (j : ℝ) / (n : ℝ)) := by
      intro j
      rw [hang_odd_a j]
    simp only [h1]
    exact pizza_sum_cos n hn (2 * θ₀ + Real.pi / (n : ℝ))
  have hcos_odd_b : ∑ j ∈ Finset.range n,
      Real.cos (2 * (θ₀ + ((2 * j + 1 : ℕ) : ℝ) * α + α)) = 0 := by
    have h1 : ∀ j : ℕ,
        Real.cos (2 * (θ₀ + ((2 * j + 1 : ℕ) : ℝ) * α + α))
          = Real.cos
            ((2 * θ₀ + 2 * Real.pi / (n : ℝ))
              + 2 * Real.pi * (j : ℝ) / (n : ℝ)) := by
      intro j
      rw [hang_odd_b j]
    simp only [h1]
    exact pizza_sum_cos n hn (2 * θ₀ + 2 * Real.pi / (n : ℝ))
  have heven_C0 : (∑ j ∈ Finset.range n,
      ∫ φ in (θ₀ + ((2 * j : ℕ) : ℝ) * α)..
        (θ₀ + ((2 * j : ℕ) : ℝ) * α + α), Real.cos (2 * φ)) = 0 := by
    have hC : ∀ j : ℕ,
        (∫ φ in (θ₀ + ((2 * j : ℕ) : ℝ) * α)..
          (θ₀ + ((2 * j : ℕ) : ℝ) * α + α), Real.cos (2 * φ))
        = (Real.sin (2 * (θ₀ + ((2 * j : ℕ) : ℝ) * α + α))
          - Real.sin (2 * (θ₀ + ((2 * j : ℕ) : ℝ) * α))) / 2 := by
      intro j
      exact pizza_integral_cos_two _ _
    have hsum : (∑ j ∈ Finset.range n,
        ∫ φ in (θ₀ + ((2 * j : ℕ) : ℝ) * α)..
          (θ₀ + ((2 * j : ℕ) : ℝ) * α + α), Real.cos (2 * φ))
        = ∑ j ∈ Finset.range n,
          (Real.sin (2 * (θ₀ + ((2 * j : ℕ) : ℝ) * α + α))
            - Real.sin (2 * (θ₀ + ((2 * j : ℕ) : ℝ) * α))) / 2 :=
      Finset.sum_congr rfl (fun j _ => hC j)
    rw [hsum]
    have hdiv : (∑ j ∈ Finset.range n,
        (Real.sin (2 * (θ₀ + ((2 * j : ℕ) : ℝ) * α + α))
          - Real.sin (2 * (θ₀ + ((2 * j : ℕ) : ℝ) * α))) / 2)
        = ((∑ j ∈ Finset.range n,
          Real.sin (2 * (θ₀ + ((2 * j : ℕ) : ℝ) * α + α)))
          - (∑ j ∈ Finset.range n,
            Real.sin (2 * (θ₀ + ((2 * j : ℕ) : ℝ) * α)))) / 2 := by
      simp only [div_eq_mul_inv]
      rw [← Finset.sum_mul]
      congr 1
      exact Finset.sum_sub_distrib _ _
    rw [hdiv, hsin_even_b, hsin_even_a]
    simp
  have heven_S0 : (∑ j ∈ Finset.range n,
      ∫ φ in (θ₀ + ((2 * j : ℕ) : ℝ) * α)..
        (θ₀ + ((2 * j : ℕ) : ℝ) * α + α), Real.sin (2 * φ)) = 0 := by
    have hS : ∀ j : ℕ,
        (∫ φ in (θ₀ + ((2 * j : ℕ) : ℝ) * α)..
          (θ₀ + ((2 * j : ℕ) : ℝ) * α + α), Real.sin (2 * φ))
        = (Real.cos (2 * (θ₀ + ((2 * j : ℕ) : ℝ) * α))
          - Real.cos (2 * (θ₀ + ((2 * j : ℕ) : ℝ) * α + α))) / 2 := by
      intro j
      exact pizza_integral_sin_two _ _
    have hsum : (∑ j ∈ Finset.range n,
        ∫ φ in (θ₀ + ((2 * j : ℕ) : ℝ) * α)..
          (θ₀ + ((2 * j : ℕ) : ℝ) * α + α), Real.sin (2 * φ))
        = ∑ j ∈ Finset.range n,
          (Real.cos (2 * (θ₀ + ((2 * j : ℕ) : ℝ) * α))
            - Real.cos (2 * (θ₀ + ((2 * j : ℕ) : ℝ) * α + α))) / 2 :=
      Finset.sum_congr rfl (fun j _ => hS j)
    rw [hsum]
    have hdiv : (∑ j ∈ Finset.range n,
        (Real.cos (2 * (θ₀ + ((2 * j : ℕ) : ℝ) * α))
          - Real.cos (2 * (θ₀ + ((2 * j : ℕ) : ℝ) * α + α))) / 2)
        = ((∑ j ∈ Finset.range n,
          Real.cos (2 * (θ₀ + ((2 * j : ℕ) : ℝ) * α)))
          - (∑ j ∈ Finset.range n,
            Real.cos (2 * (θ₀ + ((2 * j : ℕ) : ℝ) * α + α)))) / 2 := by
      simp only [div_eq_mul_inv]
      rw [← Finset.sum_mul]
      congr 1
      exact Finset.sum_sub_distrib _ _
    rw [hdiv, hcos_even_a, hcos_even_b]
    simp
  have hodd_C0 : (∑ j ∈ Finset.range n,
      ∫ φ in (θ₀ + ((2 * j + 1 : ℕ) : ℝ) * α)..
        (θ₀ + ((2 * j + 1 : ℕ) : ℝ) * α + α),
        Real.cos (2 * φ)) = 0 := by
    have hC : ∀ j : ℕ,
        (∫ φ in (θ₀ + ((2 * j + 1 : ℕ) : ℝ) * α)..
          (θ₀ + ((2 * j + 1 : ℕ) : ℝ) * α + α),
          Real.cos (2 * φ))
        = (Real.sin (2 * (θ₀ + ((2 * j + 1 : ℕ) : ℝ) * α + α))
          - Real.sin (2 * (θ₀ + ((2 * j + 1 : ℕ) : ℝ) * α))) / 2 := by
      intro j
      exact pizza_integral_cos_two _ _
    have hsum : (∑ j ∈ Finset.range n,
        ∫ φ in (θ₀ + ((2 * j + 1 : ℕ) : ℝ) * α)..
          (θ₀ + ((2 * j + 1 : ℕ) : ℝ) * α + α),
          Real.cos (2 * φ))
        = ∑ j ∈ Finset.range n,
          (Real.sin (2 * (θ₀ + ((2 * j + 1 : ℕ) : ℝ) * α + α))
            - Real.sin (2 * (θ₀ + ((2 * j + 1 : ℕ) : ℝ) * α))) / 2 :=
      Finset.sum_congr rfl (fun j _ => hC j)
    rw [hsum]
    have hdiv : (∑ j ∈ Finset.range n,
        (Real.sin (2 * (θ₀ + ((2 * j + 1 : ℕ) : ℝ) * α + α))
          - Real.sin (2 * (θ₀ + ((2 * j + 1 : ℕ) : ℝ) * α))) / 2)
        = ((∑ j ∈ Finset.range n,
          Real.sin (2 * (θ₀ + ((2 * j + 1 : ℕ) : ℝ) * α + α)))
          - (∑ j ∈ Finset.range n,
            Real.sin (2 * (θ₀ + ((2 * j + 1 : ℕ) : ℝ) * α)))) / 2 := by
      simp only [div_eq_mul_inv]
      rw [← Finset.sum_mul]
      congr 1
      exact Finset.sum_sub_distrib _ _
    rw [hdiv, hsin_odd_b, hsin_odd_a]
    simp
  have hodd_S0 : (∑ j ∈ Finset.range n,
      ∫ φ in (θ₀ + ((2 * j + 1 : ℕ) : ℝ) * α)..
        (θ₀ + ((2 * j + 1 : ℕ) : ℝ) * α + α),
        Real.sin (2 * φ)) = 0 := by
    have hS : ∀ j : ℕ,
        (∫ φ in (θ₀ + ((2 * j + 1 : ℕ) : ℝ) * α)..
          (θ₀ + ((2 * j + 1 : ℕ) : ℝ) * α + α),
          Real.sin (2 * φ))
        = (Real.cos (2 * (θ₀ + ((2 * j + 1 : ℕ) : ℝ) * α))
          - Real.cos (2 * (θ₀ + ((2 * j + 1 : ℕ) : ℝ) * α + α))) / 2 := by
      intro j
      exact pizza_integral_sin_two _ _
    have hsum : (∑ j ∈ Finset.range n,
        ∫ φ in (θ₀ + ((2 * j + 1 : ℕ) : ℝ) * α)..
          (θ₀ + ((2 * j + 1 : ℕ) : ℝ) * α + α),
          Real.sin (2 * φ))
        = ∑ j ∈ Finset.range n,
          (Real.cos (2 * (θ₀ + ((2 * j + 1 : ℕ) : ℝ) * α))
            - Real.cos (2 * (θ₀ + ((2 * j + 1 : ℕ) : ℝ) * α + α))) / 2 :=
      Finset.sum_congr rfl (fun j _ => hS j)
    rw [hsum]
    have hdiv : (∑ j ∈ Finset.range n,
        (Real.cos (2 * (θ₀ + ((2 * j + 1 : ℕ) : ℝ) * α))
          - Real.cos (2 * (θ₀ + ((2 * j + 1 : ℕ) : ℝ) * α + α))) / 2)
        = ((∑ j ∈ Finset.range n,
          Real.cos (2 * (θ₀ + ((2 * j + 1 : ℕ) : ℝ) * α)))
          - (∑ j ∈ Finset.range n,
            Real.cos
              (2 * (θ₀ + ((2 * j + 1 : ℕ) : ℝ) * α + α)))) / 2 := by
      simp only [div_eq_mul_inv]
      rw [← Finset.sum_mul]
      congr 1
      exact Finset.sum_sub_distrib _ _
    rw [hdiv, hcos_odd_a, hcos_odd_b]
    simp
  have heven_final : (∑ j ∈ Finset.range n,
      (R ^ 2 * α + A * (∫ φ in (θ₀ + ((2 * j : ℕ) : ℝ) * α)..
        (θ₀ + ((2 * j : ℕ) : ℝ) * α + α), Real.cos (2 * φ))
        + B * (∫ φ in (θ₀ + ((2 * j : ℕ) : ℝ) * α)..
          (θ₀ + ((2 * j : ℕ) : ℝ) * α + α), Real.sin (2 * φ))))
      = ∑ j ∈ Finset.range n, R ^ 2 * α := by
    rw [Finset.sum_add_distrib]
    have h2 : (∑ j ∈ Finset.range n,
        (R ^ 2 * α + A * (∫ φ in (θ₀ + ((2 * j : ℕ) : ℝ) * α)..
          (θ₀ + ((2 * j : ℕ) : ℝ) * α + α), Real.cos (2 * φ))))
        = (∑ j ∈ Finset.range n, R ^ 2 * α)
          + A * (∑ j ∈ Finset.range n,
            ∫ φ in (θ₀ + ((2 * j : ℕ) : ℝ) * α)..
              (θ₀ + ((2 * j : ℕ) : ℝ) * α + α),
              Real.cos (2 * φ)) := by
      rw [Finset.sum_add_distrib]
      congr 1
      exact (Finset.mul_sum _ _ _).symm
    rw [h2, heven_C0]
    have h3 : (∑ j ∈ Finset.range n,
        B * (∫ φ in (θ₀ + ((2 * j : ℕ) : ℝ) * α)..
          (θ₀ + ((2 * j : ℕ) : ℝ) * α + α), Real.sin (2 * φ)))
        = B * (∑ j ∈ Finset.range n,
          ∫ φ in (θ₀ + ((2 * j : ℕ) : ℝ) * α)..
            (θ₀ + ((2 * j : ℕ) : ℝ) * α + α),
            Real.sin (2 * φ)) := by
      rw [← Finset.mul_sum]
    rw [h3, heven_S0]
    simp
  have hodd_final : (∑ j ∈ Finset.range n,
      (R ^ 2 * α + A * (∫ φ in (θ₀ + ((2 * j + 1 : ℕ) : ℝ) * α)..
        (θ₀ + ((2 * j + 1 : ℕ) : ℝ) * α + α), Real.cos (2 * φ))
        + B * (∫ φ in (θ₀ + ((2 * j + 1 : ℕ) : ℝ) * α)..
          (θ₀ + ((2 * j + 1 : ℕ) : ℝ) * α + α), Real.sin (2 * φ))))
      = ∑ j ∈ Finset.range n, R ^ 2 * α := by
    rw [Finset.sum_add_distrib]
    have h2 : (∑ j ∈ Finset.range n,
        (R ^ 2 * α + A * (∫ φ in (θ₀ + ((2 * j + 1 : ℕ) : ℝ) * α)..
          (θ₀ + ((2 * j + 1 : ℕ) : ℝ) * α + α), Real.cos (2 * φ))))
        = (∑ j ∈ Finset.range n, R ^ 2 * α)
          + A * (∑ j ∈ Finset.range n,
            ∫ φ in (θ₀ + ((2 * j + 1 : ℕ) : ℝ) * α)..
              (θ₀ + ((2 * j + 1 : ℕ) : ℝ) * α + α),
              Real.cos (2 * φ)) := by
      rw [Finset.sum_add_distrib]
      congr 1
      exact (Finset.mul_sum _ _ _).symm
    rw [h2, hodd_C0]
    have h3 : (∑ j ∈ Finset.range n,
        B * (∫ φ in (θ₀ + ((2 * j + 1 : ℕ) : ℝ) * α)..
          (θ₀ + ((2 * j + 1 : ℕ) : ℝ) * α + α), Real.sin (2 * φ)))
        = B * (∑ j ∈ Finset.range n,
          ∫ φ in (θ₀ + ((2 * j + 1 : ℕ) : ℝ) * α)..
            (θ₀ + ((2 * j + 1 : ℕ) : ℝ) * α + α),
            Real.sin (2 * φ)) := by
      rw [← Finset.mul_sum]
    rw [h3, hodd_S0]
    simp
  rw [heven_final, hodd_final]

end
end MetaMathlibExt
