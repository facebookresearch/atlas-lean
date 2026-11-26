/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Round
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Tactic

/-! # Fourier expansion of a power of the distance to the nearest integer

The Fourier coefficients of the $k$-th power of the distance from a real number to the nearest
integer decay like $O(1/m^2)$, are summable, and their symmetric partial sums converge
uniformly to the function, with an $O(1/H)$ tail bound.
-/

open Filter Topology Set intervalIntegral MeasureTheory

open scoped Interval

namespace MetaMathlibExt

@[expose] public section

namespace dist_round_pow_fourier_expansion

/-- The $k$-th power of the distance to the nearest integer. -/
private noncomputable def gFun (k : ℕ) (u : ℝ) : ℝ := |u - round u| ^ k

/-- The $m$-th Fourier coefficient of `gFun k` over one period. -/
private noncomputable def cFun (k : ℕ) (m : ℤ) : ℂ :=
  ∫ u in (0 : ℝ)..1, (gFun k u : ℂ) *
    Complex.exp (-(2 * Real.pi * Complex.I * (m : ℂ) * (u : ℂ)))

private lemma gFun_add_int (k : ℕ) (u : ℝ) (n : ℤ) : gFun k (u + n) = gFun k u := by
  have hsub : (u + (n : ℝ)) - ((round u + n : ℤ) : ℝ) = u - (round u : ℝ) := by
    push_cast
    ring
  simp only [gFun, round_add_intCast, hsub]

private lemma gFun_fract (k : ℕ) (u : ℝ) : gFun k (Int.fract u) = gFun k u := by
  have h : Int.fract u = u + ((-⌊u⌋ : ℤ) : ℝ) := by rw [Int.fract]; push_cast; ring
  rw [h, gFun_add_int]

private lemma continuous_gFun (k : ℕ) : Continuous (gFun k) := by
  have h : gFun k = (fun t : ℝ => (min t (1 - t)) ^ k) ∘ Int.fract := by
    funext u
    simp only [Function.comp_apply, gFun, abs_sub_round_eq_min]
  rw [h]
  have hcont : Continuous fun t : ℝ => (min t (1 - t)) ^ k := by fun_prop
  exact ContinuousOn.comp_fract'' hcont.continuousOn (by simp)

private lemma gFun_zero (k : ℕ) (hk : 1 ≤ k) : gFun k 0 = 0 := by
  simp [gFun, zero_pow (by omega : k ≠ 0)]

private lemma gFun_one (k : ℕ) (hk : 1 ≤ k) : gFun k 1 = 0 := by
  simp [gFun, zero_pow (by omega : k ≠ 0)]

private lemma gFun_eq_pow_uIcc {k : ℕ} {x : ℝ} (hx : x ∈ Set.uIcc (0 : ℝ) (1 / 2)) :
    gFun k x = x ^ k := by
  rw [Set.uIcc, Set.mem_Icc] at hx
  simp only [min_eq_left (by norm_num : (0 : ℝ) ≤ 1 / 2),
    max_eq_right (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hx
  rcases hx.2.lt_or_eq with hlt | heq
  · have hr : round x = 0 := by
      rw [round_eq, Int.floor_eq_zero_iff]
      exact ⟨by linarith, by linarith⟩
    simp only [gFun, hr, Int.cast_zero, sub_zero, abs_of_nonneg hx.1]
  · subst heq
    have hr12 : round (1 / 2 : ℝ) = 1 := by norm_num [round_eq]
    have h2 : |(1 / 2 : ℝ) - ((1 : ℤ) : ℝ)| = 1 / 2 := by norm_num
    simp only [gFun, hr12, h2]

private lemma gFun_eq_one_sub_pow_uIcc {k : ℕ} {x : ℝ} (hx : x ∈ Set.uIcc (1 / 2 : ℝ) 1) :
    gFun k x = (1 - x) ^ k := by
  rw [Set.uIcc, Set.mem_Icc] at hx
  simp only [min_eq_left (by norm_num : (1 / 2 : ℝ) ≤ 1),
    max_eq_right (by norm_num : (1 / 2 : ℝ) ≤ 1)] at hx
  have hr : round x = 1 := by
    rw [round_eq]
    rw [Int.floor_eq_iff]
    norm_num
    constructor <;> linarith [hx.1, hx.2]
  simp [gFun, hr, abs_of_nonpos (by linarith : x - 1 ≤ 0)]

private lemma gFun_nonneg (k : ℕ) (u : ℝ) : 0 ≤ gFun k u :=
  pow_nonneg (abs_nonneg _) _

/-- Integration by parts against a complex exponential, once. -/
private lemma ibp_once {a b : ℝ} {c : ℂ} (hc : c ≠ 0) {u u' : ℝ → ℝ}
    (hu : ∀ x, HasDerivAt u (u' x) x)
    (hu' : IntervalIntegrable (fun x => (u' x : ℂ)) volume a b) :
    ∫ x in a..b, (u x : ℂ) * Complex.exp (c * (x : ℂ)) =
      (u b : ℂ) * (Complex.exp (c * (b : ℂ)) / c) - (u a : ℂ) * (Complex.exp (c * (a : ℂ)) / c)
        - ∫ x in a..b, (u' x : ℂ) * (Complex.exp (c * (x : ℂ)) / c) := by
  have hE : ∀ x : ℝ, HasDerivAt (fun y : ℝ => Complex.exp (c * (y : ℂ)) / c)
      (Complex.exp (c * (x : ℂ))) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℂ => Complex.exp (c * y))
        (c * Complex.exp (c * (x : ℂ))) (x : ℂ) := by
      simpa [mul_comm] using ((hasDerivAt_id (x : ℂ)).const_mul c).cexp
    have h2 := h1.comp_ofReal.div_const c
    convert h2 using 1
    rw [mul_div_cancel_left₀ _ hc]
  have hU : ∀ x, HasDerivAt (fun y : ℝ => (u y : ℂ)) ((u' x : ℂ)) x :=
    fun x => (hu x).ofReal_comp
  have hcontU : ContinuousOn (fun y : ℝ => (u y : ℂ)) (Set.uIcc a b) :=
    fun x _ => (hU x).continuousAt.continuousWithinAt
  have hcontE : ContinuousOn (fun y : ℝ => Complex.exp (c * (y : ℂ)) / c) (Set.uIcc a b) :=
    fun x _ => (hE x).continuousAt.continuousWithinAt
  have hEint : IntervalIntegrable (fun x => Complex.exp (c * (x : ℂ))) volume a b :=
    (Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal)).intervalIntegrable a b
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt hcontU hcontE
    (fun x _ => hU x) (fun x _ => hE x) hu' hEint
  exact h

private lemma hasDerivAt_u2 (k : ℕ) (x : ℝ) :
    HasDerivAt (fun x : ℝ => (1 - x) ^ k) (-((k : ℝ) * (1 - x) ^ (k - 1))) x := by
  have hdiff : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by
    simpa using (hasDerivAt_id x).const_sub (1 : ℝ)
  rw [show (fun x : ℝ => (1 - x) ^ k) = (fun x => x ^ k) ∘ (fun x => 1 - x) from rfl]
  exact ((hasDerivAt_pow k (1 - x)).comp x hdiff).congr_deriv (by ring)

private lemma hasDerivAt_u2' (k : ℕ) (x : ℝ) :
    HasDerivAt (fun x : ℝ => -((k : ℝ) * (1 - x) ^ (k - 1)))
      ((k : ℝ) * (((k - 1 : ℕ) : ℝ) * (1 - x) ^ (k - 1 - 1))) x := by
  have hdiff : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by
    simpa using (hasDerivAt_id x).const_sub (1 : ℝ)
  rw [show (fun x : ℝ => -((k : ℝ) * (1 - x) ^ (k - 1))) =
    (fun y : ℝ => -((k : ℝ) * y)) ∘ (fun x : ℝ => (1 - x) ^ (k - 1)) from rfl]
  have hW : HasDerivAt (fun x : ℝ => (1 - x) ^ (k - 1))
      (((k - 1 : ℕ) : ℝ) * (1 - x) ^ (k - 1 - 1) * (-1)) x := by
    rw [show (fun x : ℝ => (1 - x) ^ (k - 1)) = (fun x => x ^ (k - 1)) ∘ (fun x => 1 - x) from rfl]
    exact (hasDerivAt_pow (k - 1) (1 - x)).comp x hdiff
  exact (hW.const_mul (k : ℝ)).neg.congr_deriv (by ring)

private lemma norm_sub_boundary_le {a b : ℝ} (hab : a ≤ b) {c : ℂ} (hc : c ≠ 0)
    (hexp : ∀ x : ℝ, ‖Complex.exp (c * (x : ℂ))‖ = 1)
    {u u' u'' : ℝ → ℝ}
    (hu : ∀ x, HasDerivAt u (u' x) x) (hu' : ∀ x, HasDerivAt u' (u'' x) x)
    (hcont' : Continuous u') (hcont'' : Continuous u'')
    {B₁ B₂ : ℝ}
    (hbound' : ∀ x ∈ Set.Icc a b, |u' x| ≤ B₁)
    (hbound'' : ∀ x ∈ Set.Icc a b, |u'' x| ≤ B₂) :
    ‖(∫ x in a..b, (u x : ℂ) * Complex.exp (c * (x : ℂ)))
      - ((u b : ℂ) * (Complex.exp (c * (b : ℂ)) / c) -
        (u a : ℂ) * (Complex.exp (c * (a : ℂ)) / c))‖
      ≤ (2 * B₁ + (b - a) * B₂) / ‖c‖ ^ 2 := by
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hcne : ‖c‖ ≠ 0 := hcpos.ne'
  have hEnorm : ∀ x : ℝ, ‖Complex.exp (c * (x : ℂ)) / c‖ = 1 / ‖c‖ := fun x => by
    rw [norm_div, hexp, one_div]
  have hint' : IntervalIntegrable (fun x => (u' x : ℂ)) volume a b :=
    (by fun_prop : Continuous fun x => (u' x : ℂ)).intervalIntegrable a b
  have hint'' : IntervalIntegrable (fun x => (u'' x : ℂ)) volume a b :=
    (by fun_prop : Continuous fun x => (u'' x : ℂ)).intervalIntegrable a b
  have h1 := ibp_once hc hu hint'
  have h2 := ibp_once hc hu' hint''
  have hJ : (∫ x in a..b, (u' x : ℂ) * (Complex.exp (c * (x : ℂ)) / c))
      = (∫ x in a..b, (u' x : ℂ) * Complex.exp (c * (x : ℂ))) / c := by
    rw [← intervalIntegral.integral_div]
    apply intervalIntegral.integral_congr
    intro x _
    simp only [mul_div_assoc]
  have hId : (∫ x in a..b, (u x : ℂ) * Complex.exp (c * (x : ℂ)))
      - ((u b : ℂ) * (Complex.exp (c * (b : ℂ)) / c) -
        (u a : ℂ) * (Complex.exp (c * (a : ℂ)) / c))
      = -(((u' b : ℂ) * (Complex.exp (c * (b : ℂ)) / c) -
        (u' a : ℂ) * (Complex.exp (c * (a : ℂ)) / c)
        - ∫ x in a..b, (u'' x : ℂ) * (Complex.exp (c * (x : ℂ)) / c)) / c) := by
    rw [h1, hJ, h2]
    ring
  have e1 : ∀ x : ℝ, ‖(u' x : ℂ)‖ = |u' x| := fun x => by simp
  have hB' : ‖(u' b : ℂ) * (Complex.exp (c * (b : ℂ)) / c) -
      (u' a : ℂ) * (Complex.exp (c * (a : ℂ)) / c)‖ ≤ 2 * B₁ / ‖c‖ := by
    calc ‖(u' b : ℂ) * (Complex.exp (c * (b : ℂ)) / c) -
          (u' a : ℂ) * (Complex.exp (c * (a : ℂ)) / c)‖
        ≤ ‖(u' b : ℂ) * (Complex.exp (c * (b : ℂ)) / c)‖ +
          ‖(u' a : ℂ) * (Complex.exp (c * (a : ℂ)) / c)‖ := norm_sub_le _ _
      _ = |u' b| * (1 / ‖c‖) + |u' a| * (1 / ‖c‖) := by
          rw [norm_mul, norm_mul, hEnorm, hEnorm, e1, e1]
      _ ≤ B₁ * (1 / ‖c‖) + B₁ * (1 / ‖c‖) := by
          gcongr
          · exact hbound' b ⟨hab, le_rfl⟩
          · exact hbound' a ⟨le_rfl, hab⟩
      _ = 2 * B₁ / ‖c‖ := by
          field_simp
          ring
  have hK : ‖∫ x in a..b, (u'' x : ℂ) * (Complex.exp (c * (x : ℂ)) / c)‖
      ≤ (b - a) * B₂ / ‖c‖ := by
    have hle := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
      (C := B₂ * (1 / ‖c‖))
      (f := fun x => (u'' x : ℂ) * (Complex.exp (c * (x : ℂ)) / c)) (by
      intro x hx
      rw [Set.uIoc_of_le hab] at hx
      calc ‖(u'' x : ℂ) * (Complex.exp (c * (x : ℂ)) / c)‖
          = |u'' x| * (1 / ‖c‖) := by
            rw [norm_mul, hEnorm]
            simp
        _ ≤ B₂ * (1 / ‖c‖) := by
            gcongr
            · exact hbound'' x (Set.Ioc_subset_Icc_self hx))
    rw [abs_of_nonneg (sub_nonneg.mpr hab)] at hle
    calc ‖∫ x in a..b, (u'' x : ℂ) * (Complex.exp (c * (x : ℂ)) / c)‖
        ≤ B₂ * (1 / ‖c‖) * (b - a) := hle
      _ = (b - a) * B₂ / ‖c‖ := by
          field_simp
  calc ‖(∫ x in a..b, (u x : ℂ) * Complex.exp (c * (x : ℂ)))
        - ((u b : ℂ) * (Complex.exp (c * (b : ℂ)) / c) -
          (u a : ℂ) * (Complex.exp (c * (a : ℂ)) / c))‖
      = ‖(u' b : ℂ) * (Complex.exp (c * (b : ℂ)) / c) -
          (u' a : ℂ) * (Complex.exp (c * (a : ℂ)) / c)
          - ∫ x in a..b, (u'' x : ℂ) * (Complex.exp (c * (x : ℂ)) / c)‖ / ‖c‖ := by
        rw [hId, norm_neg, norm_div]
    _ ≤ (‖(u' b : ℂ) * (Complex.exp (c * (b : ℂ)) / c) -
          (u' a : ℂ) * (Complex.exp (c * (a : ℂ)) / c)‖ +
          ‖∫ x in a..b, (u'' x : ℂ) * (Complex.exp (c * (x : ℂ)) / c)‖) / ‖c‖ :=
        by gcongr; exact norm_sub_le _ _
    _ ≤ (2 * B₁ / ‖c‖ + (b - a) * B₂ / ‖c‖) / ‖c‖ :=
        by gcongr
    _ = (2 * B₁ + (b - a) * B₂) / ‖c‖ ^ 2 := by
        field_simp

private lemma cFun_zero (k : ℕ) (hk : 1 ≤ k) :
    cFun k 0 = ((1 / (2 ^ k * ((k : ℝ) + 1)) : ℝ) : ℂ) := by
  have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
  rw [cFun]
  simp only [Int.cast_zero, mul_zero, zero_mul, neg_zero, Complex.exp_zero, mul_one]
  rw [intervalIntegral.integral_ofReal]
  have hint1 : IntervalIntegrable (gFun k) volume (0 : ℝ) (1 / 2) :=
    (continuous_gFun k).intervalIntegrable _ _
  have hint2 : IntervalIntegrable (gFun k) volume (1 / 2 : ℝ) 1 :=
    (continuous_gFun k).intervalIntegrable _ _
  have hsplit : (∫ u in (0 : ℝ)..1, gFun k u)
      = (∫ u in (0 : ℝ)..(1 / 2), u ^ k) + (∫ u in (1 / 2 : ℝ)..1, (1 - u) ^ k) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
    congr 1
    · exact intervalIntegral.integral_congr (fun x hx => gFun_eq_pow_uIcc hx)
    · exact intervalIntegral.integral_congr (fun x hx => gFun_eq_one_sub_pow_uIcc hx)
  have h1 : (∫ u in (0 : ℝ)..(1 / 2), u ^ k) = (1 / 2 : ℝ) ^ (k + 1) / ((k : ℝ) + 1) := by
    rw [integral_pow]
    simp [zero_pow (by omega : k + 1 ≠ 0)]
  have h2 : (∫ u in (1 / 2 : ℝ)..1, (1 - u) ^ k) = ∫ u in (0 : ℝ)..(1 / 2), u ^ k := by
    simpa only [sub_self, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] using
      (intervalIntegral.integral_comp_sub_left (a := (1 / 2 : ℝ)) (b := 1) (fun u => u ^ k) 1)
  rw [hsplit, h2, h1]
  congr 1
  have hA : (1 / 2 : ℝ) ^ (k + 1) = 1 / 2 ^ (k + 1) := by rw [div_pow, one_pow, one_div]
  rw [hA, pow_succ (2 : ℝ) k]
  field_simp
  ring

private lemma coeff_bound {k : ℕ} (hk : 1 ≤ k) {m : ℤ} (hm : m ≠ 0) :
    ‖cFun k m‖ ≤ (k : ℝ) * ((k : ℝ) + 4) / (m : ℝ) ^ 2 := by
  set c : ℂ := -(2 * Real.pi * Complex.I * (m : ℂ)) with hcdef
  have hc : c ≠ 0 := by
    rw [hcdef]
    simp [hm, Real.pi_ne_zero]
  have hexp : ∀ x : ℝ, ‖Complex.exp (c * (x : ℂ))‖ = 1 := by
    intro x
    have e : c * (x : ℂ) = ((-(2 * Real.pi * (m : ℝ) * x) : ℝ) : ℂ) * Complex.I := by
      rw [hcdef]
      push_cast
      ring
    rw [e, Complex.norm_exp_ofReal_mul_I]
  have hcont : Continuous fun u => (gFun k u : ℂ) *
      Complex.exp (-(2 * Real.pi * Complex.I * (m : ℂ) * (u : ℂ))) :=
    (Complex.continuous_ofReal.comp (continuous_gFun k)).mul
      (Complex.continuous_exp.comp (by fun_prop))
  have hint1 : IntervalIntegrable (fun u => (gFun k u : ℂ) *
      Complex.exp (-(2 * Real.pi * Complex.I * (m : ℂ) * (u : ℂ)))) volume (0 : ℝ) (1 / 2) :=
    hcont.intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun u => (gFun k u : ℂ) *
      Complex.exp (-(2 * Real.pi * Complex.I * (m : ℂ) * (u : ℂ)))) volume (1 / 2 : ℝ) 1 :=
    hcont.intervalIntegrable _ _
  have hsplit : cFun k m
      = (∫ x in (0 : ℝ)..(1 / 2), ((x ^ k : ℝ) : ℂ) * Complex.exp (c * (x : ℂ)))
        + (∫ x in (1 / 2 : ℝ)..1, (((1 - x) ^ k : ℝ) : ℂ) * Complex.exp (c * (x : ℂ))) := by
    rw [cFun, ← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
    refine congrArg₂ (· + ·) ?_ ?_ <;>
      apply intervalIntegral.integral_congr <;> intro x hx <;> dsimp only
    · rw [gFun_eq_pow_uIcc hx]
      congr 1
      rw [hcdef]
      ring_nf
    · rw [gFun_eq_one_sub_pow_uIcc hx]
      congr 1
      rw [hcdef]
      ring_nf
  have hcont1' : Continuous fun x : ℝ => (k : ℝ) * x ^ (k - 1) := by fun_prop
  have hcont1'' : Continuous fun x : ℝ => (k : ℝ) * (((k - 1 : ℕ) : ℝ) * x ^ (k - 1 - 1)) := by
    fun_prop
  have hcont2' : Continuous fun x : ℝ => -((k : ℝ) * (1 - x) ^ (k - 1)) := by fun_prop
  have hcont2'' : Continuous fun x : ℝ =>
      (k : ℝ) * (((k - 1 : ℕ) : ℝ) * (1 - x) ^ (k - 1 - 1)) := by
    fun_prop
  have hbound1' : ∀ x ∈ Set.Icc (0 : ℝ) (1 / 2), |(k : ℝ) * x ^ (k - 1)| ≤ (k : ℝ) := by
    intro x hx
    have hx0 : 0 ≤ x := hx.1
    have hx1 : x ≤ 1 := hx.2.trans (by norm_num)
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (pow_nonneg hx0 _)]
    calc (k : ℝ) * x ^ (k - 1) ≤ (k : ℝ) * 1 := by
          gcongr
          exact pow_le_one₀ hx0 hx1
      _ = (k : ℝ) := mul_one _
  have hbound1'' : ∀ x ∈ Set.Icc (0 : ℝ) (1 / 2),
      |(k : ℝ) * (((k - 1 : ℕ) : ℝ) * x ^ (k - 1 - 1))| ≤ (k : ℝ) ^ 2 := by
    intro x hx
    have hx0 : 0 ≤ x := hx.1
    have hx1 : x ≤ 1 := hx.2.trans (by norm_num)
    have hp : x ^ (k - 1 - 1) ≤ 1 := pow_le_one₀ hx0 hx1
    have hcast : ((k - 1 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.sub_le k 1
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    calc (k : ℝ) * |((k - 1 : ℕ) : ℝ) * x ^ (k - 1 - 1)|
        ≤ (k : ℝ) * ((k : ℝ) * 1) := by
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
          rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (pow_nonneg hx0 _)]
          exact mul_le_mul hcast hp (pow_nonneg hx0 _) (Nat.cast_nonneg _)
      _ = (k : ℝ) ^ 2 := by ring
  have hbound2' : ∀ x ∈ Set.Icc (1 / 2 : ℝ) 1, |-((k : ℝ) * (1 - x) ^ (k - 1))| ≤ (k : ℝ) := by
    intro x hx
    have hx0 : 0 ≤ 1 - x := by linarith [hx.2]
    have hx1 : 1 - x ≤ 1 := by linarith [hx.1]
    rw [abs_neg, abs_mul, abs_of_nonneg (Nat.cast_nonneg _),
      abs_of_nonneg (pow_nonneg hx0 _)]
    calc (k : ℝ) * (1 - x) ^ (k - 1) ≤ (k : ℝ) * 1 := by
          gcongr
          exact pow_le_one₀ hx0 hx1
      _ = (k : ℝ) := mul_one _
  have hbound2'' : ∀ x ∈ Set.Icc (1 / 2 : ℝ) 1,
      |(k : ℝ) * (((k - 1 : ℕ) : ℝ) * (1 - x) ^ (k - 1 - 1))| ≤ (k : ℝ) ^ 2 := by
    intro x hx
    have hx0 : 0 ≤ 1 - x := by linarith [hx.2]
    have hx1 : 1 - x ≤ 1 := by linarith [hx.1]
    have hp : (1 - x) ^ (k - 1 - 1) ≤ 1 := pow_le_one₀ hx0 hx1
    have hcast : ((k - 1 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.sub_le k 1
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    calc (k : ℝ) * |((k - 1 : ℕ) : ℝ) * (1 - x) ^ (k - 1 - 1)|
        ≤ (k : ℝ) * ((k : ℝ) * 1) := by
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
          rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (pow_nonneg hx0 _)]
          exact mul_le_mul hcast hp (pow_nonneg hx0 _) (Nat.cast_nonneg _)
      _ = (k : ℝ) ^ 2 := by ring
  have hb1 := norm_sub_boundary_le (a := (0 : ℝ)) (b := 1 / 2) (by norm_num) hc hexp
    (hasDerivAt_pow k) (fun x => (hasDerivAt_pow (k - 1) x).const_mul (k : ℝ)) hcont1' hcont1''
    hbound1' hbound1''
  have hb2 := norm_sub_boundary_le (a := (1 / 2 : ℝ)) (b := 1) (by norm_num) hc hexp
    (hasDerivAt_u2 k) (hasDerivAt_u2' k) hcont2' hcont2'' hbound2' hbound2''
  have hB : (↑((1 / 2 : ℝ) ^ k) * (Complex.exp (c * ((1 / 2 : ℝ) : ℂ)) / c)
      - ↑((0 : ℝ) ^ k) * (Complex.exp (c * ((0 : ℝ) : ℂ)) / c))
      + (↑((1 - 1 : ℝ) ^ k) * (Complex.exp (c * ((1 : ℝ) : ℂ)) / c)
      - ↑((1 - 1 / 2 : ℝ) ^ k) * (Complex.exp (c * ((1 / 2 : ℝ) : ℂ)) / c)) = 0 := by
    rw [show ((1 : ℝ) - 1) = 0 by norm_num, show ((1 : ℝ) - 1 / 2) = 1 / 2 by norm_num]
    simp [zero_pow (by omega : k ≠ 0)]
  have htot : ‖cFun k m‖ ≤ (2 * (2 * (k : ℝ) + (1 / 2) * (k : ℝ) ^ 2)) / ‖c‖ ^ 2 := by
    rw [hsplit]
    have hb1' : ‖(∫ x in (0 : ℝ)..(1 / 2), ((x ^ k : ℝ) : ℂ) * Complex.exp (c * (x : ℂ)))
        - (↑((1 / 2 : ℝ) ^ k) * (Complex.exp (c * ((1 / 2 : ℝ) : ℂ)) / c)
        - ↑((0 : ℝ) ^ k) * (Complex.exp (c * ((0 : ℝ) : ℂ)) / c))‖
        ≤ (2 * (k : ℝ) + (1 / 2 - 0) * (k : ℝ) ^ 2) / ‖c‖ ^ 2 := hb1
    have hb2' : ‖(∫ x in (1 / 2 : ℝ)..1, (((1 - x) ^ k : ℝ) : ℂ) * Complex.exp (c * (x : ℂ)))
        - (↑((1 - 1 : ℝ) ^ k) * (Complex.exp (c * ((1 : ℝ) : ℂ)) / c)
        - ↑((1 - 1 / 2 : ℝ) ^ k) * (Complex.exp (c * ((1 / 2 : ℝ) : ℂ)) / c))‖
        ≤ (2 * (k : ℝ) + (1 - 1 / 2) * (k : ℝ) ^ 2) / ‖c‖ ^ 2 := hb2
    have hsum : ∀ (I1 I2 B1 B2 : ℂ), B1 + B2 = 0 → ‖I1 + I2‖ ≤ ‖I1 - B1‖ + ‖I2 - B2‖ := by
      intro I1 I2 B1 B2 h
      have heq : I1 + I2 = (I1 - B1) + (I2 - B2) := by
        rw [show (I1 - B1) + (I2 - B2) = (I1 + I2) - (B1 + B2) from by ring, h, sub_zero]
      rw [heq]
      exact norm_add_le _ _
    calc ‖(∫ x in (0 : ℝ)..(1 / 2), ((x ^ k : ℝ) : ℂ) * Complex.exp (c * (x : ℂ)))
          + (∫ x in (1 / 2 : ℝ)..1, (((1 - x) ^ k : ℝ) : ℂ) * Complex.exp (c * (x : ℂ)))‖
        ≤ ‖(∫ x in (0 : ℝ)..(1 / 2), ((x ^ k : ℝ) : ℂ) * Complex.exp (c * (x : ℂ)))
          - (↑((1 / 2 : ℝ) ^ k) * (Complex.exp (c * ((1 / 2 : ℝ) : ℂ)) / c)
          - ↑((0 : ℝ) ^ k) * (Complex.exp (c * ((0 : ℝ) : ℂ)) / c))‖
          + ‖(∫ x in (1 / 2 : ℝ)..1, (((1 - x) ^ k : ℝ) : ℂ) * Complex.exp (c * (x : ℂ)))
          - (↑((1 - 1 : ℝ) ^ k) * (Complex.exp (c * ((1 : ℝ) : ℂ)) / c)
          - ↑((1 - 1 / 2 : ℝ) ^ k) * (Complex.exp (c * ((1 / 2 : ℝ) : ℂ)) / c))‖ :=
        hsum _ _ _ _ hB
      _ ≤ (2 * (k : ℝ) + (1 / 2 - 0) * (k : ℝ) ^ 2) / ‖c‖ ^ 2
          + (2 * (k : ℝ) + (1 - 1 / 2) * (k : ℝ) ^ 2) / ‖c‖ ^ 2 :=
        add_le_add hb1' hb2'
      _ = (2 * (2 * (k : ℝ) + (1 / 2) * (k : ℝ) ^ 2)) / ‖c‖ ^ 2 := by ring
  have hnormc : ‖c‖ = 2 * Real.pi * |(m : ℝ)| := by
    rw [hcdef]
    simp [Complex.norm_I]
  have hden : (m : ℝ) ^ 2 ≤ ‖c‖ ^ 2 := by
    rw [hnormc, mul_pow, sq_abs]
    have hpi : (1 : ℝ) ≤ (2 * Real.pi) ^ 2 := by nlinarith [Real.pi_gt_three]
    calc (m : ℝ) ^ 2 = 1 * (m : ℝ) ^ 2 := (one_mul _).symm
      _ ≤ (2 * Real.pi) ^ 2 * (m : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hpi (sq_nonneg _)
  calc ‖cFun k m‖ ≤ (2 * (2 * (k : ℝ) + (1 / 2) * (k : ℝ) ^ 2)) / ‖c‖ ^ 2 := htot
    _ = (k : ℝ) * ((k : ℝ) + 4) / ‖c‖ ^ 2 := by congr 1; ring
    _ ≤ (k : ℝ) * ((k : ℝ) + 4) / (m : ℝ) ^ 2 :=
      div_le_div_of_nonneg_left (by positivity)
        (sq_pos_of_ne_zero (Int.cast_ne_zero.mpr hm)) hden

/-- The complex-valued version of `gFun`. -/
private noncomputable def gFunC (k : ℕ) (u : ℝ) : ℂ := (gFun k u : ℂ)

private lemma continuous_gFunC (k : ℕ) : Continuous (gFunC k) :=
  Complex.continuous_ofReal.comp (continuous_gFun k)

private lemma norm_exp_term (m : ℤ) (u : ℝ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (u : ℂ))‖ = 1 := by
  have e : 2 * Real.pi * Complex.I * (m : ℂ) * (u : ℂ)
      = ((2 * Real.pi * (m : ℝ) * u : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [e, Complex.norm_exp_ofReal_mul_I]

/-- The periodic function on the circle obtained from `gFun k`. -/
private noncomputable def fCirc (k : ℕ) (hk : 1 ≤ k) : C(AddCircle (1 : ℝ), ℂ) :=
  ⟨AddCircle.liftIoc (1 : ℝ) (0 : ℝ) (gFunC k),
    AddCircle.liftIoc_zero_continuous
      (by simp [gFunC, gFun_zero k hk, gFun_one k hk])
      (continuous_gFunC k).continuousOn⟩

private lemma fourierCoeff_fCirc (k : ℕ) (hk : 1 ≤ k) :
    fourierCoeff (fCirc k hk) = cFun k := by
  funext m
  change fourierCoeff (AddCircle.liftIoc 1 0 (gFunC k)) m = cFun k m
  rw [fourierCoeff_liftIoc_eq, fourierCoeffOn_eq_integral, cFun]
  simp only [zero_add, sub_zero, div_one, one_smul]
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only
  rw [fourier_coe_apply, smul_eq_mul]
  simp only [gFunC]
  rw [mul_comm]
  congr 1
  push_cast
  ring_nf

private lemma summable_norm_cFun (k : ℕ) (hk : 1 ≤ k) :
    Summable (fun m : ℤ => ‖cFun k m‖) := by
  apply Summable.of_norm_bounded_eventually
    (g := fun m : ℤ => (k : ℝ) * ((k : ℝ) + 4) / (m : ℝ) ^ 2)
  · have hsum : Summable (fun n : ℤ => 1 / (n : ℝ) ^ 2) :=
      (Real.summable_one_div_int_pow (p := 2)).mpr (by norm_num)
    have hmul := hsum.mul_left ((k : ℝ) * ((k : ℝ) + 4))
    apply hmul.congr
    intro n
    simp only [one_div]
    rw [div_eq_mul_one_div, one_div]
  · refine Filter.eventually_cofinite.mpr ?_
    refine (Set.finite_singleton (0 : ℤ)).subset ?_
    intro m hm
    by_contra h0
    have hne : m ≠ 0 := by simpa using h0
    exact hm (by
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      exact coeff_bound (m := m) hk hne)

private lemma hasSum_term_Icc {k : ℕ} (hk : 1 ≤ k) {v : ℝ} (hv : v ∈ Set.Icc (0 : ℝ) 1) :
    HasSum (fun m : ℤ => cFun k m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (v : ℂ)))
      ((gFun k v : ℂ)) := by
  have hfact : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  have hsum : Summable (fourierCoeff (fCirc k hk)) := by
    rw [fourierCoeff_fCirc k hk]
    exact (summable_norm_cFun k hk).of_norm
  by_cases hv0 : v = 0
  · subst hv0
    have h01 : ((0 : ℝ) : AddCircle (1 : ℝ)) = ((1 : ℝ) : AddCircle (1 : ℝ)) := by
      have h := AddCircle.coe_add_period (1 : ℝ) (0 : ℝ)
      rw [show (0 : ℝ) + 1 = 1 from by norm_num] at h
      exact h.symm
    have hp := has_pointwise_sum_fourier_series_of_summable hsum ((1 : ℝ) : AddCircle (1 : ℝ))
    rw [← h01] at hp
    have hF : (fCirc k hk) ((0 : ℝ) : AddCircle (1 : ℝ)) = (gFun k 0 : ℂ) := by
      rw [h01]
      have hco := AddCircle.liftIoc_coe_apply (p := 1) (a := 0) (f := gFunC k) (x := 1)
        (by simp : (1 : ℝ) ∈ Set.Ioc 0 (0 + 1))
      change (fCirc k hk) ((1 : ℝ) : AddCircle (1 : ℝ)) = (gFun k 0 : ℂ)
      rw [show (fCirc k hk) ((1 : ℝ) : AddCircle (1 : ℝ)) = gFunC k 1 from hco]
      simp [gFunC, gFun_zero k hk, gFun_one k hk]
    rw [hF] at hp
    apply hp.congr_fun
    intro m
    rw [fourierCoeff_fCirc k hk, smul_eq_mul, fourier_coe_apply]
    simp [div_one]
  · have hvIoc : v ∈ Set.Ioc (0 : ℝ) (0 + 1) :=
      ⟨lt_of_le_of_ne hv.1 (Ne.symm hv0), by simpa using hv.2⟩
    have hF : (fCirc k hk) ((v : ℝ) : AddCircle (1 : ℝ)) = (gFun k v : ℂ) := by
      have hco := AddCircle.liftIoc_coe_apply (p := 1) (a := 0) (f := gFunC k) (x := v) hvIoc
      change (fCirc k hk) ((v : ℝ) : AddCircle (1 : ℝ)) = (gFun k v : ℂ)
      exact hco
    have hp := has_pointwise_sum_fourier_series_of_summable hsum ((v : ℝ) : AddCircle (1 : ℝ))
    rw [hF] at hp
    apply hp.congr_fun
    intro m
    rw [fourierCoeff_fCirc k hk, smul_eq_mul, fourier_coe_apply]
    simp only [Complex.ofReal_one, div_one]

private lemma hasSum_term (k : ℕ) (hk : 1 ≤ k) (u : ℝ) :
    HasSum (fun m : ℤ => cFun k m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (u : ℂ)))
      ((gFun k u : ℂ)) := by
  set v : ℝ := Int.fract u with hvdef
  have hvIcc : v ∈ Set.Icc (0 : ℝ) 1 := ⟨Int.fract_nonneg u, (Int.fract_lt_one u).le⟩
  have hu_eq : u = v + (⌊u⌋ : ℝ) := by
    have h := Int.self_sub_floor (a := u)
    rw [hvdef]
    linarith
  have hg : gFun k u = gFun k v := by
    rw [hu_eq]
    exact gFun_add_int k v ⌊u⌋
  have hexp_eq : ∀ m : ℤ, Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (u : ℂ))
      = Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (v : ℂ)) := by
    intro m
    have huC : (u : ℂ) = (v : ℂ) + ((⌊u⌋ : ℤ) : ℂ) := by
      have h := congrArg (fun x : ℝ => (x : ℂ)) hu_eq
      push_cast at h
      exact h
    have e : 2 * Real.pi * Complex.I * (m : ℂ) * (u : ℂ)
        = 2 * Real.pi * Complex.I * (m : ℂ) * (v : ℂ)
          + ((m * ⌊u⌋ : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      rw [huC]
      push_cast
      ring
    rw [e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hkv := hasSum_term_Icc hk hvIcc
  rw [← hg] at hkv
  exact hkv.congr_fun (fun m => by rw [hexp_eq m])

private lemma uniform_tsum (k : ℕ) (hk : 1 ≤ k) :
    TendstoUniformly
      (fun (H : ℕ) (u : ℝ) => ∑ m ∈ Finset.Icc (-(H : ℤ)) H,
        cFun k m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (u : ℂ)))
      (fun u => ∑' m : ℤ, cFun k m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (u : ℂ)))
      atTop := by
  have hboundexp : ∀ (m : ℤ) (u : ℝ),
      ‖cFun k m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (u : ℂ))‖ ≤ ‖cFun k m‖ := by
    intro m u
    rw [norm_mul, norm_exp_term, mul_one]
  have hU := tendstoUniformly_tsum (summable_norm_cFun k hk) hboundexp
  intro u hu
  have h1 := hU u hu
  rw [Filter.eventually_atTop] at h1
  obtain ⟨s0, hs0⟩ := h1
  filter_upwards [eventually_ge_atTop (s0.sup fun m => m.natAbs)] with H hH x
  apply hs0
  intro m hm
  rw [Finset.mem_Icc]
  have hleN : m.natAbs ≤ s0.sup (fun m => m.natAbs) := Finset.le_sup hm
  have hleZ : ((m.natAbs : ℕ) : ℤ) ≤ (H : ℤ) := by exact_mod_cast le_trans hleN hH
  constructor
  · exact le_trans (by exact_mod_cast neg_le_neg hleZ :
        -(H : ℤ) ≤ -(((m.natAbs : ℕ) : ℤ))) (by omega : -(((m.natAbs : ℕ) : ℤ)) ≤ m)
  · exact le_trans Int.le_natAbs hleZ

private lemma uniform (k : ℕ) (hk : 1 ≤ k) :
    TendstoUniformly
      (fun (H : ℕ) (u : ℝ) => ∑ m ∈ Finset.Icc (-(H : ℤ)) H,
        cFun k m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (u : ℂ)))
      (fun u => (gFun k u : ℂ)) atTop := by
  have h := uniform_tsum k hk
  have hEq : (fun u : ℝ => ∑' m : ℤ,
      cFun k m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (u : ℂ)))
      = (fun u : ℝ => (gFun k u : ℂ)) :=
    funext fun u => (hasSum_term k hk u).tsum_eq
  rw [hEq] at h
  exact h

private lemma sum_Icc_inv_sq_sub {C : ℝ} (hC : 0 ≤ C) {H N : ℕ} (hH : 1 ≤ H) (hHN : H ≤ N) :
    ∑ n ∈ Finset.Icc (H + 1) N, C / (n : ℝ) ^ 2 ≤ C / (H : ℝ) - C / (N : ℝ) := by
  simpa only [Finset.Icc_add_one_left_eq_Ioc, div_eq_mul_inv, Finset.mul_sum, mul_sub] using
    mul_le_mul_of_nonneg_left (sum_Ioc_inv_sq_le_sub (α := ℝ) (Nat.ne_of_gt hH) hHN) hC

private lemma sum_Icc_inv_sq_le {C : ℝ} (hC : 0 ≤ C) {H N : ℕ} (hH : 1 ≤ H) (hHN : H ≤ N) :
    ∑ n ∈ Finset.Icc (H + 1) N, C / (n : ℝ) ^ 2 ≤ C / (H : ℝ) := by
  have h := sum_Icc_inv_sq_sub hC hH hHN
  have hCN : 0 ≤ C / (N : ℝ) := div_nonneg hC (Nat.cast_nonneg _)
  linarith

private lemma sum_Icc_int_inv_sq_eq {C : ℝ} {H N : ℕ} (_hHN : H ≤ N) :
    ∑ m ∈ Finset.Icc ((H : ℤ) + 1) (N : ℤ), C / (m : ℝ) ^ 2
      = ∑ n ∈ Finset.Icc (H + 1) N, C / (n : ℝ) ^ 2 := by
  symm
  refine Finset.sum_nbij (fun n => (n : ℤ)) ?_ ?_ ?_ ?_
  · intro n hn
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hn
    exact Finset.mem_Icc.mpr ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  · intro a _ b _ h
    simpa using h
  · intro m hm
    refine ⟨m.toNat, ?_, ?_⟩
    · have ⟨h1, h2⟩ := Finset.mem_Icc.mp hm
      have hm0 : 0 ≤ m := by omega
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · exact Int.toNat_of_nonneg (by
        have := (Finset.mem_Icc.mp hm).1
        omega)
  · intro n _
    simp

private lemma sum_Icc_neg_inv_sq_eq {C : ℝ} {H N : ℕ} :
    ∑ m ∈ Finset.Icc (-(N : ℤ)) (-(H : ℤ) - 1), C / (m : ℝ) ^ 2
      = ∑ m ∈ Finset.Icc ((H : ℤ) + 1) (N : ℤ), C / (m : ℝ) ^ 2 := by
  refine Finset.sum_nbij (fun m => -m) ?_ ?_ ?_ ?_
  · intro m hm
    rw [Finset.mem_Icc] at hm
    exact Finset.mem_Icc.mpr (by omega)
  · intro a _ b _ h
    exact neg_inj.mp h
  · intro m hm
    have ⟨h1, h2⟩ := Finset.mem_Icc.mp hm
    exact ⟨-m, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by simp⟩
  · intro m _
    push_cast
    rw [neg_sq]

private lemma sdiff_eq_union {H N : ℕ} :
    Finset.Icc (-(N : ℤ)) (N : ℤ) \ Finset.Icc (-(H : ℤ)) (H : ℤ)
      = Finset.Icc (-(N : ℤ)) (-(H : ℤ) - 1) ∪ Finset.Icc ((H : ℤ) + 1) (N : ℤ) := by
  ext m
  simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_union]
  omega

private lemma finite_tail_bound (k : ℕ) (hk : 1 ≤ k) {H N : ℕ} (hH : 1 ≤ H) (hHN : H ≤ N)
    (u : ℝ) :
    ‖(∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          cFun k m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (u : ℂ)))
      - (∑ m ∈ Finset.Icc (-(H : ℤ)) (H : ℤ),
          cFun k m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (u : ℂ)))‖
      ≤ (2 * ((k : ℝ) * ((k : ℝ) + 4))) / (H : ℝ) := by
  have hC : 0 ≤ (k : ℝ) * ((k : ℝ) + 4) := by positivity
  have hsub : Finset.Icc (-(H : ℤ)) (H : ℤ) ⊆ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
    intro m hm
    simp only [Finset.mem_Icc] at hm ⊢
    constructor <;> omega
  have hsd : (∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) \ Finset.Icc (-(H : ℤ)) (H : ℤ),
        cFun k m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (u : ℂ)))
      = (∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          cFun k m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (u : ℂ)))
        - (∑ m ∈ Finset.Icc (-(H : ℤ)) (H : ℤ),
          cFun k m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (u : ℂ))) :=
    eq_sub_iff_add_eq.mpr (Finset.sum_sdiff hsub)
  rw [← hsd]
  calc ‖∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) \ Finset.Icc (-(H : ℤ)) (H : ℤ),
          cFun k m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (u : ℂ))‖
      ≤ ∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) \ Finset.Icc (-(H : ℤ)) (H : ℤ), ‖cFun k m‖ := by
        calc ‖∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) \ Finset.Icc (-(H : ℤ)) (H : ℤ),
              cFun k m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (u : ℂ))‖
            ≤ ∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) \ Finset.Icc (-(H : ℤ)) (H : ℤ),
              ‖cFun k m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (u : ℂ))‖ :=
            norm_sum_le _ _
          _ = ∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) \ Finset.Icc (-(H : ℤ)) (H : ℤ),
              ‖cFun k m‖ := by
              apply Finset.sum_congr rfl
              intro m _
              rw [norm_mul, norm_exp_term, mul_one]
    _ ≤ ∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) \ Finset.Icc (-(H : ℤ)) (H : ℤ),
          (k : ℝ) * ((k : ℝ) + 4) / (m : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro m hm
        have hm0 : m ≠ 0 := by
          rintro rfl
          exact (Finset.mem_sdiff.mp hm).2
            (Finset.mem_Icc.mpr ⟨neg_nonpos.mpr (Nat.cast_nonneg _), Nat.cast_nonneg _⟩)
        exact coeff_bound hk hm0
    _ ≤ (2 * ((k : ℝ) * ((k : ℝ) + 4))) / (H : ℝ) := by
        rw [sdiff_eq_union]
        have hdisj : Disjoint (Finset.Icc (-(N : ℤ)) (-(H : ℤ) - 1))
            (Finset.Icc ((H : ℤ) + 1) (N : ℤ)) := by
          rw [Finset.disjoint_left]
          intro m hm1 hm2
          simp only [Finset.mem_Icc] at hm1 hm2
          omega
        rw [Finset.sum_union hdisj, sum_Icc_neg_inv_sq_eq, sum_Icc_int_inv_sq_eq hHN]
        have hpos := sum_Icc_inv_sq_le hC hH hHN
        calc (∑ n ∈ Finset.Icc (H + 1) N, (k : ℝ) * ((k : ℝ) + 4) / (n : ℝ) ^ 2)
            + (∑ n ∈ Finset.Icc (H + 1) N, (k : ℝ) * ((k : ℝ) + 4) / (n : ℝ) ^ 2)
            ≤ (k : ℝ) * ((k : ℝ) + 4) / (H : ℝ) + (k : ℝ) * ((k : ℝ) + 4) / (H : ℝ) :=
            add_le_add hpos hpos
          _ = (2 * ((k : ℝ) * ((k : ℝ) + 4))) / (H : ℝ) := by ring

private lemma tail_bound (k : ℕ) (hk : 1 ≤ k) (H : ℕ) (hH : 1 ≤ H) (u : ℝ) :
    ‖(gFun k u : ℂ) - cFun k 0
      - ∑ m ∈ (Finset.Icc (-(H : ℤ)) (H : ℤ)).erase 0,
          cFun k m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (u : ℂ))‖
      ≤ (2 * ((k : ℝ) * ((k : ℝ) + 4))) / (H : ℝ) := by
  have h0mem : (0 : ℤ) ∈ Finset.Icc (-(H : ℤ)) (H : ℤ) :=
    Finset.mem_Icc.mpr ⟨neg_nonpos.mpr (Nat.cast_nonneg _), Nat.cast_nonneg _⟩
  have hterm0 : cFun k 0 * Complex.exp (2 * Real.pi * Complex.I * ((0 : ℤ) : ℂ) * (u : ℂ))
      = cFun k 0 := by simp
  have hrewrite : (gFun k u : ℂ) - cFun k 0
      - ∑ m ∈ (Finset.Icc (-(H : ℤ)) (H : ℤ)).erase 0,
          cFun k m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (u : ℂ))
      = (gFun k u : ℂ) - ∑ m ∈ Finset.Icc (-(H : ℤ)) (H : ℤ),
          cFun k m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (u : ℂ)) := by
    rw [← Finset.add_sum_erase _ _ h0mem, hterm0]
    ring
  rw [hrewrite]
  have hlim : Tendsto (fun N : ℕ => ‖(∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          cFun k m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (u : ℂ)))
      - (∑ m ∈ Finset.Icc (-(H : ℤ)) (H : ℤ),
          cFun k m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (u : ℂ)))‖)
      atTop (𝓝 ‖(gFun k u : ℂ) - ∑ m ∈ Finset.Icc (-(H : ℤ)) (H : ℤ),
          cFun k m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (u : ℂ))‖) := by
    have h1 : Tendsto (fun N : ℕ => (∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
            cFun k m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (u : ℂ)))
        - (∑ m ∈ Finset.Icc (-(H : ℤ)) (H : ℤ),
            cFun k m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (u : ℂ))))
        atTop (𝓝 ((gFun k u : ℂ) - ∑ m ∈ Finset.Icc (-(H : ℤ)) (H : ℤ),
            cFun k m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (u : ℂ)))) :=
      ((uniform k hk).tendsto_at u).sub tendsto_const_nhds
    exact h1.norm
  have hlim2 : Tendsto (fun N : ℕ => ‖(∑ m ∈ Finset.Icc (-((N + H : ℕ) : ℤ)) ((N + H : ℕ) : ℤ),
          cFun k m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (u : ℂ)))
      - (∑ m ∈ Finset.Icc (-(H : ℤ)) (H : ℤ),
          cFun k m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (u : ℂ)))‖)
      atTop (𝓝 ‖(gFun k u : ℂ) - ∑ m ∈ Finset.Icc (-(H : ℤ)) (H : ℤ),
          cFun k m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (u : ℂ))‖) :=
    hlim.comp (tendsto_add_atTop_nat H)
  apply le_of_tendsto_of_tendsto' hlim2 tendsto_const_nhds
  intro N
  exact finite_tail_bound k hk hH (by omega) u

end dist_round_pow_fourier_expansion

/-- **Fourier expansion of a power of the distance to the nearest integer.** Let $k$ be a
positive integer, let $g(u) = |u - \operatorname{round}(u)|^k$ be the $k$-th power of the
distance from a real $u$ to the nearest integer, let $e(x) = e^{2\pi i x}$, and for every
integer $m$ let $c(m) = \int_0^1 g(u)\, e(-mu)\, du$. Then $c(0) = 1/(2^k (k + 1))$, the mean of
$g$ over a period; there is a real constant $C$ with $|c(m)| \le C / m^2$ for every integer
$m \ne 0$; the series $\sum_{m \in \mathbb{Z}} |c(m)|$ converges; the symmetric partial sums
$\sum_{|m| \le H} c(m)\, e(mu)$ converge to $g(u)$ uniformly in real $u$ as $H \to \infty$; and
there is a real constant $C'$ such that for every integer $H \ge 1$ and every real $u$,
$$\Bigl|g(u) - c(0) - \sum_{0 < |m| \le H} c(m)\, e(mu)\Bigr| \le \frac{C'}{H}.$$

Source: Anji Dong, Katerina Saettone, Kendra Song and Alexandru Zaharescu, *An Equidistribution
Result for Differences Associated with Square Pyramidal Numbers*, Journal of Integer Sequences 29
(2026), Article 26.5.5, Lemma 10 (`jis-2026-26.5.5-lem-10`). -/
theorem dist_round_pow_fourier_expansion (k : ℕ) (hk : 1 ≤ k) :
    let g : ℝ → ℝ := fun u => |u - round u| ^ k
    let c : ℤ → ℂ := fun m => ∫ u in (0 : ℝ)..1,
      (g u : ℂ) * Complex.exp (-(2 * Real.pi * Complex.I * (m : ℂ) * (u : ℂ)))
    c 0 = ((1 / (2 ^ k * ((k : ℝ) + 1)) : ℝ) : ℂ) ∧
      (∃ C : ℝ, ∀ m : ℤ, m ≠ 0 → ‖c m‖ ≤ C / (m : ℝ) ^ 2) ∧
      Summable (fun m : ℤ => ‖c m‖) ∧
      TendstoUniformly (fun (H : ℕ) (u : ℝ) => ∑ m ∈ Finset.Icc (-(H : ℤ)) H,
          c m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (u : ℂ)))
        (fun u => (g u : ℂ)) atTop ∧
      ∃ C : ℝ, ∀ H : ℕ, 1 ≤ H → ∀ u : ℝ,
        ‖(g u : ℂ) - c 0 - ∑ m ∈ (Finset.Icc (-(H : ℤ)) H).erase 0,
            c m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (u : ℂ))‖ ≤ C / H := by
  refine ⟨dist_round_pow_fourier_expansion.cFun_zero k hk,
    ⟨(k : ℝ) * ((k : ℝ) + 4), fun m hm => dist_round_pow_fourier_expansion.coeff_bound hk hm⟩,
    dist_round_pow_fourier_expansion.summable_norm_cFun k hk,
    dist_round_pow_fourier_expansion.uniform k hk,
    ⟨2 * ((k : ℝ) * ((k : ℝ) + 4)),
      fun H hH u => dist_round_pow_fourier_expansion.tail_bound k hk H hH u⟩⟩

end

end MetaMathlibExt
