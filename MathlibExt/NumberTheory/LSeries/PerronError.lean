/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Complex.VerticalIntegral.Basic
public import MathlibExt.Analysis.PerronKernel
public import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.Harmonic.Bounds
import MathlibExt.Analysis.Complex.VerticalIntegral.CauchyKernel
import MathlibExt.Analysis.Complex.VerticalIntegral.PerronKernel
import MathlibExt.NumberTheory.LSeries.VerticalLine

/-!
# Truncated Perron formula with explicit error

For `x > 0`, `c > 0` and `T > 0`, the truncated Perron integral
`(1 / 2πi) ∫_{c - iT}^{c + iT} x ^ s / s ds` approximates the step function `perronStep x`
(`0` for `x < 1`, `1 / 2` at `x = 1`, `1` for `x > 1`) within
`x ^ c * min 1 (1 / (T |log x|))`. Summing this against the coefficients of a Dirichlet
series gives the truncated Perron formula for `∑_{n ≤ x} a n`, with an error controlled by
the sum `∑ ‖a n‖ (x / n) ^ c min 1 (1 / (T |log (x / n)|))`; when `‖a n‖ ≤ A n ^ ε` this
error sum is `O(A (x ^ (c + ε) / ((c - 1 - ε) T) + x ^ ε log x / T))`.

## Main definitions

* `PerronKernel.perronStep`: the step function at `1`, with value `1 / 2` at the jump.

## Main statements

* `PerronKernel.norm_truncated_sub_perronStep_lt`: the truncated Perron kernel is within
  `x ^ c * min 1 (1 / (T |log x|))` of `perronStep x`, for `x ≠ 1`.
* `Complex.hasVerticalIntegral_cpow_div_sub_one_pow_succ`:
  `(1 / 2πi) ∫_(c) x ^ s / (s - 1) ^ (k + 1) ds = x (log x) ^ k / k!` for `x > 1`, `c > 1`.
* `Real.abs_sub_div_le_abs_log_div`, `sum_range_add_one_rpow_neg_le`,
  `sum_range_one_div_one_add_abs_sub_le`: elementary estimates used for the error sum.
* `LSeries.tsum_perron_error_le`: the bound for the Perron error sum.
* `LSeries.norm_sum_sub_truncated_perron_le`: the truncated Perron formula
  `∑_{n ≤ x} a n = (1 / 2πi) ∫_{c - iT}^{c + iT} L(a, s) x ^ s / s ds
    + O(x ^ (c + ε) / T + x ^ ε log x / T)` for coefficients `a n = O(n ^ δ)` for all `δ > 0`.
-/

@[expose] public section

open Complex Filter MeasureTheory
open scoped Real Topology

namespace PerronKernel

/-- The step function at `1` that truncated Perron integrals approximate:
`perronStep x = 0` for `x < 1`, `perronStep 1 = 1 / 2` and `perronStep x = 1` for `x > 1`. -/
noncomputable def perronStep (x : ℝ) : ℝ :=
  if x < 1 then 0 else if x = 1 then 1 / 2 else 1

/-- `perronStep x = 0` for `x < 1`. -/
theorem perronStep_of_lt_one {x : ℝ} (hx : x < 1) : perronStep x = 0 := by
  simp [perronStep, hx]

/-- `perronStep 1 = 1 / 2`. -/
theorem perronStep_one : perronStep 1 = 1 / 2 := by
  simp [perronStep]

/-- `perronStep x = 1` for `x > 1`. -/
theorem perronStep_of_one_lt {x : ℝ} (hx : 1 < x) : perronStep x = 1 := by
  simp [perronStep, not_lt.mpr hx.le, hx.ne']

/-- **The truncated Perron kernel near the jump.** For `x > 0`, `x ≠ 1`, `c > 0`, `T > 0`
and `T |log x| ≤ 1`,
`‖(1 / 2π) ∫_{-T}^{T} x ^ (c + it) / (c + it) dt - perronStep x‖ < x ^ c`. -/
theorem norm_truncated_sub_perronStep_lt_rpow {x c R : ℝ} (hx : 0 < x)
    (hx1 : x ≠ 1) (hc : 0 < c) (hR : 0 < R) (hnear : R * |Real.log x| ≤ 1) :
    ‖((1 / (2 * π)) • ∫ t in (-R)..R,
          (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / ((c : ℂ) + (t : ℂ) * I)) -
        ((perronStep x : ℝ) : ℂ)‖ < x ^ c := by
  have hpi : (0:ℝ) < π := Real.pi_pos
  have hpi3 : (3:ℝ) < π := Real.pi_gt_three
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ, P = x ^ c := ⟨_, rfl⟩
  have hP : (0:ℝ) < P := by rw [hPdef]; exact Real.rpow_pos_of_pos hx c
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Real.log x := ⟨_, rfl⟩
  have hnear' : R * |L| ≤ 1 := by rw [hLdef]; exact hnear
  have hD : ∀ t : ℝ, (0:ℝ) < c ^ 2 + t ^ 2 := fun t => by positivity
  have hzne : ∀ t : ℝ, ((c : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro t hz
    exact hc.ne' (by simpa using congrArg Complex.re hz)
  -- the real and imaginary parts of the integrand
  have alg : ∀ (Q A₀ B₀ p q : ℝ), p ≠ 0 →
      (Q : ℂ) * ((A₀ : ℂ) + (B₀ : ℂ) * I) / ((p : ℂ) + (q : ℂ) * I)
        = ((Q * (p * A₀ + q * B₀) / (p ^ 2 + q ^ 2) : ℝ) : ℂ)
          + ((Q * (p * B₀ - q * A₀) / (p ^ 2 + q ^ 2) : ℝ) : ℂ) * I := by
    intro Q A₀ B₀ p q hp
    have hpq : p ^ 2 + q ^ 2 ≠ 0 := by positivity
    have hz : (p : ℂ) + (q : ℂ) * I ≠ 0 := Complex.ofReal_add_mul_I_ne_zero (Or.inl hp)
    have hpqC : (p : ℂ) ^ 2 + (q : ℂ) ^ 2 ≠ 0 := by exact_mod_cast hpq
    rw [div_eq_iff hz]
    push_cast
    field_simp
    ring_nf
    simp only [I_sq]
    ring
  obtain ⟨u, hudef⟩ : ∃ u : ℝ → ℝ, u = fun t =>
      P * (c * Real.cos (L * t) + t * Real.sin (L * t)) / (c ^ 2 + t ^ 2) := ⟨_, rfl⟩
  obtain ⟨v, hvdef⟩ : ∃ v : ℝ → ℝ, v = fun t =>
      P * (c * Real.sin (L * t) - t * Real.cos (L * t)) / (c ^ 2 + t ^ 2) := ⟨_, rfl⟩
  have huval : ∀ t : ℝ,
      u t = P * (c * Real.cos (L * t) + t * Real.sin (L * t)) / (c ^ 2 + t ^ 2) := by
    intro t; rw [hudef]
  have hvval : ∀ t : ℝ,
      v t = P * (c * Real.sin (L * t) - t * Real.cos (L * t)) / (c ^ 2 + t ^ 2) := by
    intro t; rw [hvdef]
  have hcu : Continuous u := by
    rw [hudef]; exact Continuous.div (by fun_prop) (by fun_prop) fun t => (hD t).ne'
  have hcv : Continuous v := by
    rw [hvdef]; exact Continuous.div (by fun_prop) (by fun_prop) fun t => (hD t).ne'
  have hxs : ∀ t : ℝ, (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)
      = (P : ℂ) * ((Real.cos (L * t) : ℂ) + (Real.sin (L * t) : ℂ) * I) := by
    intro t
    have hPe : P = Real.exp (L * c) := by rw [hPdef, hLdef, Real.rpow_def_of_pos hx]
    have hxc : ((P : ℝ) : ℂ) = Complex.exp (((L * c : ℝ) : ℂ)) := by
      rw [← Complex.ofReal_exp, hPe]
    have h1 : ((Real.log x : ℝ) : ℂ) * ((c : ℂ) + (t : ℂ) * I)
        = ((L * c : ℝ) : ℂ) + ((L * t : ℝ) : ℂ) * I := by
      rw [← hLdef]; push_cast; ring
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne' : (x:ℂ) ≠ 0),
      ← Complex.ofReal_log hx.le, h1, Complex.exp_add, Complex.exp_mul_I, ← hxc,
      Complex.ofReal_cos, Complex.ofReal_sin]
  have hkey : ∀ t : ℝ, (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / ((c : ℂ) + (t : ℂ) * I)
      = ((u t : ℝ) : ℂ) + ((v t : ℝ) : ℂ) * I := by
    intro t
    rw [hxs t, huval t, hvval t]
    exact alg P (Real.cos (L * t)) (Real.sin (L * t)) c t hc.ne'
  -- folding the symmetric interval
  have hfold : ∀ f : ℝ → ℝ, Continuous f →
      (∫ t in (-R)..R, f t) = (∫ t in (0:ℝ)..R, f (-t)) + ∫ t in (0:ℝ)..R, f t := by
    intro f hf
    have h1 : (∫ t in (-R)..(0:ℝ), f t) + ∫ t in (0:ℝ)..R, f t = ∫ t in (-R)..R, f t :=
      intervalIntegral.integral_add_adjacent_intervals
        (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)
    rw [← h1]
    congr 1
    simp
  have hueven : ∀ t : ℝ, u (-t) = u t := by
    intro t
    rw [huval, huval, show L * -t = -(L * t) by ring, Real.cos_neg, Real.sin_neg]
    ring
  have hvodd : ∀ t : ℝ, v (-t) = -v t := by
    intro t
    rw [hvval, hvval, show L * -t = -(L * t) by ring, Real.cos_neg, Real.sin_neg]
    ring
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = ∫ t in (0:ℝ)..R, u t := ⟨_, rfl⟩
  have hUint : (∫ t in (-R)..R, u t) = 2 * A := by
    rw [hfold u hcu]
    simp only [hueven]
    rw [hAdef]; ring
  have hVint : (∫ t in (-R)..R, v t) = 0 := by
    rw [hfold v hcv]
    simp only [hvodd]
    rw [intervalIntegral.integral_neg]
    ring
  -- the integral is real, and equals `A / π`
  have hI : ((1 / (2 * π)) • ∫ t in (-R)..R,
        (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / ((c : ℂ) + (t : ℂ) * I))
      = ((A / π : ℝ) : ℂ) := by
    have hiu : IntervalIntegrable (fun t : ℝ => ((u t : ℝ) : ℂ)) MeasureTheory.volume (-R) R :=
      (Complex.continuous_ofReal.comp hcu).intervalIntegrable _ _
    have hiv : IntervalIntegrable (fun t : ℝ => ((v t : ℝ) : ℂ) * I)
        MeasureTheory.volume (-R) R :=
      ((Complex.continuous_ofReal.comp hcv).mul continuous_const).intervalIntegrable _ _
    have h0 : (∫ t in (-R)..R,
        (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / ((c : ℂ) + (t : ℂ) * I))
        = ((2 * A : ℝ) : ℂ) := by
      simp only [hkey]
      rw [intervalIntegral.integral_add hiu hiv, intervalIntegral.integral_mul_const,
        intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal, hUint, hVint]
      push_cast
      ring
    rw [h0, Complex.real_smul]
    push_cast
    field_simp
  rw [hI, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, ← hPdef]
  -- the arctangent integral
  have harctan : (∫ t in (0:ℝ)..R, c / (c ^ 2 + t ^ 2)) = Real.arctan (R / c) := by
    rw [integral_div_sq_add_sq]
    simp
  -- the majorant
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ → ℝ, M = fun t => P * (c / (c ^ 2 + t ^ 2) + |L|) := ⟨_, rfl⟩
  have hMval : ∀ t : ℝ, M t = P * (c / (c ^ 2 + t ^ 2) + |L|) := by intro t; rw [hMdef]
  have hcM : Continuous M := by
    rw [hMdef]
    exact continuous_const.mul
      ((continuous_const.div (by fun_prop) fun t => (hD t).ne').add continuous_const)
  have hbound : ∀ t : ℝ, |u t| ≤ M t := by
    intro t
    have hDt := hD t
    have h1 : |Real.cos (L * t)| ≤ 1 := Real.abs_cos_le_one _
    have h2 : |Real.sin (L * t)| ≤ |L| * |t| := by
      have := Real.abs_sin_le_abs (x := L * t)
      rwa [abs_mul] at this
    have e1 : |c * Real.cos (L * t)| ≤ c := by
      rw [abs_mul, abs_of_pos hc]
      calc c * |Real.cos (L * t)| ≤ c * 1 := by
            exact mul_le_mul_of_nonneg_left h1 hc.le
        _ = c := mul_one c
    have e2 : |t * Real.sin (L * t)| ≤ |L| * t ^ 2 := by
      rw [abs_mul]
      calc |t| * |Real.sin (L * t)| ≤ |t| * (|L| * |t|) :=
            mul_le_mul_of_nonneg_left h2 (abs_nonneg t)
        _ = |L| * t ^ 2 := by
            rw [show |t| * (|L| * |t|) = |L| * (|t| * |t|) by ring, abs_mul_abs_self, sq]
    have h3 : |c * Real.cos (L * t) + t * Real.sin (L * t)| ≤ c + |L| * t ^ 2 :=
      le_trans (abs_add_le _ _) (add_le_add e1 e2)
    rw [huval, hMval, abs_div, abs_of_pos hDt, abs_mul, abs_of_pos hP, div_le_iff₀ hDt]
    have h4 : P * |c * Real.cos (L * t) + t * Real.sin (L * t)| ≤ P * (c + |L| * t ^ 2) :=
      mul_le_mul_of_nonneg_left h3 hP.le
    have h5 : P * (c / (c ^ 2 + t ^ 2) + |L|) * (c ^ 2 + t ^ 2)
        = P * (c + |L| * (c ^ 2 + t ^ 2)) := by field_simp
    have h6 : |L| * t ^ 2 ≤ |L| * (c ^ 2 + t ^ 2) := by
      have : t ^ 2 ≤ c ^ 2 + t ^ 2 := by nlinarith [sq_nonneg c]
      exact mul_le_mul_of_nonneg_left this (abs_nonneg L)
    have h7 : P * (c + |L| * t ^ 2) ≤ P * (c + |L| * (c ^ 2 + t ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ hP.le
      linarith
    rw [h5]
    linarith
  have hi1 : IntervalIntegrable (fun t : ℝ => c / (c ^ 2 + t ^ 2)) MeasureTheory.volume 0 R :=
    (continuous_const.div (by fun_prop) fun t => (hD t).ne').intervalIntegrable _ _
  have hMint : (∫ t in (0:ℝ)..R, M t) = P * (Real.arctan (R / c) + |L| * R) := by
    simp only [hMval]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add hi1 intervalIntegrable_const, harctan,
      intervalIntegral.integral_const]
    simp only [smul_eq_mul, sub_zero]
    ring
  have hAub : A ≤ P * (Real.arctan (R / c) + |L| * R) := by
    rw [hAdef, ← hMint]
    refine intervalIntegral.integral_mono_on hR.le (hcu.intervalIntegrable _ _)
      (hcM.intervalIntegrable _ _) ?_
    intro t _
    exact le_trans (le_abs_self _) (hbound t)
  have hAlb : -(P * (Real.arctan (R / c) + |L| * R)) ≤ A := by
    rw [hAdef, ← hMint, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_mono_on hR.le ((hcM.neg).intervalIntegrable _ _)
      (hcu.intervalIntegrable _ _) ?_
    intro t _
    exact (abs_le.mp (hbound t)).1
  have hstep : P * (Real.arctan (R / c) + |L| * R) < P * π := by
    refine mul_lt_mul_of_pos_left ?_ hP
    have h1 := Real.arctan_lt_pi_div_two (R / c)
    have h2 : |L| * R ≤ 1 := by rw [mul_comm]; exact hnear'
    linarith
  have hAlt : A < P * π := lt_of_le_of_lt hAub hstep
  have hAgt : -(P * π) < A := by linarith
  have hdiv1 : A / π < P := by rw [div_lt_iff₀ hpi]; linarith
  have hdiv2 : -P < A / π := by rw [lt_div_iff₀ hpi]; linarith
  rcases lt_or_gt_of_ne hx1 with hlt | hgt
  · have hδ : perronStep x = 0 := by simp [perronStep, hlt]
    rw [hδ, sub_zero, abs_lt]
    exact ⟨hdiv2, hdiv1⟩
  · have hδ : perronStep x = 1 := by simp [perronStep, not_lt.mpr hgt.le, hgt.ne']
    have hP1 : 1 < P := by
      rw [hPdef]
      exact Real.one_lt_rpow_iff_of_pos hx |>.mpr (Or.inl ⟨hgt, hc⟩)
    have hL0 : 0 < L := by rw [hLdef]; exact Real.log_pos hgt
    have hLR : L * R ≤ 1 := by
      rw [abs_of_pos hL0] at hnear'
      linarith [hnear']
    have hAnn : 0 ≤ A := by
      rw [hAdef]
      refine intervalIntegral.integral_nonneg hR.le ?_
      intro t ht
      have ht0 : 0 ≤ t := ht.1
      have htR : t ≤ R := ht.2
      have hLt : L * t ≤ 1 := by nlinarith
      have hLt0 : 0 ≤ L * t := mul_nonneg hL0.le ht0
      have hcos : 0 ≤ Real.cos (L * t) :=
        Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
      have hsin : 0 ≤ Real.sin (L * t) :=
        Real.sin_nonneg_of_nonneg_of_le_pi hLt0 (by linarith)
      rw [huval]
      have hnum : 0 ≤ c * Real.cos (L * t) + t * Real.sin (L * t) :=
        add_nonneg (mul_nonneg hc.le hcos) (mul_nonneg ht0 hsin)
      exact div_nonneg (mul_nonneg hP.le hnum) (hD t).le
    have hApi : 0 ≤ A / π := div_nonneg hAnn hpi.le
    rw [hδ, abs_lt]
    constructor <;> linarith

/-- **The truncated Perron kernel away from the jump.** For `x > 0`, `x ≠ 1`, `c > 0` and
`T > 0`,
`‖(1 / 2π) ∫_{-T}^{T} x ^ (c + it) / (c + it) dt - perronStep x‖ < x ^ c / (T |log x|)`. -/
theorem norm_truncated_sub_perronStep_lt_rpow_div {x c R : ℝ} (hx : 0 < x)
    (hx1 : x ≠ 1) (hc : 0 < c) (hR : 0 < R) :
    ‖((1 / (2 * π)) • ∫ t in (-R)..R,
          (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / ((c : ℂ) + (t : ℂ) * I)) -
        ((perronStep x : ℝ) : ℂ)‖ < x ^ c / (R * |Real.log x|) := by
  have hL0 : Real.log x ≠ 0 := by
    rcases lt_or_gt_of_ne hx1 with h | h
    · exact (Real.log_neg hx h).ne
    · exact (Real.log_pos h).ne'
  have hstep : ((perronStep x : ℝ) : ℂ) = if 1 < x then (1 : ℂ) else 0 := by
    rcases lt_or_gt_of_ne hx1 with h | h
    · simp [perronStep_of_lt_one h, not_lt.mpr h.le]
    · simp [perronStep_of_one_lt h, h]
  have hK : (1 / (2 * π)) • ∫ t in (-R)..R,
      (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / ((c : ℂ) + (t : ℂ) * I) = perronKernel x c R := by
    simp [perronKernel, Complex.real_smul]
  rw [hK, hstep]
  refine (perron_bound hx hx1 hc hR).trans_lt ?_
  have hpos : 0 < R * |Real.log x| := mul_pos hR (abs_pos.mpr hL0)
  have hxc : 0 < x ^ c := Real.rpow_pos_of_pos hx c
  rw [← Real.rpow_def_of_pos hx, div_div, div_div,
    div_lt_div_iff_of_pos_left hxc (by positivity) hpos]
  nlinarith [Real.pi_gt_three]

/-- **The truncated Perron kernel.** For `x > 0`, `x ≠ 1`, `c > 0` and `T > 0`,
`‖(1 / 2π) ∫_{-T}^{T} x ^ (c + it) / (c + it) dt - perronStep x‖
  < x ^ c * min 1 (1 / (T |log x|))`. -/
theorem norm_truncated_sub_perronStep_lt {x c R : ℝ} (hx : 0 < x)
    (hx1 : x ≠ 1) (hc : 0 < c) (hR : 0 < R) :
    ‖((1 / (2 * π)) • ∫ t in (-R)..R,
          (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / ((c : ℂ) + (t : ℂ) * I)) -
        ((perronStep x : ℝ) : ℂ)‖ <
      x ^ c * min 1 (1 / (R * |Real.log x|)) := by
  have hL0 : Real.log x ≠ 0 := by
    rcases lt_or_gt_of_ne hx1 with h | h
    · exact (Real.log_neg hx h).ne
    · exact (Real.log_pos h).ne'
  have hpos : 0 < R * |Real.log x| := mul_pos hR (abs_pos.mpr hL0)
  rcases le_total (R * |Real.log x|) 1 with hnear | hfar
  · have hmin : min 1 (1 / (R * |Real.log x|)) = 1 := by
      refine min_eq_left ?_
      rw [le_div_iff₀ hpos]
      linarith
    rw [hmin, mul_one]
    exact norm_truncated_sub_perronStep_lt_rpow hx hx1 hc hR hnear
  · have hmin : min 1 (1 / (R * |Real.log x|)) = 1 / (R * |Real.log x|) := by
      refine min_eq_right ?_
      rw [div_le_one hpos]
      linarith
    rw [hmin, mul_one_div]
    exact norm_truncated_sub_perronStep_lt_rpow_div hx hx1 hc hR

end PerronKernel

namespace Complex

/-- **The Perron kernel with a pole at `1`.** For `k : ℕ`, `c > 1` and `x > 1`,
`(1 / 2πi) ∫_(c) x ^ s / (s - 1) ^ (k + 1) ds = x (log x) ^ k / k!`. -/
theorem hasVerticalIntegral_cpow_div_sub_one_pow_succ {k : ℕ} {x c : ℝ} (hx : 1 < x)
    (hc : 1 < c) :
    HasVerticalIntegral c (fun s : ℂ => (x : ℂ) ^ s / (s - 1) ^ (k + 1))
      ((x : ℂ) * (Real.log x : ℂ) ^ k / (Nat.factorial k : ℂ)) := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
  have hc1 : (0 : ℝ) < c - 1 := by linarith
  -- the same kernel with its pole at the origin, on the shifted line `Re w = c - 1`
  have key : HasVerticalIntegral (c - 1) (fun w : ℂ => (x : ℂ) ^ w / w ^ (k + 1))
      ((Real.log x : ℂ) ^ k / (Nat.factorial k : ℂ)) := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simpa using hasVerticalIntegral_cpow_div_self_of_one_lt hx hc1
    · exact hasVerticalIntegral_cpow_div_pow_succ_of_one_le hk hc1 hx.le
  have h2 := (key.const_mul (x : ℂ)).comp_sub_ofReal (a := 1)
  rw [show (x : ℂ) * ((Real.log x : ℂ) ^ k / (Nat.factorial k : ℂ))
      = (x : ℂ) * (Real.log x : ℂ) ^ k / (Nat.factorial k : ℂ) by ring] at h2
  refine h2.congr_line fun t => ?_
  simp only [Complex.ofReal_one]
  rw [Complex.cpow_sub _ _ hxC, Complex.cpow_one]
  field_simp

end Complex

namespace Real

/-- **A lower bound for `|log (x / y)|` near `y = x`.** For `x > 0` and
`x / 2 < y < 3 x / 2`, `|x - y| / (2 x) ≤ |log (x / y)|`. -/
theorem abs_sub_div_le_abs_log_div {x y : ℝ} (hx : 0 < x) (hy₁ : x / 2 < y)
    (hy₂ : y < 3 * x / 2) :
    |x - y| / (2 * x) ≤ |Real.log (x / y)| := by
  have hy0 : 0 < y := by linarith
  -- `log (y / x) = - log (x / y)`
  have hinv : Real.log (y / x) = -Real.log (x / y) := by
    rw [← inv_div x y, Real.log_inv]
  -- ## The two one-sided estimates, with the divisions cleared
  have key1 : x - y ≤ Real.log (x / y) * x := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < y / x by positivity)
    rw [hinv] at h
    have h' : (x - y) / x ≤ Real.log (x / y) := by
      rw [div_le_iff₀ hx]
      have : y / x * x = y := by field_simp
      nlinarith [this]
    rwa [div_le_iff₀ hx] at h'
  have key2 : Real.log (x / y) * y ≤ x - y := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < x / y by positivity)
    have hxy : x / y * y = x := by field_simp
    nlinarith [h, hxy]
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * x)]
  rcases le_or_gt y x with h | h
  · have hL : 0 ≤ Real.log (x / y) := by nlinarith
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ x - y), abs_of_nonneg hL]
    nlinarith
  · have hL : Real.log (x / y) ≤ 0 := by nlinarith
    rw [abs_of_nonpos (by linarith : x - y ≤ 0), abs_of_nonpos hL]
    nlinarith

end Real

/-- **Partial sums of the `p`-series.** For real `s > 1` and every `N`,
`∑_{n < N} (n + 1) ^ (-s) ≤ 1 + 1 / (s - 1)`. -/
theorem sum_range_add_one_rpow_neg_le {s : ℝ} (hs : 1 < s) (N : ℕ) :
    ∑ n ∈ Finset.range N, ((n : ℝ) + 1) ^ (-s) ≤ 1 + 1 / (s - 1) := by
  have hs1 : (0 : ℝ) < s - 1 := by linarith
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp only [Finset.range_zero, Finset.sum_empty]
    positivity
  -- ## Peel off the `n = 0` term, which is `1`
  have hsplit : ∑ n ∈ Finset.range N, ((n : ℝ) + 1) ^ (-s)
      = 1 + ∑ n ∈ Finset.Ico 1 N, ((n : ℝ) + 1) ^ (-s) := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hN]
    norm_num
  rw [hsplit]
  gcongr
  -- ## The tail is at most `∫_1^N x ^ (-s)`, by antitonicity
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-s)) (Set.Icc (1 : ℕ) (N : ℕ)) := by
    intro x hx y _ hxy
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one (by exact_mod_cast hx.1)
    exact Real.rpow_le_rpow_of_nonpos hx0 hxy (by linarith)
  have hsum := AntitoneOn.sum_le_integral_Ico (f := fun x : ℝ => x ^ (-s)) hN hanti
  simp only [Nat.cast_one, Nat.cast_add] at hsum
  refine le_trans (le_of_eq ?_) (hsum.trans ?_)
  · exact Finset.sum_congr rfl fun i _ => by ring_nf
  -- ## Evaluate the integral
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hmem : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) (N : ℝ) := by
    rw [Set.uIcc_of_le hN1]; simp only [Set.mem_Icc, not_and, not_le]; intro h; linarith
  rw [integral_rpow (Or.inr ⟨by linarith, hmem⟩), Real.one_rpow]
  have hpos : (0 : ℝ) ≤ (N : ℝ) ^ (-s + 1) := Real.rpow_nonneg (by positivity) _
  have hne : (-s + 1) ≠ 0 := by intro h; linarith
  have heq : ((N : ℝ) ^ (-s + 1) - 1) / (-s + 1) = (1 - (N : ℝ) ^ (-s + 1)) / (s - 1) := by
    field_simp
    ring
  rw [heq]
  gcongr
  linarith

/-- **A harmonic sum centred at an integer.** For natural numbers `M` and `P`,
`∑_{n < P} 1 / (1 + |(n + 1) - M|) ≤ 2 + 2 log P`. -/
theorem sum_range_one_div_one_add_abs_sub_le (M P : ℕ) :
    ∑ n ∈ Finset.range P, 1 / (1 + |((n : ℝ) + 1) - (M : ℝ)|) ≤ 2 + 2 * Real.log P := by
  -- ## The harmonic bound `∑_{j < N} 1 / (j + 1) ≤ 1 + log N`, in `ℝ`
  have hharm : ∀ N : ℕ, ∑ j ∈ Finset.range N, (1 : ℝ) / ((j : ℝ) + 1) ≤ 1 + Real.log N := by
    intro N
    have h := harmonic_le_one_add_log N
    simp only [harmonic] at h
    push_cast at h
    simpa [one_div] using h
  have hnonneg : ∀ i : ℕ, (0 : ℝ) ≤ (1 : ℝ) / ((i : ℝ) + 1) := by
    intro i
    positivity
  -- ## Split `range P` at the point `M`
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = M - 1 := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ, Q = min K P := ⟨_, rfl⟩
  have hQP : Q ≤ P := by omega
  have hsplit : ∑ n ∈ Finset.range P, 1 / (1 + |((n : ℝ) + 1) - (M : ℝ)|)
      = (∑ n ∈ Finset.range Q, 1 / (1 + |((n : ℝ) + 1) - (M : ℝ)|))
        + ∑ n ∈ Finset.Ico Q P, 1 / (1 + |((n : ℝ) + 1) - (M : ℝ)|) := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico]
    exact (Finset.sum_Ico_consecutive _ (Nat.zero_le Q) hQP).symm
  -- ## The lower half, reflected: the `j`-th term from the top is at distance `≥ j`
  have hlow : ∑ n ∈ Finset.range Q, 1 / (1 + |((n : ℝ) + 1) - (M : ℝ)|)
      ≤ ∑ j ∈ Finset.range P, (1 : ℝ) / ((j : ℝ) + 1) := by
    have hrefl : ∑ n ∈ Finset.range Q, 1 / (1 + |((n : ℝ) + 1) - (M : ℝ)|)
        = ∑ j ∈ Finset.range Q, 1 / (1 + |(((Q - 1 - j : ℕ) : ℝ) + 1) - (M : ℝ)|) :=
      (Finset.sum_range_reflect (fun n => 1 / (1 + |((n : ℝ) + 1) - (M : ℝ)|)) Q).symm
    rw [hrefl]
    refine le_trans (Finset.sum_le_sum ?_)
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hQP)
        (fun i _ _ => hnonneg i))
    intro j hj
    rw [Finset.mem_range] at hj
    have h1 : (Q - 1 - j) + j + 1 ≤ Q := by omega
    have h2 : Q + 1 ≤ M := by omega
    have h1' : ((Q - 1 - j : ℕ) : ℝ) + (j : ℝ) + 1 ≤ (Q : ℝ) := by exact_mod_cast h1
    have h2' : (Q : ℝ) + 1 ≤ (M : ℝ) := by exact_mod_cast h2
    refine one_div_le_one_div_of_le (by positivity) ?_
    have hna := neg_abs_le (((Q - 1 - j : ℕ) : ℝ) + 1 - (M : ℝ))
    have : ((Q - 1 - j : ℕ) : ℝ) + 1 - (M : ℝ) = (((Q - 1 - j : ℕ) : ℝ) + 1) - (M : ℝ) := by ring
    rw [this] at hna
    linarith
  -- ## The upper half: the `j`-th term above `M` is at distance `≥ j`
  have hup : ∑ n ∈ Finset.Ico Q P, 1 / (1 + |((n : ℝ) + 1) - (M : ℝ)|)
      ≤ ∑ j ∈ Finset.range P, (1 : ℝ) / ((j : ℝ) + 1) := by
    have hre : ∑ n ∈ Finset.Ico Q P, 1 / (1 + |((n : ℝ) + 1) - (M : ℝ)|)
        = ∑ j ∈ Finset.range (P - Q), 1 / (1 + |(((Q + j : ℕ) : ℝ) + 1) - (M : ℝ)|) :=
      Finset.sum_Ico_eq_sum_range (f := fun n => 1 / (1 + |((n : ℝ) + 1) - (M : ℝ)|)) ..
    rw [hre]
    refine le_trans (Finset.sum_le_sum ?_)
      (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_subset_range.mpr (show P - Q ≤ P by omega)) (fun i _ _ => hnonneg i))
    intro j hj
    rw [Finset.mem_range] at hj
    have h2 : M ≤ Q + 1 := by omega
    have h2' : (M : ℝ) ≤ (Q : ℝ) + 1 := by exact_mod_cast h2
    have hcast : ((Q + j : ℕ) : ℝ) = (Q : ℝ) + (j : ℝ) := by push_cast; ring
    refine one_div_le_one_div_of_le (by positivity) ?_
    have hla := le_abs_self ((((Q + j : ℕ) : ℝ) + 1) - (M : ℝ))
    rw [hcast] at hla ⊢
    linarith
  -- ## Conclude
  have hH := hharm P
  rw [hsplit]
  linarith

namespace LSeries

/-- **The Perron error sum.** There is an absolute constant `C` such that for every `ε > 0`,
every `c` with `1 + ε < c ≤ 2`, every sequence `a` with `‖a n‖ ≤ A n ^ ε` for `n ≥ 1`, every
`x ≥ 1` and every `T` with `1 ≤ T ≤ x`,
`∑_{n ≥ 1} ‖a n‖ (x / n) ^ c min 1 (1 / (T |log (x / n)|))
  ≤ C A (x ^ (c + ε) / ((c - 1 - ε) T) + x ^ ε log x / T)`. -/
theorem tsum_perron_error_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (c ε : ℝ), 0 < ε → 1 + ε < c → c ≤ 2 →
      ∀ (a : ℕ → ℂ) (A x T : ℝ), 0 < A →
        (∀ n : ℕ, 1 ≤ n → ‖a n‖ ≤ A * (n : ℝ) ^ ε) → 1 ≤ x →
          1 ≤ T → T ≤ x →
            ∑' n : ℕ, ‖a (n + 1)‖ * (x / ((n : ℝ) + 1)) ^ c *
                min 1 (1 / (T * |Real.log (x / ((n : ℝ) + 1))|)) ≤
              C * A * (x ^ (c + ε) / ((c - 1 - ε) * T) + x ^ ε * Real.log x / T) := by
  classical
  refine ⟨1000, by norm_num, ?_⟩
  intro c ε hε hcε hc2 a A x T hA ha hx hT1 hTx
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le zero_lt_one hT1
  have hc1 : (1 : ℝ) < c := by linarith
  have hD : (0 : ℝ) < c - 1 - ε := by linarith
  have hD1 : c - 1 - ε ≤ 1 := by linarith
  have hε1 : ε < 1 := by linarith
  have hlogx : (0 : ℝ) ≤ Real.log x := Real.log_nonneg hx
  have hxe : (0 : ℝ) < x ^ ε := Real.rpow_pos_of_pos hx0 ε
  -- ## The coefficient bound, with the index shift absorbed
  have hacoef : ∀ n : ℕ, ‖a (n + 1)‖ ≤ A * ((n : ℝ) + 1) ^ ε := by
    intro n
    have h := ha (n + 1) (by omega)
    have hcast : (((n + 1 : ℕ)) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rwa [hcast] at h
  -- ## Pointwise bound on the tail range `n + 1 ≤ x / 2` or `3 * x / 2 ≤ n + 1`
  have hterm_tail : ∀ n : ℕ, ((n : ℝ) + 1 ≤ x / 2 ∨ 3 * x / 2 ≤ (n : ℝ) + 1) →
      ‖a (n + 1)‖ * (x / ((n : ℝ) + 1)) ^ c *
          min 1 (1 / (T * |Real.log (x / ((n : ℝ) + 1))|))
        ≤ 3 * A * x ^ c / T * ((n : ℝ) + 1) ^ (-(c - ε)) := by
    intro n hcase
    have hm0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    -- off the central range, `|log (x / n)| ≥ log (3 / 2) ≥ 1 / 3`
    have hlogb : (1 : ℝ) / 3 ≤ |Real.log (x / ((n : ℝ) + 1))| := by
      rcases hcase with h | h
      · have h2 : (2 : ℝ) ≤ x / ((n : ℝ) + 1) := by rw [le_div_iff₀ hm0]; linarith
        have hl2 : Real.log 2 ≤ Real.log (x / ((n : ℝ) + 1)) :=
          Real.log_le_log (by norm_num) h2
        have h3 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
        rw [abs_of_nonneg (by linarith)]
        linarith
      · have h2 : x / ((n : ℝ) + 1) ≤ 2 / 3 := by rw [div_le_iff₀ hm0]; linarith
        have hl2 : Real.log (x / ((n : ℝ) + 1)) ≤ Real.log (2 / 3) :=
          Real.log_le_log (by positivity) h2
        have h3 : Real.log (2 / 3) ≤ 2 / 3 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
        rw [abs_of_nonpos (by linarith)]
        linarith
    have hLpos : (0 : ℝ) < |Real.log (x / ((n : ℝ) + 1))| := by linarith
    have hminb : min 1 (1 / (T * |Real.log (x / ((n : ℝ) + 1))|)) ≤ 3 / T := by
      refine le_trans (min_le_right _ _) ?_
      rw [div_le_div_iff₀ (mul_pos hT0 hLpos) hT0]
      nlinarith
    have hp : (0 : ℝ) ≤ (x / ((n : ℝ) + 1)) ^ c := Real.rpow_nonneg (by positivity) c
    have hmin0 : (0 : ℝ) ≤ min 1 (1 / (T * |Real.log (x / ((n : ℝ) + 1))|)) :=
      le_min zero_le_one (by positivity)
    have h1 : ‖a (n + 1)‖ * (x / ((n : ℝ) + 1)) ^ c *
          min 1 (1 / (T * |Real.log (x / ((n : ℝ) + 1))|))
        ≤ A * ((n : ℝ) + 1) ^ ε * (x / ((n : ℝ) + 1)) ^ c * (3 / T) :=
      mul_le_mul (mul_le_mul_of_nonneg_right (hacoef n) hp) hminb hmin0 (by positivity)
    refine le_trans h1 (le_of_eq ?_)
    rw [Real.div_rpow hx0.le hm0.le, show -(c - ε) = ε - c by ring, Real.rpow_sub hm0]
    ring
  -- ## Pointwise bound on the central range `x / 2 < n + 1 < 3 * x / 2`
  have hterm_cen : ∀ n : ℕ, x / 2 < (n : ℝ) + 1 → (n : ℝ) + 1 < 3 * x / 2 →
      ‖a (n + 1)‖ * (x / ((n : ℝ) + 1)) ^ c *
          min 1 (1 / (T * |Real.log (x / ((n : ℝ) + 1))|))
        ≤ 64 * A * (x * x ^ ε) / T * (1 / (1 + |(n : ℝ) + 1 - (⌊x⌋₊ : ℝ)|)) := by
    intro n hm1 hm2
    have hm0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    -- the `min` factor, through `|log (x / n)| ≥ |x - n| / (2 * x)`
    have hminb : min 1 (1 / (T * |Real.log (x / ((n : ℝ) + 1))|))
        ≤ 4 * x / (T * (1 + |x - ((n : ℝ) + 1)|)) := by
      rcases le_or_gt |x - ((n : ℝ) + 1)| 1 with h1 | h1
      · refine le_trans (min_le_left _ _) ?_
        rw [le_div_iff₀ (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_left h1 hT0.le]
      · refine le_trans (min_le_right _ _) ?_
        have hlogge : |x - ((n : ℝ) + 1)| / (2 * x) ≤ |Real.log (x / ((n : ℝ) + 1))| :=
          Real.abs_sub_div_le_abs_log_div hx0 hm1 hm2
        have hLpos : (0 : ℝ) < |Real.log (x / ((n : ℝ) + 1))| :=
          lt_of_lt_of_le (div_pos (by linarith) (by positivity)) hlogge
        rw [div_le_div_iff₀ (mul_pos hT0 hLpos) (by positivity)]
        have hkey : 2 * T * |x - ((n : ℝ) + 1)|
            ≤ 4 * x * (T * |Real.log (x / ((n : ℝ) + 1))|) := by
          have hmul := mul_le_mul_of_nonneg_left hlogge
            (show (0 : ℝ) ≤ 4 * x * T by positivity)
          calc 2 * T * |x - ((n : ℝ) + 1)|
              = 4 * x * T * (|x - ((n : ℝ) + 1)| / (2 * x)) := by field_simp; ring
            _ ≤ 4 * x * T * |Real.log (x / ((n : ℝ) + 1))| := hmul
            _ = 4 * x * (T * |Real.log (x / ((n : ℝ) + 1))|) := by ring
        nlinarith [mul_le_mul_of_nonneg_left h1.le hT0.le]
    -- the coefficient factor: `n ≤ 2 * x` and `ε < 1`
    have hcoef2 : ‖a (n + 1)‖ ≤ A * (2 * x ^ ε) := by
      have h1 := hacoef n
      have h2 : ((n : ℝ) + 1) ^ ε ≤ 2 * x ^ ε := by
        have hle : ((n : ℝ) + 1) ≤ 2 * x := by linarith
        have h3 : ((n : ℝ) + 1) ^ ε ≤ (2 * x) ^ ε := Real.rpow_le_rpow hm0.le hle hε.le
        have h4 : (2 * x) ^ ε = 2 ^ ε * x ^ ε := Real.mul_rpow (by norm_num) hx0.le
        have h5 : (2 : ℝ) ^ ε ≤ 2 := by
          have h6 := Real.rpow_le_rpow_of_exponent_le (one_le_two (α := ℝ)) hε1.le
          rwa [Real.rpow_one] at h6
        nlinarith [hxe]
      nlinarith [hA.le]
    -- the `(x / n) ^ c` factor: `x / n ≤ 2` and `c ≤ 2`
    have hpow4 : (x / ((n : ℝ) + 1)) ^ c ≤ 4 := by
      have h2 : x / ((n : ℝ) + 1) ≤ 2 := by rw [div_le_iff₀ hm0]; linarith
      calc (x / ((n : ℝ) + 1)) ^ c ≤ (2 : ℝ) ^ c :=
            Real.rpow_le_rpow (by positivity) h2 (by linarith)
        _ ≤ (2 : ℝ) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le one_le_two hc2
        _ = 4 := by norm_num
    -- moving from `x` to `⌊x⌋₊` in the denominator
    have habsb : 1 / (1 + |x - ((n : ℝ) + 1)|) ≤ 2 / (1 + |(n : ℝ) + 1 - (⌊x⌋₊ : ℝ)|) := by
      have hMx : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le hx0.le
      have hxM : x < ((⌊x⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one x
      have htri : |(n : ℝ) + 1 - (⌊x⌋₊ : ℝ)| ≤ |x - ((n : ℝ) + 1)| + 1 := by
        have h := abs_add_le ((n : ℝ) + 1 - x) (x - (⌊x⌋₊ : ℝ))
        have he : (n : ℝ) + 1 - x + (x - (⌊x⌋₊ : ℝ)) = (n : ℝ) + 1 - (⌊x⌋₊ : ℝ) := by ring
        rw [he] at h
        have h2 : |(n : ℝ) + 1 - x| = |x - ((n : ℝ) + 1)| := abs_sub_comm _ _
        have h3 : |x - (⌊x⌋₊ : ℝ)| ≤ 1 := by
          rw [abs_of_nonneg (by linarith)]
          linarith
        linarith
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [abs_nonneg (x - ((n : ℝ) + 1))]
    -- assemble the three factors
    have hmin0 : (0 : ℝ) ≤ min 1 (1 / (T * |Real.log (x / ((n : ℝ) + 1))|)) :=
      le_min zero_le_one (by positivity)
    have hp : (0 : ℝ) ≤ (x / ((n : ℝ) + 1)) ^ c := Real.rpow_nonneg (by positivity) c
    have hstep1 : ‖a (n + 1)‖ * (x / ((n : ℝ) + 1)) ^ c *
          min 1 (1 / (T * |Real.log (x / ((n : ℝ) + 1))|))
        ≤ A * (2 * x ^ ε) * 4 * (4 * x / (T * (1 + |x - ((n : ℝ) + 1)|))) :=
      mul_le_mul (mul_le_mul hcoef2 hpow4 hp (by positivity)) hminb hmin0 (by positivity)
    refine le_trans hstep1 ?_
    have hne1 : (1 + |x - ((n : ℝ) + 1)|) ≠ 0 := by positivity
    have hneT : T ≠ 0 := ne_of_gt hT0
    have heq : A * (2 * x ^ ε) * 4 * (4 * x / (T * (1 + |x - ((n : ℝ) + 1)|)))
        = 32 * A * (x * x ^ ε) / T * (1 / (1 + |x - ((n : ℝ) + 1)|)) := by
      field_simp
      ring
    rw [heq]
    have hK : (0 : ℝ) ≤ 32 * A * (x * x ^ ε) / T := by positivity
    have h2 : 1 / (1 + |x - ((n : ℝ) + 1)|)
        ≤ 2 * (1 / (1 + |(n : ℝ) + 1 - (⌊x⌋₊ : ℝ)|)) := by
      have h3 := habsb
      rw [show (2 : ℝ) / (1 + |(n : ℝ) + 1 - (⌊x⌋₊ : ℝ)|)
          = 2 * (1 / (1 + |(n : ℝ) + 1 - (⌊x⌋₊ : ℝ)|)) by ring] at h3
      exact h3
    calc 32 * A * (x * x ^ ε) / T * (1 / (1 + |x - ((n : ℝ) + 1)|))
        ≤ 32 * A * (x * x ^ ε) / T * (2 * (1 / (1 + |(n : ℝ) + 1 - (⌊x⌋₊ : ℝ)|))) :=
          mul_le_mul_of_nonneg_left h2 hK
      _ = 64 * A * (x * x ^ ε) / T * (1 / (1 + |(n : ℝ) + 1 - (⌊x⌋₊ : ℝ)|)) := by ring
  -- ## The central block has at most `⌈3 * x / 2⌉₊ ≤ 3 * x` terms
  have hPpos : (0 : ℝ) < ((⌈3 * x / 2⌉₊ : ℕ) : ℝ) := by
    exact_mod_cast Nat.ceil_pos.mpr (by linarith)
  have hPle : ((⌈3 * x / 2⌉₊ : ℕ) : ℝ) ≤ 3 * x := by
    have h := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 3 * x / 2 by linarith)
    linarith
  have hlogP : Real.log ((⌈3 * x / 2⌉₊ : ℕ) : ℝ) ≤ 2 + Real.log x := by
    have h1 : Real.log ((⌈3 * x / 2⌉₊ : ℕ) : ℝ) ≤ Real.log (3 * x) := Real.log_le_log hPpos hPle
    have h2 : Real.log (3 * x) = Real.log 3 + Real.log x :=
      Real.log_mul (by norm_num) (ne_of_gt hx0)
    have h3 : Real.log 3 ≤ 2 := by
      have h4 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
      linarith
    linarith
  -- ## The two comparisons with the main term
  have hxc1 : (1 : ℝ) ≤ x ^ (c - 1) := by
    have h := Real.rpow_le_rpow_of_exponent_le hx (show (0 : ℝ) ≤ c - 1 by linarith)
    rwa [Real.rpow_zero] at h
  have hDlog : (c - 1 - ε) * Real.log x ≤ x ^ (c - 1) := by
    have hexp : Real.log x * (c - 1) ≤ Real.exp (Real.log x * (c - 1)) := by
      linarith [Real.add_one_le_exp (Real.log x * (c - 1))]
    rw [Real.rpow_def_of_pos hx0]
    nlinarith [hlogx, hε.le]
  have hcore : (c - 1 - ε) * (2 + 2 * Real.log ((⌈3 * x / 2⌉₊ : ℕ) : ℝ)) ≤ 8 * x ^ (c - 1) := by
    have h1 := mul_le_mul_of_nonneg_left hlogP hD.le
    nlinarith [hDlog, hxc1, hD1, hD]
  have hsplitx : x ^ (c + ε) = x ^ (c - 1) * (x * x ^ ε) := by
    rw [show c + ε = (c - 1) + (1 + ε) by ring, Real.rpow_add hx0, Real.rpow_add hx0,
      Real.rpow_one]
  have key1 : 64 * A * (x * x ^ ε) / T * (2 + 2 * Real.log ((⌈3 * x / 2⌉₊ : ℕ) : ℝ))
      ≤ 512 * A * x ^ (c + ε) / ((c - 1 - ε) * T) := by
    have hK : (0 : ℝ) ≤ 64 * A * (x * x ^ ε) / T := by positivity
    have hstep : 2 + 2 * Real.log ((⌈3 * x / 2⌉₊ : ℕ) : ℝ) ≤ 8 * x ^ (c - 1) / (c - 1 - ε) := by
      rw [le_div_iff₀ hD]
      linarith [hcore]
    have hE : 64 * A * (x * x ^ ε) / T * (8 * x ^ (c - 1) / (c - 1 - ε))
        = 512 * A * x ^ (c + ε) / ((c - 1 - ε) * T) := by
      rw [hsplitx]
      field_simp
      ring
    calc 64 * A * (x * x ^ ε) / T * (2 + 2 * Real.log ((⌈3 * x / 2⌉₊ : ℕ) : ℝ))
        ≤ 64 * A * (x * x ^ ε) / T * (8 * x ^ (c - 1) / (c - 1 - ε)) :=
          mul_le_mul_of_nonneg_left hstep hK
      _ = 512 * A * x ^ (c + ε) / ((c - 1 - ε) * T) := hE
  have key2 : 3 * A * x ^ c / T * (1 + 1 / (c - ε - 1))
      ≤ 6 * A * x ^ (c + ε) / ((c - 1 - ε) * T) := by
    have hinv : (1 : ℝ) ≤ 1 / (c - 1 - ε) := by rw [le_div_iff₀ hD]; linarith
    have h1 : (1 : ℝ) + 1 / (c - ε - 1) ≤ 2 / (c - 1 - ε) := by
      rw [show c - ε - 1 = c - 1 - ε by ring]
      have h2 : (2 : ℝ) / (c - 1 - ε) = 1 / (c - 1 - ε) + 1 / (c - 1 - ε) := by ring
      linarith
    have hxc : x ^ c ≤ x ^ (c + ε) := Real.rpow_le_rpow_of_exponent_le hx (by linarith)
    have h2 : 3 * A * x ^ c / T ≤ 3 * A * x ^ (c + ε) / T := by
      rw [div_le_div_iff₀ hT0 hT0]
      have h5 : (0 : ℝ) ≤ 3 * A * T := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hxc h5]
    have h3 : (0 : ℝ) ≤ 1 + 1 / (c - ε - 1) := by
      rw [show c - ε - 1 = c - 1 - ε by ring]
      positivity
    calc 3 * A * x ^ c / T * (1 + 1 / (c - ε - 1))
        ≤ 3 * A * x ^ (c + ε) / T * (2 / (c - 1 - ε)) :=
          mul_le_mul h2 h1 h3 (by positivity)
      _ = 6 * A * x ^ (c + ε) / ((c - 1 - ε) * T) := by
          field_simp
          ring
  -- ## Sum the pointwise bounds over the two ranges
  refine Real.tsum_le_of_sum_range_le (fun n => ?_) (fun N => ?_)
  · have hp : (0 : ℝ) ≤ (x / ((n : ℝ) + 1)) ^ c := Real.rpow_nonneg (by positivity) c
    have hmin0 : (0 : ℝ) ≤ min 1 (1 / (T * |Real.log (x / ((n : ℝ) + 1))|)) :=
      le_min zero_le_one (by positivity)
    exact mul_nonneg (mul_nonneg (norm_nonneg _) hp) hmin0
  · have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.range N)
      (fun n : ℕ => x / 2 < (n : ℝ) + 1 ∧ (n : ℝ) + 1 < 3 * x / 2)
      (fun n => ‖a (n + 1)‖ * (x / ((n : ℝ) + 1)) ^ c *
        min 1 (1 / (T * |Real.log (x / ((n : ℝ) + 1))|)))
    rw [← hsplit]
    have hcen : ∑ n ∈ (Finset.range N).filter
          (fun n : ℕ => x / 2 < (n : ℝ) + 1 ∧ (n : ℝ) + 1 < 3 * x / 2),
          ‖a (n + 1)‖ * (x / ((n : ℝ) + 1)) ^ c *
            min 1 (1 / (T * |Real.log (x / ((n : ℝ) + 1))|))
        ≤ 64 * A * (x * x ^ ε) / T * (2 + 2 * Real.log ((⌈3 * x / 2⌉₊ : ℕ) : ℝ)) := by
      have h1 : ∑ n ∈ (Finset.range N).filter
            (fun n : ℕ => x / 2 < (n : ℝ) + 1 ∧ (n : ℝ) + 1 < 3 * x / 2),
            ‖a (n + 1)‖ * (x / ((n : ℝ) + 1)) ^ c *
              min 1 (1 / (T * |Real.log (x / ((n : ℝ) + 1))|))
          ≤ ∑ n ∈ (Finset.range N).filter
              (fun n : ℕ => x / 2 < (n : ℝ) + 1 ∧ (n : ℝ) + 1 < 3 * x / 2),
              64 * A * (x * x ^ ε) / T * (1 / (1 + |(n : ℝ) + 1 - (⌊x⌋₊ : ℝ)|)) := by
        refine Finset.sum_le_sum fun n hn => ?_
        rw [Finset.mem_filter] at hn
        exact hterm_cen n hn.2.1 hn.2.2
      have h2 : ∑ n ∈ (Finset.range N).filter
              (fun n : ℕ => x / 2 < (n : ℝ) + 1 ∧ (n : ℝ) + 1 < 3 * x / 2),
              64 * A * (x * x ^ ε) / T * (1 / (1 + |(n : ℝ) + 1 - (⌊x⌋₊ : ℝ)|))
          ≤ ∑ n ∈ Finset.range ⌈3 * x / 2⌉₊,
              64 * A * (x * x ^ ε) / T * (1 / (1 + |(n : ℝ) + 1 - (⌊x⌋₊ : ℝ)|)) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => by positivity)
        intro n hn
        rw [Finset.mem_filter] at hn
        rw [Finset.mem_range, Nat.lt_ceil]
        have h3 := hn.2.2
        have h4 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      have h3 : ∑ n ∈ Finset.range ⌈3 * x / 2⌉₊,
              64 * A * (x * x ^ ε) / T * (1 / (1 + |(n : ℝ) + 1 - (⌊x⌋₊ : ℝ)|))
          = 64 * A * (x * x ^ ε) / T * ∑ n ∈ Finset.range ⌈3 * x / 2⌉₊,
              1 / (1 + |(n : ℝ) + 1 - (⌊x⌋₊ : ℝ)|) := by
        rw [Finset.mul_sum]
      have h4 := sum_range_one_div_one_add_abs_sub_le ⌊x⌋₊ ⌈3 * x / 2⌉₊
      have hK : (0 : ℝ) ≤ 64 * A * (x * x ^ ε) / T := by positivity
      refine h1.trans (h2.trans ?_)
      rw [h3]
      exact mul_le_mul_of_nonneg_left h4 hK
    have htail : ∑ n ∈ (Finset.range N).filter
          (fun n : ℕ => ¬(x / 2 < (n : ℝ) + 1 ∧ (n : ℝ) + 1 < 3 * x / 2)),
          ‖a (n + 1)‖ * (x / ((n : ℝ) + 1)) ^ c *
            min 1 (1 / (T * |Real.log (x / ((n : ℝ) + 1))|))
        ≤ 3 * A * x ^ c / T * (1 + 1 / (c - ε - 1)) := by
      have h1 : ∑ n ∈ (Finset.range N).filter
            (fun n : ℕ => ¬(x / 2 < (n : ℝ) + 1 ∧ (n : ℝ) + 1 < 3 * x / 2)),
            ‖a (n + 1)‖ * (x / ((n : ℝ) + 1)) ^ c *
              min 1 (1 / (T * |Real.log (x / ((n : ℝ) + 1))|))
          ≤ ∑ n ∈ (Finset.range N).filter
              (fun n : ℕ => ¬(x / 2 < (n : ℝ) + 1 ∧ (n : ℝ) + 1 < 3 * x / 2)),
              3 * A * x ^ c / T * ((n : ℝ) + 1) ^ (-(c - ε)) := by
        refine Finset.sum_le_sum fun n hn => ?_
        rw [Finset.mem_filter] at hn
        refine hterm_tail n ?_
        rcases not_and_or.mp hn.2 with h | h
        · exact Or.inl (not_lt.mp h)
        · exact Or.inr (not_lt.mp h)
      have h2 : ∑ n ∈ (Finset.range N).filter
              (fun n : ℕ => ¬(x / 2 < (n : ℝ) + 1 ∧ (n : ℝ) + 1 < 3 * x / 2)),
              3 * A * x ^ c / T * ((n : ℝ) + 1) ^ (-(c - ε))
          ≤ ∑ n ∈ Finset.range N, 3 * A * x ^ c / T * ((n : ℝ) + 1) ^ (-(c - ε)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun i _ _ => by positivity)
      have h3 : ∑ n ∈ Finset.range N, 3 * A * x ^ c / T * ((n : ℝ) + 1) ^ (-(c - ε))
          = 3 * A * x ^ c / T * ∑ n ∈ Finset.range N, ((n : ℝ) + 1) ^ (-(c - ε)) := by
        rw [Finset.mul_sum]
      have h4 := sum_range_add_one_rpow_neg_le (show (1 : ℝ) < c - ε by linarith) N
      have hK : (0 : ℝ) ≤ 3 * A * x ^ c / T := by positivity
      refine h1.trans (h2.trans ?_)
      rw [h3]
      exact mul_le_mul_of_nonneg_left h4 hK
    have hX : (0 : ℝ) ≤ x ^ (c + ε) / ((c - 1 - ε) * T) := by positivity
    have hY : (0 : ℝ) ≤ x ^ ε * Real.log x / T := by positivity
    have e1 : 512 * A * x ^ (c + ε) / ((c - 1 - ε) * T)
        + 6 * A * x ^ (c + ε) / ((c - 1 - ε) * T)
        = 518 * (A * (x ^ (c + ε) / ((c - 1 - ε) * T))) := by ring
    have e2 : 1000 * A * (x ^ (c + ε) / ((c - 1 - ε) * T) + x ^ ε * Real.log x / T)
        = 1000 * (A * (x ^ (c + ε) / ((c - 1 - ε) * T)))
          + 1000 * (A * (x ^ ε * Real.log x / T)) := by ring
    linarith [key1, key2, mul_nonneg hA.le hX, mul_nonneg hA.le hY]

/-- **The truncated Perron formula.** Let `a` satisfy `‖a n‖ ≤ A_δ n ^ δ` for every `δ > 0`
and let `ε > 0` and `c > 1`. There is `C > 0` such that for every `x` that is not an integer
and every `T` with `1 ≤ T ≤ x`,
`‖∑_{n ≤ x} a n - (1 / 2π) ∫_{-T}^{T} L(a, c + it) x ^ (c + it) / (c + it) dt‖
  ≤ C (x ^ (c + ε) / T + x ^ ε log x / T)`. -/
theorem norm_sum_sub_truncated_perron_le
    {a : ℕ → ℂ} {ε : ℝ} (hε : 0 < ε)
    (ha : ∀ δ : ℝ, 0 < δ → ∃ A : ℝ, 0 < A ∧ ∀ n : ℕ, 1 ≤ n → ‖a n‖ ≤ A * (n : ℝ) ^ δ) :
    ∀ c : ℝ, 1 < c → ∃ C : ℝ, 0 < C ∧ ∀ x R : ℝ, 1 ≤ R → R ≤ x →
      (∀ n : ℕ, (n : ℝ) ≠ x) →
        ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n) -
            ((1 / (2 * π)) • ∫ t in (-R)..R,
              LSeries a ((c : ℂ) + (t : ℂ) * I) *
                  (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) /
                ((c : ℂ) + (t : ℂ) * I))‖ ≤
          C * (x ^ (c + ε) / R + x ^ ε * Real.log x / R) := by
  classical
  intro c hc
  obtain ⟨C0, hC0, hsplit⟩ := tsum_perron_error_le
  obtain ⟨c', hc'def⟩ : ∃ c' : ℝ, c' = min c 2 := ⟨_, rfl⟩
  have hc'1 : 1 < c' := by rw [hc'def]; exact lt_min hc (by norm_num)
  have hc'2 : c' ≤ 2 := by rw [hc'def]; exact min_le_right _ _
  have hc'c : c' ≤ c := by rw [hc'def]; exact min_le_left _ _
  obtain ⟨e, hedef⟩ : ∃ e : ℝ, e = min ε ((c' - 1) / 2) := ⟨_, rfl⟩
  have he0 : 0 < e := by rw [hedef]; exact lt_min hε (by linarith)
  have heε : e ≤ ε := by rw [hedef]; exact min_le_left _ _
  have hec' : 1 + e < c' := by
    have : e ≤ (c' - 1) / 2 := by rw [hedef]; exact min_le_right _ _
    linarith
  obtain ⟨A, hA, hAa⟩ := ha e he0
  have hsum : LSeriesSummable a (c : ℂ) := by
    refine LSeriesSummable_of_le_const_mul_rpow (x := 1 + e) (by simp; linarith)
      ⟨A, fun n hn => ?_⟩
    rw [show 1 + e - 1 = e by ring]
    exact hAa n (Nat.one_le_iff_ne_zero.mpr hn)
  -- the truncated Perron kernel at `x / n`, summed against `a n` (the Perron error sum)
  have hperron : ∀ x R : ℝ, 0 < x → (∀ n : ℕ, (n : ℝ) ≠ x) → 0 < R →
      ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n) -
            ((1 / (2 * π)) • ∫ t in (-R)..R,
              LSeries a ((c : ℂ) + (t : ℂ) * I) *
                  (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) /
                ((c : ℂ) + (t : ℂ) * I))‖ ≤
        ∑' n : ℕ, ‖a (n + 1)‖ * (x / ((n : ℝ) + 1)) ^ c *
            min 1 (1 / (R * |Real.log (x / ((n : ℝ) + 1))|)) := by
    intro x R hx hxi hR
    have hc0 : (0:ℝ) < c := lt_trans one_pos hc
    have hpi : (0:ℝ) < π := Real.pi_pos
    have hxc : (0:ℝ) < x ^ c := Real.rpow_pos_of_pos hx c
    have hre : ∀ t : ℝ, ((c:ℂ) + (t:ℂ) * I).re = c := by intro t; simp
    have hzne : ∀ t : ℝ, ((c:ℂ) + (t:ℂ) * I) ≠ 0 := by
      intro t h
      have h1 : (c:ℝ) = 0 := by simpa using congrArg Complex.re h
      exact hc0.ne' h1
    have hznorm : ∀ t : ℝ, c ≤ ‖((c:ℂ) + (t:ℂ) * I)‖ := by
      intro t
      calc c = ((c:ℂ) + (t:ℂ) * I).re := (hre t).symm
        _ ≤ ‖((c:ℂ) + (t:ℂ) * I)‖ := Complex.re_le_norm _
    have habs : Summable (fun n : ℕ => ‖LSeries.term a (c:ℂ) n‖) :=
      summable_norm_iff.mpr hsum
    obtain ⟨w, hwdef⟩ : ∃ w : ℕ → ℝ, w = fun n => x ^ c * ‖LSeries.term a (c:ℂ) n‖ :=
      ⟨_, rfl⟩
    have hwS : Summable w := by rw [hwdef]; exact habs.mul_left _
    have hw0 : ∀ n, 0 ≤ w n := by
      intro n; rw [hwdef]; exact mul_nonneg hxc.le (norm_nonneg _)
    have hwval : ∀ n : ℕ, n ≠ 0 → w n = ‖a n‖ * (x / n) ^ c := by
      intro n hn
      have hn0 : 0 < n := Nat.pos_of_ne_zero hn
      rw [hwdef]
      simp only [LSeries.term_of_ne_zero hn, norm_div, Complex.norm_natCast_cpow_of_pos hn0,
        Complex.ofReal_re]
      rw [Real.div_rpow hx.le (Nat.cast_nonneg n)]
      ring
    have hw00 : w 0 = 0 := by rw [hwdef]; simp
    have hEcont : ∀ u : ℝ, 0 < u →
        Continuous (fun t : ℝ => ((u:ℝ):ℂ) ^ ((c:ℂ) + (t:ℂ) * I)) :=
      fun u hu => Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hu.ne'))
    have hKcont : ∀ u : ℝ, 0 < u →
        Continuous (fun t : ℝ =>
          ((u:ℝ):ℂ) ^ ((c:ℂ) + (t:ℂ) * I) / ((c:ℂ) + (t:ℂ) * I)) :=
      fun u hu => Continuous.div (hEcont u hu) (by fun_prop) hzne
    obtain ⟨K, hKdef⟩ : ∃ K : ℕ → ℂ, K = fun (n : ℕ) =>
        (1 / (2 * π)) • ∫ t in (-R)..R,
          ((x / (n:ℝ) : ℝ) : ℂ) ^ ((c:ℂ) + (t:ℂ) * I) /
            ((c:ℂ) + (t:ℂ) * I) := ⟨_, rfl⟩
    obtain ⟨D, hDdef⟩ : ∃ D : ℕ → ℂ, D = fun (n : ℕ) =>
        a n * ((PerronKernel.perronStep (x / (n:ℝ)) : ℝ) : ℂ) := ⟨_, rfl⟩
    obtain ⟨B, hBdef⟩ : ∃ B : ℕ → ℝ, B = fun (n : ℕ) =>
        w n * min 1 (1 / (R * |Real.log (x / (n:ℝ))|)) := ⟨_, rfl⟩
    have hK0 : K 0 = 0 := by
      rw [hKdef]
      simp only [Nat.cast_zero, div_zero, Complex.ofReal_zero]
      rw [show (∫ t in (-R)..R,
          (0:ℂ) ^ ((c:ℂ) + (t:ℂ) * I) / ((c:ℂ) + (t:ℂ) * I)) = 0 by
        rw [show (fun t : ℝ =>
            (0:ℂ) ^ ((c:ℂ) + (t:ℂ) * I) / ((c:ℂ) + (t:ℂ) * I))
            = fun _ : ℝ => (0:ℂ) by
          funext t; rw [Complex.zero_cpow (hzne t), zero_div]]
        simp]
      simp
    have hD0 : D 0 = 0 := by rw [hDdef]; simp [PerronKernel.perronStep]
    have hB00 : B 0 = 0 := by rw [hBdef]; simp [hw00]
    have hkey : ∀ n : ℕ, n ≠ 0 →
        ‖K n - ((PerronKernel.perronStep (x / n) : ℝ) : ℂ)‖
          ≤ (x / n) ^ c * min 1 (1 / (R * |Real.log (x / n)|)) := by
      intro n hn
      have hnR : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hxn : 0 < x / n := div_pos hx hnR
      have hxn1 : x / n ≠ 1 := by
        intro h
        exact hxi n ((div_eq_one_iff_eq hnR.ne').mp h).symm
      rw [hKdef]
      exact (PerronKernel.norm_truncated_sub_perronStep_lt hxn hxn1 hc0 hR).le
    have hsplit' : ∀ n : ℕ, n ≠ 0 → ∀ t : ℝ,
        LSeries.term a ((c:ℂ) + (t:ℂ) * I) n *
            (x:ℂ) ^ ((c:ℂ) + (t:ℂ) * I) / ((c:ℂ) + (t:ℂ) * I)
          = a n * (((x / n : ℝ) : ℂ) ^ ((c:ℂ) + (t:ℂ) * I) /
              ((c:ℂ) + (t:ℂ) * I)) :=
      fun n hn t => term_mul_cpow_div a hn hx _
    have hHS : HasSum (fun n : ℕ => a n * K n)
        ((1 / (2 * π)) • ∫ t in (-R)..R,
          LSeries a ((c:ℂ) + (t:ℂ) * I) * (x:ℂ) ^ ((c:ℂ) + (t:ℂ) * I) /
            ((c:ℂ) + (t:ℂ) * I)) := by
      have hmain : HasSum (fun n : ℕ => ∫ t in (-R)..R,
          LSeries.term a ((c:ℂ) + (t:ℂ) * I) n *
              (x:ℂ) ^ ((c:ℂ) + (t:ℂ) * I) / ((c:ℂ) + (t:ℂ) * I))
          (∫ t in (-R)..R,
            LSeries a ((c:ℂ) + (t:ℂ) * I) * (x:ℂ) ^ ((c:ℂ) + (t:ℂ) * I) /
              ((c:ℂ) + (t:ℂ) * I)) := by
        have h := hsum.hasSum_intervalIntegral_term_vertical_mul (hKcont x hx) (B := x ^ c / c)
          (fun t => by
            rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx, hre]
            exact div_le_div_of_nonneg_left hxc.le hc0 (hznorm t)) R
        simpa only [mul_div_assoc] using h
      have hsm := hmain.const_smul (1 / (2 * π) : ℝ)
      refine hsm.congr_fun ?_
      intro n
      rcases eq_or_ne n 0 with rfl | hn
      · simp [hK0]
      · simp only [hsplit' n hn]
        rw [intervalIntegral.integral_const_mul, hKdef, mul_smul_comm]
    have hDzero : ∀ n : ℕ, n ∉ Finset.Icc 1 ⌊x⌋₊ → D n = 0 := by
      intro n hnmem
      rcases eq_or_ne n 0 with rfl | hn
      · exact hD0
      · have hnR : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
        have hnx : ¬ ((n:ℝ) ≤ x) := by
          intro hlt
          refine hnmem ?_
          simp only [Finset.mem_Icc]
          exact ⟨Nat.one_le_iff_ne_zero.mpr hn, Nat.le_floor hlt⟩
        have hlt1 : x / n < 1 := by
          rw [div_lt_one hnR]
          exact lt_of_not_ge hnx
        rw [hDdef]
        simp [PerronKernel.perronStep, hlt1]
    have hDsum : ∑' n, D n = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n := by
      rw [tsum_eq_sum hDzero]
      refine Finset.sum_congr rfl ?_
      intro n hnmem
      simp only [Finset.mem_Icc] at hnmem
      have hn : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hnmem.1
      have hnR : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hnle : (n:ℝ) ≤ x := (Nat.le_floor_iff hx.le).mp hnmem.2
      have hgt1 : 1 < x / n := by
        rw [lt_div_iff₀ hnR]
        have := hxi n
        simpa using lt_of_le_of_ne hnle this
      rw [hDdef]
      simp [PerronKernel.perronStep, not_lt.mpr hgt1.le, hgt1.ne']
    have hDsummable : Summable D := summable_of_ne_finset_zero hDzero
    have hB0 : ∀ n : ℕ, 0 ≤ B n := by
      intro n
      rw [hBdef]
      refine mul_nonneg (hw0 n) (le_min zero_le_one ?_)
      positivity
    have hBle : ∀ n : ℕ, B n ≤ w n := by
      intro n
      rw [hBdef]
      exact mul_le_of_le_one_right (hw0 n) (min_le_left _ _)
    have hBsum : Summable B := Summable.of_nonneg_of_le hB0 hBle hwS
    have hdiffnorm : ∀ n : ℕ, ‖D n - a n * K n‖ ≤ B n := by
      intro n
      rcases eq_or_ne n 0 with rfl | hn
      · rw [hK0, hD0]
        simpa using hB0 0
      · rw [hDdef, hBdef]
        simp only
        rw [show a n * ((PerronKernel.perronStep (x / (n:ℝ)) : ℝ) : ℂ) - a n * K n
            = -(a n * (K n - ((PerronKernel.perronStep (x / (n:ℝ)) : ℝ) : ℂ))) by ring]
        rw [norm_neg, norm_mul, hwval n hn, mul_assoc]
        exact mul_le_mul_of_nonneg_left (hkey n hn) (norm_nonneg _)
    have hnormsummable : Summable (fun n => ‖D n - a n * K n‖) :=
      Summable.of_nonneg_of_le (fun n => norm_nonneg _) hdiffnorm hBsum
    have hshift : ∑' n : ℕ, B n = ∑' n : ℕ, ‖a (n + 1)‖ * (x / ((n : ℝ) + 1)) ^ c *
        min 1 (1 / (R * |Real.log (x / ((n : ℝ) + 1))|)) := by
      rw [hBsum.tsum_eq_zero_add, hB00, zero_add]
      refine tsum_congr fun n => ?_
      rw [hBdef]
      simp only
      rw [hwval (n + 1) (Nat.succ_ne_zero n)]
      push_cast
      ring
    rw [← hDsum, ← hHS.tsum_eq, ← hDsummable.tsum_sub hHS.summable, ← hshift]
    calc ‖∑' n, (D n - a n * K n)‖
        ≤ ∑' n, ‖D n - a n * K n‖ := norm_tsum_le_tsum_norm hnormsummable
      _ ≤ ∑' n, B n := hnormsummable.tsum_le_tsum hdiffnorm hBsum
  -- the error split at the reduced abscissa `c' ≤ 2`, then the factor `x ^ (c - c')`
  have hD : (0:ℝ) < c' - 1 - e := by linarith
  refine ⟨C0 * A * (1 / (c' - 1 - e) + 1), by positivity, ?_⟩
  intro x R hR1 hRx hxi
  have hx1 : 1 ≤ x := le_trans hR1 hRx
  have hx0 : 0 < x := by linarith
  have hR0 : 0 < R := by linarith
  refine le_trans (hperron x R hx0 hxi hR0) ?_
  have hE' := hsplit c' e he0 hec' hc'2 a A x R hA (fun n hn => hAa n hn) hx1 hR1 hRx
  have hmin0 : ∀ n : ℕ, 0 ≤ min 1 (1 / (R * |Real.log (x / ((n : ℝ) + 1))|)) := fun n =>
    le_min zero_le_one (by positivity)
  have hS : Summable (fun n : ℕ => ‖a (n + 1)‖ * (x / ((n : ℝ) + 1)) ^ c' *
      min 1 (1 / (R * |Real.log (x / ((n : ℝ) + 1))|))) := by
    have hp : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (e - c')) := by
      have h := (summable_nat_add_iff 1).mpr
        (Real.summable_nat_rpow.mpr (show e - c' < -1 by linarith))
      simpa [Nat.cast_add, Nat.cast_one] using h
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) (hp.mul_left (A * x ^ c'))
    · exact mul_nonneg (by positivity) (hmin0 n)
    · have hn1 : (0:ℝ) < (n : ℝ) + 1 := by positivity
      have han : ‖a (n + 1)‖ ≤ A * ((n : ℝ) + 1) ^ e := by
        have h := hAa (n + 1) (by omega)
        push_cast at h
        exact h
      have hmin1 : min 1 (1 / (R * |Real.log (x / ((n : ℝ) + 1))|)) ≤ 1 := min_le_left _ _
      have hdiv : (x / ((n : ℝ) + 1)) ^ c' = x ^ c' * ((n : ℝ) + 1) ^ (-c') := by
        rw [Real.div_rpow hx0.le hn1.le, Real.rpow_neg hn1.le, div_eq_mul_inv]
      have hsplitpow : ((n : ℝ) + 1) ^ (e - c') = ((n : ℝ) + 1) ^ e * ((n : ℝ) + 1) ^ (-c') := by
        rw [sub_eq_add_neg, Real.rpow_add hn1]
      have hq : (0:ℝ) ≤ (x / ((n : ℝ) + 1)) ^ c' := by positivity
      calc ‖a (n + 1)‖ * (x / ((n : ℝ) + 1)) ^ c' *
            min 1 (1 / (R * |Real.log (x / ((n : ℝ) + 1))|))
          ≤ ‖a (n + 1)‖ * (x / ((n : ℝ) + 1)) ^ c' * 1 := by
            gcongr
        _ ≤ A * ((n : ℝ) + 1) ^ e * (x / ((n : ℝ) + 1)) ^ c' * 1 := by gcongr
        _ = A * x ^ c' * ((n : ℝ) + 1) ^ (e - c') := by
            rw [hdiv, hsplitpow]; ring
  have hterm : ∀ n : ℕ, ‖a (n + 1)‖ * (x / ((n : ℝ) + 1)) ^ c *
        min 1 (1 / (R * |Real.log (x / ((n : ℝ) + 1))|)) ≤
      x ^ (c - c') * (‖a (n + 1)‖ * (x / ((n : ℝ) + 1)) ^ c' *
        min 1 (1 / (R * |Real.log (x / ((n : ℝ) + 1))|))) := by
    intro n
    have hn1 : (1:ℝ) ≤ (n : ℝ) + 1 := by
      have : (0:ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hxn : 0 < x / ((n : ℝ) + 1) := by positivity
    have hpow : (x / ((n : ℝ) + 1)) ^ c =
        (x / ((n : ℝ) + 1)) ^ (c - c') * (x / ((n : ℝ) + 1)) ^ c' := by
      rw [← Real.rpow_add hxn]; ring_nf
    have hle : (x / ((n : ℝ) + 1)) ^ (c - c') ≤ x ^ (c - c') :=
      Real.rpow_le_rpow hxn.le (div_le_self hx0.le hn1) (by linarith)
    rw [hpow]
    have h0 : 0 ≤ ‖a (n + 1)‖ * (x / ((n : ℝ) + 1)) ^ c' *
        min 1 (1 / (R * |Real.log (x / ((n : ℝ) + 1))|)) :=
      mul_nonneg (by positivity) (hmin0 n)
    calc ‖a (n + 1)‖ * ((x / ((n : ℝ) + 1)) ^ (c - c') * (x / ((n : ℝ) + 1)) ^ c') *
          min 1 (1 / (R * |Real.log (x / ((n : ℝ) + 1))|))
        = (x / ((n : ℝ) + 1)) ^ (c - c') * (‖a (n + 1)‖ * (x / ((n : ℝ) + 1)) ^ c' *
          min 1 (1 / (R * |Real.log (x / ((n : ℝ) + 1))|))) := by ring
      _ ≤ x ^ (c - c') * (‖a (n + 1)‖ * (x / ((n : ℝ) + 1)) ^ c' *
          min 1 (1 / (R * |Real.log (x / ((n : ℝ) + 1))|))) :=
        mul_le_mul_of_nonneg_right hle h0
  have hS' : Summable (fun n : ℕ => ‖a (n + 1)‖ * (x / ((n : ℝ) + 1)) ^ c *
      min 1 (1 / (R * |Real.log (x / ((n : ℝ) + 1))|))) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (by positivity) (hmin0 n)) hterm
      (hS.mul_left _)
  have hxD : 0 < x ^ (c - c') := Real.rpow_pos_of_pos hx0 _
  have hlog : Real.log x ≤ x := by
    have := Real.log_le_sub_one_of_pos hx0; linarith
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have h1 : x ^ (c - c') * x ^ (c' + e) ≤ x ^ (c + ε) := by
    rw [← Real.rpow_add hx0]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have h2 : x ^ (c - c') * (x ^ e * Real.log x) ≤ x ^ (c + ε) := by
    calc x ^ (c - c') * (x ^ e * Real.log x) ≤ x ^ (c - c') * (x ^ e * x ^ (1:ℝ)) := by
          rw [Real.rpow_one]; gcongr
      _ = x ^ (c - c' + e + 1) := by rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]; ring_nf
      _ ≤ x ^ (c + ε) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hP0 : 0 ≤ x ^ ε * Real.log x / R := by positivity
  set D := c' - 1 - e with hDdef
  calc ∑' n : ℕ, ‖a (n + 1)‖ * (x / ((n : ℝ) + 1)) ^ c *
        min 1 (1 / (R * |Real.log (x / ((n : ℝ) + 1))|))
      ≤ ∑' n : ℕ, x ^ (c - c') * (‖a (n + 1)‖ * (x / ((n : ℝ) + 1)) ^ c' *
        min 1 (1 / (R * |Real.log (x / ((n : ℝ) + 1))|))) :=
        hS'.tsum_le_tsum hterm (hS.mul_left _)
    _ = x ^ (c - c') * ∑' n : ℕ, ‖a (n + 1)‖ * (x / ((n : ℝ) + 1)) ^ c' *
        min 1 (1 / (R * |Real.log (x / ((n : ℝ) + 1))|)) := tsum_mul_left
    _ ≤ x ^ (c - c') * (C0 * A * (x ^ (c' + e) / (D * R) + x ^ e * Real.log x / R)) :=
        mul_le_mul_of_nonneg_left hE' hxD.le
    _ = C0 * A * ((x ^ (c - c') * x ^ (c' + e)) / (D * R) +
          (x ^ (c - c') * (x ^ e * Real.log x)) / R) := by ring
    _ ≤ C0 * A * (x ^ (c + ε) / (D * R) + x ^ (c + ε) / R) := by gcongr
    _ = C0 * A * (1 / D + 1) * (x ^ (c + ε) / R) := by field_simp
    _ ≤ C0 * A * (1 / D + 1) * (x ^ (c + ε) / R + x ^ ε * Real.log x / R) := by
        gcongr; linarith

end LSeries
