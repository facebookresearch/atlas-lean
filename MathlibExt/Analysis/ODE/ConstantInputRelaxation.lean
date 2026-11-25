/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.ODE.ScalarRelaxation
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Constant-input scalar relaxation

`amount k R A₀` solves `A' = R - k A`, `A(0) = A₀`. Its closed form gives the
zero-input exponential, half-life shift, sign and steady-state bounds used by
compartment, reservoir, and ventilation models.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory intervalIntegral

namespace MathlibExt.Biology.Biophysics.CompartmentKinetics

open MathlibExt.Biology.Dynamics.FeedForwardLoop (relaxation hasDerivAt_relaxation)

/-- Solution of `A' = R - k A` with constant input `R` and initial value `A₀`. -/
noncomputable def amount (k R A₀ t : ℝ) : ℝ := relaxation k (fun _ ↦ R) A₀ t

/-- Equilibrium `R / k` of the constant-input equation when `k ≠ 0`. -/
noncomputable def steadyAmount (k R : ℝ) : ℝ := R / k

/-- Half-life of exponential decay at a positive rate `k`. -/
noncomputable def halfLife (k : ℝ) : ℝ := log 2 / k

/-- The affine differential equation holds with a two-sided derivative at every `t ≥ 0`. -/
def IsSolution (k R : ℝ) (A : ℝ → ℝ) : Prop :=
  ∀ t, 0 ≤ t → HasDerivAt A (R - k * A t) t

variable {k R A₀ t : ℝ}

@[simp]
theorem amount_zero (k R A₀ : ℝ) : amount k R A₀ 0 = A₀ := by
  simp [amount, relaxation]

theorem hasDerivAt_amount (k R A₀ t : ℝ) :
    HasDerivAt (amount k R A₀) (R - k * amount k R A₀ t) t :=
  hasDerivAt_relaxation A₀ (fun _ _ ↦ intervalIntegrable_const) continuousAt_const

/-- `∫₀ᵗ e^{-k (t - s)} ds = (1 - e^{-k t}) / k` for `k ≠ 0`. -/
theorem integral_exp_neg_mul_sub (hk : k ≠ 0) (t : ℝ) :
    ∫ s in (0)..t, exp (-k * (t - s)) = (1 - exp (-k * t)) / k := by
  have hd (s : ℝ) : HasDerivAt (fun s ↦ exp (-k * (t - s)) / k) (exp (-k * (t - s))) s := by
    have h := ((((hasDerivAt_id s).const_sub t).const_mul (-k)).exp).div_const k
    refine h.congr_deriv ?_
    rw [show (-k * -1 : ℝ) = k by ring, mul_div_assoc, div_self hk, mul_one]
    rfl
  rw [integral_eq_sub_of_hasDerivAt (fun s _ ↦ hd s)
    ((by fun_prop : Continuous fun s ↦ exp (-k * (t - s))).intervalIntegrable 0 t)]
  simp only [sub_self, mul_zero, exp_zero, sub_zero]
  ring

/-- The exponential with negative slope `-k` tends to zero at infinity. -/
theorem tendsto_exp_neg_mul (hk : 0 < k) :
    Tendsto (fun t ↦ exp (-k * t)) atTop (𝓝 0) :=
  (tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hk)).congr fun t ↦ by
    simp [neg_mul]

/-- **Explicit solution, `k ≠ 0`:** `A(t) = A∞ + (A₀ - A∞) e^{-k t}` with `A∞ = R / k`. -/
theorem amount_eq_of_ne_zero (hk : k ≠ 0) (R A₀ t : ℝ) :
    amount k R A₀ t = R / k + (A₀ - R / k) * exp (-k * t) := by
  simp only [amount, relaxation]
  rw [intervalIntegral.integral_mul_const, integral_exp_neg_mul_sub hk]
  ring

/-- With zero removal rate, the amount changes linearly. -/
theorem amount_rate_zero (R A₀ t : ℝ) : amount 0 R A₀ t = A₀ + R * t := by
  simp [amount, relaxation, mul_comm]

/-- **Uniqueness.** A solution of `A' = R - k A` on `[0, ∞)` is `amount k R (A 0)` there. -/
theorem IsSolution.eq_amount {A : ℝ → ℝ} (h : IsSolution k R A) (ht : 0 ≤ t) :
    A t = amount k R (A 0) t := by
  set D : ℝ → ℝ := fun s ↦ (A s - amount k R (A 0) s) * exp (k * s)
  have hD (s : ℝ) (hs : 0 ≤ s) : HasDerivAt D 0 s := by
    have h' : HasDerivAt D (((R - k * A s) - (R - k * amount k R (A 0) s)) * exp (k * s) +
        (A s - amount k R (A 0) s) * (exp (k * s) * (k * 1))) s :=
      ((h s hs).sub (hasDerivAt_amount k R (A 0) s)).mul (((hasDerivAt_id s).const_mul k).exp)
    convert h' using 1
    ring
  have hconst := constant_of_has_deriv_right_zero (f := D) (a := 0) (b := t)
    (fun s hs ↦ (hD s hs.1).continuousAt.continuousWithinAt)
    (fun s hs ↦ (hD s hs.1).hasDerivWithinAt) t ⟨ht, le_rfl⟩
  simp only [D, amount_zero, sub_self, zero_mul, mul_eq_zero, exp_ne_zero, or_false] at hconst
  linarith

/-- **Nonnegativity.** For `k ≥ 0`, `R ≥ 0` and `A₀ ≥ 0` the amount stays nonnegative for
`t ≥ 0`. -/
theorem amount_nonneg (hk : 0 ≤ k) (hR : 0 ≤ R) (hA₀ : 0 ≤ A₀) (ht : 0 ≤ t) :
    0 ≤ amount k R A₀ t := by
  rcases hk.eq_or_lt with rfl | hk
  · rw [amount_rate_zero]
    positivity
  · rw [amount_eq_of_ne_zero hk.ne']
    have he : exp (-k * t) ≤ 1 := exp_le_one_iff.2 (by nlinarith)
    have hRk : 0 ≤ R / k := div_nonneg hR hk.le
    nlinarith [exp_pos (-k * t)]

/-- With zero input the solution is `A₀ e^{-k t}`, including at `k = 0`. -/
theorem amount_bolus (k A₀ t : ℝ) : amount k 0 A₀ t = A₀ * exp (-k * t) := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp [amount_rate_zero]
  · simp [amount_eq_of_ne_zero hk]

/-- At nonzero rate and zero input, a shift by `log 2 / k` halves the solution.
For negative `k` this is a backward shift. -/
theorem amount_bolus_add_halfLife (hk : k ≠ 0) (A₀ t : ℝ) :
    amount k 0 A₀ (t + halfLife k) = amount k 0 A₀ t / 2 := by
  rw [amount_bolus, amount_bolus, halfLife,
    show -k * (t + log 2 / k) = -k * t - log 2 by field_simp; ring, exp_sub, exp_log two_pos]
  ring

/-- With positive removal rate the solution tends to `R / k`. -/
theorem tendsto_amount (hk : 0 < k) (R A₀ : ℝ) :
    Tendsto (amount k R A₀) atTop (𝓝 (steadyAmount k R)) := by
  have he := tendsto_exp_neg_mul hk
  simp_rw [funext (amount_eq_of_ne_zero hk.ne' R A₀), steadyAmount]
  simpa using (he.const_mul (A₀ - R / k)).const_add (R / k)

/-- Starting above the steady state (`R / k ≤ A₀`, `k > 0`), the amount decreases. -/
theorem amount_antitone (hk : 0 < k) (h : steadyAmount k R ≤ A₀) : Antitone (amount k R A₀) := by
  intro a b hab
  rw [amount_eq_of_ne_zero hk.ne', amount_eq_of_ne_zero hk.ne']
  have := mul_le_mul_of_nonneg_left (exp_le_exp.2 (by nlinarith : -k * b ≤ -k * a))
    (sub_nonneg.2 h)
  rw [steadyAmount] at this
  linarith

/-- Starting below the steady state, the amount never exceeds it. -/
theorem amount_le_steadyAmount (hk : 0 < k) (h : A₀ ≤ steadyAmount k R) (t : ℝ) :
    amount k R A₀ t ≤ steadyAmount k R := by
  rw [amount_eq_of_ne_zero hk.ne']
  rw [steadyAmount] at *
  nlinarith [exp_pos (-k * t)]

/-- Starting above the steady state, the amount never falls below it. -/
theorem steadyAmount_le_amount (hk : 0 < k) (h : steadyAmount k R ≤ A₀) (t : ℝ) :
    steadyAmount k R ≤ amount k R A₀ t := by
  rw [amount_eq_of_ne_zero hk.ne']
  rw [steadyAmount] at *
  nlinarith [exp_pos (-k * t)]

end MathlibExt.Biology.Biophysics.CompartmentKinetics
