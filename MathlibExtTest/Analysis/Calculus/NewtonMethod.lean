/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Calculus.NewtonMethod
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic

open MetaMathlibExt

-- Newton iteration for `x² - 4` converges to `2` from every sufficiently close start.
example :
    ∃ δ > 0, ∀ x₀ ∈ Set.Ioo (2 - δ) (2 + δ),
      ∀ X : ℕ → ℝ, X 0 = x₀ →
        (∀ n, X (n + 1) = X n - (X n ^ 2 - 4) /
          deriv (fun x : ℝ => x ^ 2 - 4) (X n)) →
        Filter.Tendsto X Filter.atTop (nhds 2) := by
  have hderiv_sq_sub_four (y : ℝ) :
      deriv (fun x : ℝ => x ^ 2 - 4) y = 2 * y := by
    have hpow : deriv (fun x : ℝ => x ^ 2) y = 2 * y := by
      change deriv ((id : ℝ → ℝ) ^ 2) y = 2 * y
      rw [deriv_pow (differentiableAt_id (𝕜 := ℝ)) 2, deriv_id]
      norm_num
    change deriv ((fun x : ℝ => x ^ 2) - fun _ => 4) y = 2 * y
    rw [deriv_sub (by fun_prop) (by fun_prop), hpow, deriv_const]
    ring
  have hf : ContDiff ℝ 2 (fun x : ℝ => x ^ 2 - 4) := by fun_prop
  have hroot : (2 : ℝ) ^ 2 - 4 = 0 := by norm_num
  have hderiv : deriv (fun x : ℝ => x ^ 2 - 4) 2 ≠ 0 := by
    rw [hderiv_sq_sub_four]
    norm_num
  obtain ⟨δ, hδ, _, hmain⟩ :=
    newton_method_local_quadratic_convergence hf hroot hderiv
  refine ⟨δ, hδ, ?_⟩
  intro x₀ hx₀ X hX₀ hrec
  exact (hmain x₀ hx₀ X hX₀ hrec).2.2

-- The one-step bound controls the concrete Newton update from `3` toward the root `2`.
example :
    |(3 : ℝ) - ((3 : ℝ) ^ 2 - 4) /
      deriv (fun x : ℝ => x ^ 2 - 4) 3 - 2| ≤ 1 / 3 := by
  have hderiv_sq_sub_four (y : ℝ) :
      deriv (fun x : ℝ => x ^ 2 - 4) y = 2 * y := by
    have hpow : deriv (fun x : ℝ => x ^ 2) y = 2 * y := by
      change deriv ((id : ℝ → ℝ) ^ 2) y = 2 * y
      rw [deriv_pow (differentiableAt_id (𝕜 := ℝ)) 2, deriv_id]
      norm_num
    change deriv ((fun x : ℝ => x ^ 2) - fun _ => 4) y = 2 * y
    rw [deriv_sub (by fun_prop) (by fun_prop), hpow, deriv_const]
    ring
  have hf : Differentiable ℝ (fun x : ℝ => x ^ 2 - 4) := by fun_prop
  have hK : LipschitzOnWith (2 : NNReal)
      (deriv (fun x : ℝ => x ^ 2 - 4)) (Set.uIcc 2 3) := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro a _ b _
    rw [hderiv_sq_sub_four, hderiv_sq_sub_four, Real.dist_eq, Real.dist_eq]
    change |2 * a - 2 * b| ≤ (2 : ℝ) * |a - b|
    calc
      |2 * a - 2 * b| = |(2 : ℝ) * (a - b)| := by
        congr 1
        ring
      _ = 2 * |a - b| := by
        rw [abs_mul]
        norm_num
      _ ≤ 2 * |a - b| := le_rfl
  have h := newton_step_sub_root_abs_le (c := (2 : ℝ)) (x := 3)
    (m := 6) (K := (2 : NNReal)) hf (by norm_num) (by norm_num) hK (by
      rw [hderiv_sq_sub_four]
      norm_num)
  rw [hderiv_sq_sub_four] at h ⊢
  calc
    |(3 : ℝ) - ((3 : ℝ) ^ 2 - 4) / (2 * 3) - 2| ≤
        (2 / 6 : ℝ) * |(3 : ℝ) - 2| ^ 2 := by simpa using h
    _ = 1 / 3 := by norm_num

private noncomputable def expNewton (x : ℝ) : ℕ → ℝ
  | 0 => x
  | n + 1 => expNewton x n - 1 + Real.exp (-(expNewton x n))

private theorem deriv_exp_sub_one : deriv (fun x : ℝ => Real.exp x - 1) = Real.exp :=
  funext fun x => ((Real.hasDerivAt_exp x).sub_const 1).deriv

private theorem expNewton_rec (x : ℝ) (n : ℕ) :
    expNewton x (n + 1) = expNewton x n - (Real.exp (expNewton x n) - 1) /
      deriv (fun y : ℝ => Real.exp y - 1) (expNewton x n) := by
  rw [expNewton, deriv_exp_sub_one, Real.exp_neg, sub_div, div_self (Real.exp_ne_zero _), one_div]
  ring

-- On [0, 1] the explicit update is nonnegative and at most half the old iterate.
private theorem expNewton_contract {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ x - 1 + Real.exp (-x) ∧ x - 1 + Real.exp (-x) ≤ x / 2 := by
  have hexp : Real.exp (-x) ≤ 1 / (1 + x) := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by linarith) (by linarith [Real.add_one_le_exp x])
  have hfrac : 1 / (1 + x) ≤ 1 - x / 2 := by
    rw [div_le_iff₀ (by linarith : 0 < (1 : ℝ) + x)]
    nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hx1)]
  exact ⟨by linarith [Real.add_one_le_exp (-x)], by linarith [hexp.trans hfrac]⟩

-- Squeeze the explicit tail between zero and a geometric sequence, without the global theorem.
private theorem expNewton_tail {x : ℝ} (hx0 : 0 ≤ expNewton x 1) (hx1 : expNewton x 1 ≤ 1) :
    Filter.Tendsto (expNewton x) Filter.atTop (nhds 0) ∧
      (∀ n : ℕ, 0 ≤ expNewton x (n + 1)) ∧
      ∀ n : ℕ, expNewton x (n + 2) ≤ expNewton x (n + 1) := by
  have half (n : ℕ) (h0 : 0 ≤ expNewton x (n + 1)) (h1 : expNewton x (n + 1) ≤ 1) :
      0 ≤ expNewton x (n + 2) ∧ expNewton x (n + 2) ≤ expNewton x (n + 1) / 2 :=
    expNewton_contract h0 h1
  have hpow_le (n : ℕ) : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hbounds (n : ℕ) : 0 ≤ expNewton x (n + 1) ∧ expNewton x (n + 1) ≤ (1 / 2 : ℝ) ^ n := by
    induction n with
    | zero => exact ⟨hx0, by simpa using hx1⟩
    | succ n ih =>
      have h := half n ih.1 (ih.2.trans (hpow_le n))
      refine ⟨h.1, h.2.trans ?_⟩
      rw [pow_succ]
      linarith [ih.2]
  refine ⟨(Filter.tendsto_add_atTop_iff_nat 1).mp ?_, fun n => (hbounds n).1, ?_⟩
  · exact squeeze_zero (fun n => (hbounds n).1) (fun n => (hbounds n).2)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
  · intro n
    obtain ⟨h0, hle⟩ := hbounds n
    exact (half n h0 (hle.trans (hpow_le n))).2.trans (by linarith)

private theorem expNewton_below_first : expNewton (-Real.log 2) 1 = 1 - Real.log 2 := by
  change -Real.log 2 - 1 + Real.exp (-(-Real.log 2)) = _
  rw [neg_neg, Real.exp_log (by norm_num)]
  ring

-- The root is unique by injectivity of the exponential.
example (s : ℝ) : Real.exp s - 1 = 0 ↔ s = 0 := by
  rw [sub_eq_zero, ← Real.exp_zero, Real.exp_eq_exp]

-- A start below zero crosses the root strictly on the very first step.
example : expNewton (-Real.log 2) 0 < 0 ∧ 0 < expNewton (-Real.log 2) 1 := by
  have hlog := Real.log_lt_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    (show (2 : ℝ) ≠ 1 by norm_num)
  rw [expNewton_below_first]
  exact ⟨neg_neg_of_pos (Real.log_pos (by norm_num)), by linarith⟩

-- Both this below-root start and the above-root start at 1 have a nonnegative,
-- nonincreasing tail that converges to zero.
example (x : ℝ) (hx : x = -Real.log 2 ∨ x = 1) :
    Filter.Tendsto (expNewton x) Filter.atTop (nhds 0) ∧
      (∀ n : ℕ, 0 ≤ expNewton x (n + 1)) ∧
      ∀ n : ℕ, expNewton x (n + 2) ≤ expNewton x (n + 1) := by
  rcases hx with rfl | rfl
  · apply expNewton_tail <;> rw [expNewton_below_first]
    · linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    · linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  · have h := expNewton_contract (by norm_num : (0 : ℝ) ≤ 1) le_rfl
    exact expNewton_tail h.1 (h.2.trans (by norm_num))

-- Starting at the root gives a constant sequence, so both inequalities can be equalities.
example (n : ℕ) : expNewton 0 n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [expNewton, ih, Real.exp_zero]

-- Client check: the public theorem applies to the explicit iteration from below the root.
example : Filter.Tendsto (expNewton (-Real.log 2)) Filter.atTop (nhds 0) := by
  have hf : ContDiff ℝ 2 (fun x : ℝ => Real.exp x - 1) := by fun_prop
  have hf' : ∀ x, 0 < deriv (fun x : ℝ => Real.exp x - 1) x := by
    rw [deriv_exp_sub_one]
    exact Real.exp_pos
  have hf'' : ∀ x, 0 < deriv (deriv (fun x : ℝ => Real.exp x - 1)) x := by
    rw [deriv_exp_sub_one, Real.deriv_exp]
    exact Real.exp_pos
  have hr : Real.exp 0 - 1 = 0 := by simp
  exact ((newton_method_global_convergence hf hf' hf'' hr).2 _ (expNewton_rec _)).1
