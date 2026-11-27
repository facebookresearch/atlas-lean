/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.NumberTheory.Bernoulli
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Derivatives of $x/(1 - e^x)$ at zero

The main result, `MetaMathlibExt.iteratedDeriv_inv_one_sub_exp_div_self_zero`, states that if
$f(0) = -1$ and $f(x) = (1 - e^x)/x$ for $x \ne 0$, then the $k$-th derivative of $1/f$ at $0$
is $-B_k$, where $B_k$ is `bernoulli k` (so $B_1 = -1/2$). Equivalently, $x/(e^x - 1)$,
extended by $1$ at $0$, has $k$-th derivative $B_k$ at $0$.

The function $f$ is the slope function `dslope` of $h(x) = 1 - e^x$ at $0$, so $1/f$ is analytic
at $0$. Differentiating $(1/f) \cdot h = \mathrm{id}$ at $0$ with Leibniz's rule, using $h(0) = 0$
and $h^{(m)}(0) = -1$ for $m \ge 1$, shows that the derivatives of $-1/f$ at $0$ satisfy the
recursion `sum_bernoulli` of the Bernoulli numbers.
-/

namespace MetaMathlibExt

open Finset

/-- **Derivatives of $x/(1 - e^x)$ at zero.** Write $B_k$ for the $k$-th Bernoulli number,
with the convention $B_1 = -1/2$. Let $f : \mathbb{R} \to \mathbb{R}$ satisfy $f(0) = -1$ and
$f(x) = (1 - e^x)/x$ for every $x \ne 0$. Then for every natural number $k$, the $k$-th
derivative of $1/f$ at $0$ equals $-B_k$.

Source: Horst Alzer and Kendall C. Richards, *Extensions of Some Combinatorial Identities and
Various Related Results*, INTEGERS 25 (2025), Article A61, Lemma 2. -/
public theorem iteratedDeriv_inv_one_sub_exp_div_self_zero {f : ℝ → ℝ} (hf0 : f 0 = -1)
    (hf : ∀ x ≠ 0, f x = (1 - Real.exp x) / x) (k : ℕ) :
    iteratedDeriv k (fun x => 1 / f x) 0 = -(bernoulli k : ℝ) := by
  set h : ℝ → ℝ := fun x => 1 - Real.exp x with h_def
  have hha : AnalyticAt ℝ h 0 := analyticAt_const.sub analyticAt_rexp
  -- `f` is the slope function of `h` at `0`, so `1 / f` is analytic at `0`.
  have hdslope : f = dslope h 0 := by
    funext x
    rcases eq_or_ne x 0 with rfl | hx
    · simp [dslope_same, hf0, h_def]
    · simp [dslope_of_ne _ hx, slope_def_field, hf x hx, h_def]
  have hga : AnalyticAt ℝ (fun x => 1 / f x) 0 :=
    analyticAt_const.div (hdslope ▸ hha.dslope 0) (by norm_num [hf0])
  -- `(1 / f x) * h x = x` for every real `x`.
  have hprod : (fun x => 1 / f x * h x) = fun x => x := by
    funext x
    rcases eq_or_ne x 0 with rfl | hx
    · simp [h_def]
    · have hx' : 1 - Real.exp x ≠ 0 :=
        sub_ne_zero.mpr fun he => hx (Real.exp_eq_one_iff x |>.mp he.symm)
      rw [hf x hx, h_def]
      field_simp
  -- The derivatives of `h` at `0` are `0, -1, -1, ...`.
  have hh (m : ℕ) : iteratedDeriv m h 0 = if m = 0 then 0 else -1 := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [h_def]
    · rw [h_def, iteratedDeriv_const_sub hm, iteratedDeriv_neg, iteratedDeriv_eq_iterate,
        Real.iter_deriv_exp]
      simp [hm.ne']
  -- Leibniz's rule applied to `(1 / f) * h = id`.
  have hrec (n : ℕ) :
      ∑ i ∈ range (n + 1), (n.choose i : ℝ) * iteratedDeriv i (fun x => 1 / f x) 0 *
        iteratedDeriv (n - i) h 0 = if n = 1 then 1 else 0 := by
    rw [← iteratedDeriv_fun_mul hga.contDiffAt hha.contDiffAt, hprod, iteratedDeriv_fun_id_zero]
  -- At order `k + 1`, the recursion determines the `k`-th derivative from the earlier ones in the
  -- same way as `sum_bernoulli` determines `B_k`; conclude by strong induction.
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    have hB : ∑ i ∈ range (k + 1), ((k + 1).choose i : ℝ) * (bernoulli i : ℝ) =
        if k + 1 = 1 then 1 else 0 := by
      simpa only [Rat.cast_sum, Rat.cast_mul, Rat.cast_natCast, apply_ite (Rat.cast : ℚ → ℝ),
        Rat.cast_one, Rat.cast_zero] using congrArg (Rat.cast : ℚ → ℝ) (sum_bernoulli (k + 1))
    have hR := hrec (k + 1)
    -- The last term vanishes since `h 0 = 0`; the others carry the factor `-1`.
    rw [sum_range_succ, Nat.sub_self, hh 0, ite_eq_left rfl, mul_zero, add_zero,
      sum_congr rfl fun i hi => by
        rw [hh (k + 1 - i), ite_eq_right (by simp only [mem_range] at hi; omega)]] at hR
    rw [sum_range_succ, sum_congr rfl fun i hi => by rw [ih i (mem_range.mp hi)]] at hR
    simp only [mul_neg, mul_one, neg_neg] at hR
    rw [sum_range_succ, Nat.choose_succ_self_right] at hB
    rw [Nat.choose_succ_self_right] at hR
    have hk : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    apply mul_left_cancel₀ hk
    linear_combination hB - hR

end MetaMathlibExt
