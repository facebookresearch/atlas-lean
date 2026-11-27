/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.NumberTheory.Bernoulli
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import MathlibExt.Combinatorics.Enumerative.StirlingSecondExpDeriv

/-!
# Derivatives of powers and the reciprocal of $(1 - e^x)/x$ at zero

Let $f(x) = (1 - e^x)/x$ off zero and $f(0) = -1$. Then
`MetaMathlibExt.iteratedDeriv_pow_one_sub_exp_div_self_zero` gives the derivatives of $f^k$
at zero in terms of Stirling numbers of the second kind, and
`MetaMathlibExt.iteratedDeriv_inv_one_sub_exp_div_self_zero` gives those of $1/f$ in terms of
Bernoulli numbers.

The function $f$ is the slope function `dslope` of $h(x) = 1 - e^x$ at $0$. For the powers,
Leibniz's rule applied to $x^k f(x)^k = (1-e^x)^k$ isolates the derivative of $f^k$.
The derivative of $(1-e^x)^k$ is given by `iteratedDeriv_one_sub_exp_pow` in
`MathlibExt.Combinatorics.Enumerative.StirlingSecondExpDeriv`. For the reciprocal,
differentiating $(1/f) \cdot h = \mathrm{id}$ gives the Bernoulli recurrence `sum_bernoulli`.

## References

* Horst Alzer and Kendall C. Richards, *Extensions of Some Combinatorial Identities and
  Various Related Results*, INTEGERS 25 (2025), Article A61, pp. 1–20, Lemmas 1 and 2 (p. 9).
* I. S. Gradshteyn and I. M. Ryzhik, *Table of Integrals, Series, and Products*, 7th ed.,
  Elsevier, 2007, p. 1047 (the expansion cited in Lemma 1).
* Kunle Adegoke and Robert Frontczak, *Three Classes of Combinatorial Sums Involving
  Central Binomial Coefficients and Harmonic Numbers*, INTEGERS 26 (2026), Article A109,
  pp. 1–16, Lemma 1 (p. 10), for the derivative of $(1-e^x)^k$.
-/

namespace MetaMathlibExt

open Finset

private theorem analyticAt_one_sub_exp_div_self {f : ℝ → ℝ} (hf0 : f 0 = -1)
    (hf : ∀ x ≠ 0, f x = (1 - Real.exp x) / x) : AnalyticAt ℝ f 0 := by
  let h : ℝ → ℝ := fun x => 1 - Real.exp x
  have ha : AnalyticAt ℝ h 0 := analyticAt_const.sub analyticAt_rexp
  have hdslope : f = dslope h 0 := by
    funext x
    rcases eq_or_ne x 0 with rfl | hx
    · simp [dslope_same, hf0, h]
    · simp [dslope_of_ne _ hx, slope_def_field, hf x hx, h]
  rw [hdslope]
  exact ha.dslope 0

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
  -- `f` is analytic and nonzero at `0`, so `1 / f` is analytic there as well.
  have hga : AnalyticAt ℝ (fun x => 1 / f x) 0 :=
    analyticAt_const.div (analyticAt_one_sub_exp_div_self hf0 hf) (by norm_num [hf0])
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

/-- **Derivatives at zero of powers of $(1 - e^x)/x$.** Write $S(n, k)$ for the Stirling numbers
of the second kind. Let $f : \mathbb{R} \to \mathbb{R}$ satisfy $f(0) = -1$ and
$f(x) = (1 - e^x)/x$ for every $x \ne 0$. Then for all natural numbers $k$ and $r$, the $r$-th
derivative of $f^k$ at $0$ equals $(-1)^k S(r+k, k) / \binom{r+k}{k}$.

This is the expansion recorded in Gradshteyn and Ryzhik, p. 1047.

Source: Horst Alzer and Kendall C. Richards, *Extensions of Some Combinatorial Identities and
Various Related Results*, INTEGERS 25 (2025), Article A61, Lemma 1. -/
public theorem iteratedDeriv_pow_one_sub_exp_div_self_zero {f : ℝ → ℝ} (hf0 : f 0 = -1)
    (hf : ∀ x ≠ 0, f x = (1 - Real.exp x) / x) (k r : ℕ) :
    iteratedDeriv r (fun x => f x ^ k) 0 =
      (-1 : ℝ) ^ k * (Nat.stirlingSecond (r + k) k : ℝ) / ((r + k).choose k : ℝ) := by
  have hfa := analyticAt_one_sub_exp_div_self hf0 hf
  have hprod : (fun x => x ^ k * f x ^ k) = fun x => (1 - Real.exp x) ^ k := by
    have hxmul (x : ℝ) : x * f x = 1 - Real.exp x := by
      rcases eq_or_ne x 0 with rfl | hx
      · simp
      · rw [hf x hx, mul_comm x, div_mul_cancel₀ _ hx]
    funext x
    rw [← mul_pow, hxmul]
  -- In the Leibniz sum, only the order-`k` derivative of `x^k` is nonzero at `0`.
  have hxpow : ContDiffAt ℝ (r + k : ℕ) (fun x : ℝ => x ^ k) 0 := contDiffAt_id.pow k
  have h : ∑ j ∈ range (r + k + 1), ((r + k).choose j : ℝ) *
      iteratedDeriv j (fun x : ℝ => x ^ k) 0 * iteratedDeriv (r + k - j) (fun x => f x ^ k) 0 =
        iteratedDeriv (r + k) (fun x : ℝ => x ^ k * f x ^ k) 0 :=
    (iteratedDeriv_fun_mul hxpow (hfa.pow k).contDiffAt).symm
  have hExp := (iteratedDeriv_one_sub_exp_pow k (r + k) 0).1
  rw [hprod, hExp.1.trans hExp.2] at h
  rw [sum_eq_single k] at h
  · rw [iteratedDeriv_fun_pow_zero, ite_eq_left rfl, show r + k - k = r by omega] at h
    have hk : (k.factorial : ℝ) ≠ 0 := by positivity
    have hc : ((r + k).choose k : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_ne_zero (Nat.le_add_left k r))
    apply (eq_div_iff hc).2
    apply mul_right_cancel₀ hk
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h
  · intro j _ hj
    simp only [iteratedDeriv_fun_pow_zero, ite_eq_right hj, Nat.cast_zero, mul_zero, zero_mul]
  · intro hk
    exact (hk (mem_range.mpr (by omega))).elim

end MetaMathlibExt
