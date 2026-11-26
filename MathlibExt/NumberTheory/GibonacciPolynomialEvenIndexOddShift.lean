/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import MathlibExt.NumberTheory.GeneralizedFibonacciPolynomial
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Odd-shift telescoping at even Gibonacci indices

At a positive real argument, the even-indexed Fibonacci and Lucas polynomials grow at least
geometrically. The difference between the series of reciprocal powers and its shifted tail is
therefore the finite sum of its initial terms.

## References

* Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
  The Fibonacci Quarterly 62 (2024), no. 2, 147–156, Lemma 2.4.
* Thomas Koshy, *Sums Involving Gibonacci Polynomial Squares*, The Fibonacci Quarterly 61 (2023),
  no. 2, 98–104, §1.3, Lemma 3, the result cited by Lin and Zhou.
* Thomas Koshy, *Additional Sums Involving Gibonacci Polynomials*, The Fibonacci Quarterly 61
  (2023), no. 1, 12–20, §2.1, Lemma 3, the reciprocal case cited by Koshy's later paper.
-/

namespace MetaMathlibExt

open Polynomial

local notation "𝔣" => generalizedFibonacciPolynomial 0 1 X 1
local notation "𝔩" => generalizedFibonacciPolynomial 2 X X 1

-- The source uses oddness in the reindexing; the reindexed telescoping argument works for any k.
set_option linter.unusedVariables false in
/-- **Telescoping inverse-power series of gibonacci polynomials at even indices, odd shift.**
Let $x > 0$ be real, and let $g_n$ denote either the Fibonacci polynomials, given by $g_0 = 0$ and
$g_1 = 1$, or the Lucas polynomials, given by $g_0 = 2$ and $g_1 = x$, both satisfying
$g_{n+2} = x g_{n+1} + g_n$ and evaluated at $x$. Let $k$ be an odd natural number and
$\lambda$ a positive integer. Then
$$\sum_{n=0}^{\infty} \left(\frac{1}{g_{2n+2}^{\lambda}} - \frac{1}{g_{2n+2+2k}^{\lambda}}\right) =
\sum_{r=1}^{k} \frac{1}{g_{2r}^{\lambda}}.$$

The source quotes this lemma from Koshy as the sum over $n \ge (k + 1)/2$ of
$1/g_{2n+1-k}^{\lambda} - 1/g_{2n+1+k}^{\lambda}$; here the summation index is shifted to start
at $0$.

Source: Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
The Fibonacci Quarterly 62 (2024), Article linzhou02172024,
Lemma 2.4 (`fq-2024-linzhou02172024-lem-2.4`). -/
public theorem tsum_inv_pow_gibonacciPoly_succ_sub_odd {x : ℝ} (hx : 0 < x)
    {g : ℕ → ℤ[X]} (hg : g = 𝔣 ∨ g = 𝔩) {k lam : ℕ} (hk : Odd k) (hlam : 0 < lam) :
    ∑' n : ℕ, (1 / aeval x (g (2 * n + 2)) ^ lam - 1 / aeval x (g (2 * n + 2 + 2 * k)) ^ lam) =
      ∑ r ∈ Finset.Icc 1 k, 1 / aeval x (g (2 * r)) ^ lam := by
  let a (n : ℕ) : ℝ := aeval x (g n)
  let f (n : ℕ) : ℝ := 1 / a (2 * n + 2) ^ lam
  have hs : Summable f := by
    have hrec (n : ℕ) : a (n + 2) = x * a (n + 1) + a n := by
      rcases hg with rfl | rfl <;> simp [a]
    have hpos (n : ℕ) : 0 ≤ a n ∧ 0 < a (n + 1) := by
      induction n with
      | zero => rcases hg with rfl | rfl <;> norm_num [a, hx, map_ofNat]
      | succ n ih =>
        exact ⟨ih.2.le, hrec n ▸ add_pos_of_pos_of_nonneg (mul_pos hx ih.2) ih.1⟩
    have heven (n : ℕ) : 0 < a (2 * n + 2) := (hpos (2 * n + 1)).2
    -- Unroll the recurrence twice to bound the next even term from below.
    have hgrowth (n : ℕ) : (1 + x ^ 2) * a (2 * n + 2) ≤ a (2 * (n + 1) + 2) := by
      rw [show 2 * (n + 1) + 2 = (2 * n + 2) + 2 by omega, hrec (2 * n + 2),
        show 2 * n + 2 + 1 = (2 * n + 1) + 2 by omega, hrec (2 * n + 1)]
      nlinarith [mul_nonneg hx.le (hpos (2 * n + 1)).1]
    have hfactor : 1 < 1 + x ^ 2 := lt_add_of_pos_right 1 (sq_pos_of_pos hx)
    have hratio : ((1 + x ^ 2) ^ lam)⁻¹ < 1 :=
      inv_lt_one_of_one_lt₀ (one_lt_pow₀ hfactor hlam.ne')
    apply summable_of_ratio_norm_eventually_le hratio
    apply Filter.Eventually.of_forall
    intro n
    simp only [f, norm_div, norm_one, norm_pow, Real.norm_eq_abs, abs_of_pos (heven _),
      ← one_div, one_div_mul_one_div, ← mul_pow]
    have hbase := mul_pos (zero_lt_one.trans hfactor) (heven n)
    exact one_div_le_one_div_of_le (pow_pos hbase _) (pow_le_pow_left₀ hbase.le (hgrowth n) _)
  -- As in `tsum_inv_pow_gibonacciPoly_sub_even`, subtract the summable tail.
  calc
    _ = ∑' n : ℕ, (f n - f (n + k)) := by
      simp only [f, a, show ∀ n : ℕ, 2 * (n + k) + 2 = 2 * n + 2 + 2 * k by omega]
    _ = ∑ n ∈ Finset.range k, f n := by
      rw [hs.tsum_sub ((summable_nat_add_iff k).2 hs)]
      exact sub_eq_of_eq_add (hs.sum_add_tsum_nat_add k).symm
    _ = _ := by
      rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
      simp only [Nat.add_sub_cancel, f, a, show ∀ n : ℕ, 2 * (1 + n) = 2 * n + 2 by omega]

end MetaMathlibExt
