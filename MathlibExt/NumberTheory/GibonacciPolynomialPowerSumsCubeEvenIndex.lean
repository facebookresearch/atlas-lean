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
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import MathlibExt.NumberTheory.FibonacciPolynomialOddPowerSub
import MathlibExt.NumberTheory.GibonacciPolynomialPowerSums
import MathlibExt.NumberTheory.Recurrences.LucasPolynomialSquareFamily

/-!
# Cubic series at even Fibonacci polynomial indices

For a positive real argument `x`, the odd shift `1` and even shift `2` give two
cubic-denominator series at even Fibonacci polynomial indices, starting at indices `2` and `4`,
respectively. The positivity hypothesis ensures that the shifted Fibonacci values are nonzero
and that their reciprocal powers decay. The odd-power and Catalan identities rewrite each
summand as `x ^ 2 + 4` times a difference of inverse cubes, so only the initial terms survive.

## References

* Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
  The Fibonacci Quarterly 62 (2024), no. 2, 147–156, Corollary 4.3, Theorem 1.5, and
  Lemmas 2.1–2.3 and 4.1.
* Thomas Koshy, *Sums Involving Gibonacci Polynomial Squares*, The Fibonacci Quarterly
  61 (2023), no. 2, 98–104, §1.1, Eq. (4), and §1.3, Lemmas 1–2. Lin and Zhou cite
  these for the product identity and the reciprocal-power telescoping in Lemmas 2.1–2.3.
-/

namespace MetaMathlibExt

open Polynomial

local notation "𝔣" => generalizedFibonacciPolynomial 0 1 X 1
local notation "𝔩" => generalizedFibonacciPolynomial 2 X X 1
local notation "F[" x "," n "]" => aeval x (𝔣 n)
local notation "L[" x "," n "]" => aeval x (𝔩 n)

/-- **Cubic-denominator series for even-index Fibonacci polynomials.** Let $f_i$ and $\ell_i$ be the
Fibonacci and Lucas polynomials, defined by $f_0 = 0$, $f_1 = 1$, $\ell_0 = 2$, $\ell_1 = x$ and
$g_{i+2} = x g_{i+1} + g_i$ for $g = f, \ell$. For every real $x > 0$,
$$
\sum_{n \ge 1} \frac{(x^3 + 3x) f_{6n}(x) + 3x f_{2n}(x)}{(f_{2n}(x)^2 + 1)^3} = x^2 + 4
$$
and
$$
\sum_{n \ge 2} \frac{x(x^4 + 4x^2 + 3) \ell_{6n}(x) - 3x \ell_{2n}(x)}{(f_{2n}(x)^2 - x^2)^3} =
\frac{(x^2 + 4)\bigl((x^2 + 2)^3 + 1\bigr)}{x^3 (x^2 + 2)^3}.
$$

Source: Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
The Fibonacci Quarterly 62 (2024), Article linzhou02172024,
Corollary 4.3 (`fq-2024-linzhou02172024-cor-4.3`). -/
public theorem tsum_fibPoly_cube_even_index {x : ℝ} (hx : 0 < x) :
    ∑' n : ℕ, ((x ^ 3 + 3 * x) * aeval x (𝔣 (6 * (n + 1))) + 3 * x * aeval x (𝔣 (2 * (n + 1)))) /
        (aeval x (𝔣 (2 * (n + 1))) ^ 2 + 1) ^ 3 =
      x ^ 2 + 4 ∧
      ∑' n : ℕ, (x * (x ^ 4 + 4 * x ^ 2 + 3) * aeval x (𝔩 (6 * (n + 2))) -
          3 * x * aeval x (𝔩 (2 * (n + 2)))) /
          (aeval x (𝔣 (2 * (n + 2))) ^ 2 - x ^ 2) ^ 3 =
        (x ^ 2 + 4) * ((x ^ 2 + 2) ^ 3 + 1) / (x ^ 3 * (x ^ 2 + 2) ^ 3) := by
  have hf₂ : F[x, 2] = x := by simp
  have hf₄ : F[x, 4] = x * (x ^ 2 + 2) := by
    simp
    ring
  have hf₆ : F[x, 6] = x * (x ^ 4 + 4 * x ^ 2 + 3) := by
    simp
    ring
  have hl₃ : L[x, 3] = x ^ 3 + 3 * x := by
    simp [map_ofNat]
    ring
  have hpos := pos_of_gibonacci_recurrence hx (fun n ↦ F[x, n + 1])
    (fun n ↦ by simp [Nat.add_right_comm n 2 1]) (by simp) (by rw [hf₂]; exact hx)
  have hsign (n : ℕ) : (-1 : ℝ) ^ (2 * n) = 1 := (even_two_mul n).neg_one_pow
  constructor
  · calc
      _ = ∑' n : ℕ, (x ^ 2 + 4) * (1 / F[x, 2 * n + 1] ^ 3 -
          1 / F[x, 2 * n + 1 + 2] ^ 3) := by
        apply tsum_congr
        intro n
        have hk : 1 ≤ 2 * (n + 1) := by omega
        have hlo : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
        have hhi : 2 * (n + 1) + 1 = 2 * n + 1 + 2 := by omega
        have hmul : 2 * (n + 1) * 3 = 6 * (n + 1) := by omega
        have hden := congrArg (aeval x) (gibonacciPoly_mul_sub_sq hk).1
        simp only [map_sub, map_mul, map_pow, map_neg, map_one, pow_succ (-1 : ℝ), hsign,
          mul_neg, mul_one, neg_neg, generalizedFibonacciPolynomial_one,
          one_pow, hlo, hhi] at hden
        have hprod : F[x, 2 * (n + 1)] ^ 2 + 1 = F[x, 2 * n + 1] * F[x, 2 * n + 1 + 2] := by
          linear_combination -hden
        have hnum := congrArg (aeval x) ((fibPoly_pow_odd_sub hk 1).1 (by decide))
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, map_add, map_sub,
          map_mul, map_pow, map_neg, map_one, map_natCast, map_ofNat, aeval_X, hlo, hhi, hmul,
          Nat.choose_zero_right, Nat.choose_one_right, Nat.mul_zero, Nat.mul_one, hsign,
          generalizedFibonacciPolynomial_one, hl₃] at hnum
        rw [hprod, div_sub_div _ _ (pow_ne_zero 3 (hpos (2 * n)).ne')
          (pow_ne_zero 3 (hpos (2 * n + 2)).ne'), ← mul_pow, one_mul, mul_one, ← mul_div_assoc]
        congr 1
        linear_combination -hnum
      _ = x ^ 2 + 4 := by
        rw [tsum_mul_left, tsum_inv_pow_gibonacciPoly_sub_odd hx (Or.inl rfl)
          (k := 1) (lam := 3) (by decide) (by decide)]
        simp
  · calc
      _ = ∑' n : ℕ, (x ^ 2 + 4) * (1 / F[x, 2 * n + 2] ^ 3 -
          1 / F[x, 2 * n + 2 + 4] ^ 3) := by
        apply tsum_congr
        intro n
        have hk : 2 ≤ 2 * (n + 2) := by omega
        have hlo : 2 * (n + 2) - 2 = 2 * n + 2 := by omega
        have hhi : 2 * (n + 2) + 2 = 2 * n + 2 + 4 := by omega
        have hmul : 2 * (n + 2) * 3 = 6 * (n + 2) := by omega
        have hden := congrArg (aeval x) (gibonacciPoly_mul_sub_sq hk).1
        simp only [map_sub, map_mul, map_pow, map_neg, map_one, pow_succ (-1 : ℝ), hsign,
          neg_one_mul, mul_neg, mul_one, neg_neg, hlo, hhi, hf₂] at hden
        have hprod : F[x, 2 * (n + 2)] ^ 2 - x ^ 2 = F[x, 2 * n + 2] * F[x, 2 * n + 2 + 4] := by
          linear_combination -hden
        have hnum := congrArg (aeval x) ((fibPoly_pow_odd_sub hk 1).2 (by decide))
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, map_add, map_sub,
          map_mul, map_pow, map_neg, map_one, map_natCast, map_ofNat, aeval_X, hlo, hhi, hmul,
          Nat.choose_zero_right, Nat.choose_one_right, Nat.mul_zero, Nat.mul_one,
          pow_succ (-1 : ℝ), hsign, hf₂, hf₆] at hnum
        rw [hprod, div_sub_div _ _ (pow_ne_zero 3 (hpos (2 * n + 1)).ne')
          (pow_ne_zero 3 (hpos (2 * n + 5)).ne'), ← mul_pow, one_mul, mul_one, ← mul_div_assoc]
        congr 1
        linear_combination -hnum
      _ = _ := by
        rw [tsum_mul_left, tsum_inv_pow_gibonacciPoly_sub_even hx (Or.inl rfl)
          (k := 2) (lam := 3) (by decide) (by decide)]
        have hIcc : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
        rw [hIcc, Finset.sum_pair (by decide)]
        norm_num only [Nat.reduceMul, hf₂, hf₄, mul_pow]
        have hx₂ : x ^ 2 + 2 ≠ 0 := by positivity
        field_simp [hx.ne', hx₂]

end MetaMathlibExt
