/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import MathlibExt.NumberTheory.GeneralizedFibonacciPolynomial
import Mathlib.Tactic.LinearCombination
import MathlibExt.NumberTheory.Recurrences.GibonacciPolynomialRatioTelescoping
import MathlibExt.NumberTheory.Recurrences.HoradamGeneralizedCatalanIdentity

/-!
# Sums involving a family of Jacobsthal polynomial squares

We prove the reciprocal sums of shifted Fibonacci and Lucas polynomial squares.
`tsum_gibonacciPoly_sq_sub_family_of_catalan` states the sum for either sequence with its Catalan
constant, and `tsum_gibonacciPoly_sq_sub_family` specializes it to the two sequences.

Statements from Thomas Koshy and Zhenguang Gao, *Sums Involving a Family of Jacobsthal Polynomial
Squares*, The Fibonacci Quarterly 62 (2024), Article koshy12202023.

The Fibonacci and Lucas polynomials `f_n`, `l_n` (`z_{n+2} = x z_{n+1} + z_n`, initial values
`0, 1` and `2, x`) and the Jacobsthal and Jacobsthal-Lucas polynomials `J_n`, `j_n`
(`z_{n+2} = z_{n+1} + x z_n`, initial values `0, 1` and `2, 1`) are the existing
`generalizedFibonacciPolynomial` sequences over `ℤ[X]`, evaluated at real `x > 0` with
`Polynomial.aeval`. As in the paper, `Δ = √(x² + 4)`, `α = (x + Δ)/2`, `D = √(4x + 1)` and
`w = (1 + D)/2`.
-/

namespace MetaMathlibExt

open Polynomial

/-- The Fibonacci polynomials `f_n(x)`. -/
local notation "𝔣" => generalizedFibonacciPolynomial 0 1 X 1

/-- The Lucas polynomials `l_n(x)`. -/
local notation "𝔩" => generalizedFibonacciPolynomial 2 X X 1

/-- **Reciprocal sums of shifted squares of the Fibonacci or Lucas polynomials, with the Catalan
constant.** Let `x > 0`, let `g` be the Fibonacci polynomials `f_n` or the Lucas polynomials
`l_n`, and let `C = g_1(x)^2 - g_0(x) g_2(x)` (`C = 1` for `f` and `C = -(x^2 + 4)` for `l`).
For positive integers `k`, `p`, `r`, `t` with `t ≤ 2p` and `α = (x + √(x^2 + 4))/2`,
`∑_{n ≥ 0} (-1)^{tk} C f_r(x) f_{2pk}(x) / (g_{(2pn+p+t)k}(x)^2 - (-1)^{tk} C f_{pk}(x)^2)`
equals `g_{tk+r}(x)/g_{tk}(x) - α^r`. The proof shows that `g_n(x) > 0` for `n ≥ 1`, factors
each denominator as `g_{(2pn+t)k}(x) g_{(2p(n+1)+t)k}(x)` with the Catalan identity, and
telescopes. `tsum_gibonacciPoly_sq_sub_family` is the case `g = f`, `C = 1` together with the
case `g = l`, `C = -(x^2 + 4)`. -/
public theorem tsum_gibonacciPoly_sq_sub_family_of_catalan {x : ℝ} (hx : 0 < x) (g : ℕ → ℤ[X])
    (C : ℝ) (hg : g = 𝔣 ∨ g = 𝔩) (hC : aeval x (g 1) * aeval x (g 1) -
      aeval x (g 0) * aeval x (g 2) = C)
    {k p r t : ℕ} (hk : 0 < k) (hp : 0 < p) (hr : 0 < r) (ht₀ : 0 < t) (ht : t ≤ 2 * p) :
    ∑' n : ℕ, (-1) ^ (t * k) * C * aeval x (𝔣 r) * aeval x (𝔣 (2 * p * k)) /
        (aeval x (g ((2 * p * n + p + t) * k)) ^ 2 -
          (-1) ^ (t * k) * C * aeval x (𝔣 (p * k)) ^ 2) =
      aeval x (g (t * k + r)) / aeval x (g (t * k)) - ((x + √(x ^ 2 + 4)) / 2) ^ r := by
  let G (n : ℕ) := aeval x (g n)
  let F (n : ℕ) := aeval x (𝔣 n)
  have hG (n : ℕ) : G (n + 2) = x * G (n + 1) + 1 * G n := by
    rcases hg with rfl | rfl <;> simp [G]
  have hF (n : ℕ) : F (n + 2) = x * F (n + 1) + 1 * F n := by simp [F]
  have hseeds : 0 ≤ G 0 ∧ 0 < G 1 := by
    rcases hg with rfl | rfl <;> norm_num [G, hx, map_ofNat]
  have hpos' (n : ℕ) : 0 ≤ G n ∧ 0 < G (n + 1) := by
    induction n with
    | zero => exact hseeds
    | succ n ih =>
      refine ⟨ih.2.le, ?_⟩
      rw [hG, one_mul]
      exact add_pos_of_pos_of_nonneg (mul_pos hx ih.2) ih.1
  have hpos {n : ℕ} (hn : 0 < n) : 0 < G n := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    exact (hpos' j).2
  have catalan := horadam_generalized_catalan_identity x 1 G G F hG hG hF
    (by simp [F]) (by simp [F])
  change G 1 * G 1 - G 0 * G 2 = C at hC
  have det (s i j : ℕ) :
      G (s + i) * G (s + j) - G s * G (s + i + j) = (-1) ^ s * C * F j * F i := by
    have hseed := catalan 0 j 1
    simp only [Nat.zero_add, pow_zero, one_mul, mul_comm (G j) (G 1), hC] at hseed
    rw [catalan, hseed]
    ring
  let e (n : ℕ) := (2 * p * n + t) * k
  have hnext (n : ℕ) : e (n + 1) = e n + 2 * p * k := by dsimp [e]; ring
  have hsign (n : ℕ) : (-1 : ℝ) ^ e n = (-1) ^ (t * k) := by
    simp [e, Nat.add_mul, pow_add, Nat.mul_assoc, pow_mul]
  have hprev (n : ℕ) : 2 * p * (n + 1) + t - 2 * p = 2 * p * n + t := by
    rw [Nat.mul_succ]
    omega
  have hsum := hasSum_gibonacciPoly_pow_ratio_telescoping g hg hx hk hr ht₀
    (m := 1) one_pos ht
  simp only [hprev, pow_one, one_mul] at hsum
  apply HasSum.tsum_eq
  refine hsum.congr_fun fun n => ?_
  have he : 0 < e n := Nat.mul_pos (Nat.add_pos_right _ ht₀) hk
  have he' : 0 < e (n + 1) := by
    rw [hnext]
    exact Nat.add_pos_right _ (by positivity)
  change (-1) ^ (t * k) * C * F r * F (2 * p * k) /
      (G ((2 * p * n + p + t) * k) ^ 2 - (-1) ^ (t * k) * C * F (p * k) ^ 2) =
    G (e n + r) / G (e n) - G (e (n + 1) + r) / G (e (n + 1))
  -- Equal shifts factor the square denominator into two positive sequence values.
  have hden : G ((2 * p * n + p + t) * k) ^ 2 - (-1) ^ (t * k) * C * F (p * k) ^ 2 =
      G (e n) * G (e (n + 1)) := by
    have h := det (e n) (p * k) (p * k)
    rw [hsign] at h
    rw [show (2 * p * n + p + t) * k = e n + p * k by dsimp [e]; ring, hnext,
      show e n + 2 * p * k = e n + p * k + p * k by ring]
    linear_combination h
  rw [hden, div_sub_div _ _ (hpos he).ne' (hpos he').ne']
  congr 1
  rw [hnext, show e n + 2 * p * k + r = e n + r + 2 * p * k by omega, det, hsign]
  ring

/-- **Reciprocal sums of shifted squares of Fibonacci and Lucas polynomials (Koshy–Gao,
Theorem 2.1).** Let $f_n(x)$ and $l_n(x)$ be the Fibonacci and Lucas polynomials, given by
$z_{n+2} = x z_{n+1} + z_n$ with initial values $f_0 = 0$, $f_1 = 1$ and $l_0 = 2$, $l_1 = x$.
Let $x > 0$ be real, let $k$, $p$, $r$, $t$ be positive integers with $t \le 2p$, and let
$\alpha = (x + \sqrt{x^2 + 4})/2$. Then
$$
\sum_{n=0}^{\infty} \frac{(-1)^{tk} f_r(x) f_{2pk}(x)}
{f_{(2pn+p+t)k}(x)^2 - (-1)^{tk} f_{pk}(x)^2} =
\frac{f_{tk+r}(x)}{f_{tk}(x)} - \alpha^r
$$
and
$$
\sum_{n=0}^{\infty} \frac{(-1)^{tk+1} (x^2 + 4) f_r(x) f_{2pk}(x)}
{l_{(2pn+p+t)k}(x)^2 + (-1)^{tk} (x^2 + 4) f_{pk}(x)^2} =
\frac{l_{tk+r}(x)}{l_{tk}(x)} - \alpha^r.
$$

In the source the sums run over $n \ge 1$, with $(2pn + t - p)k$ in place of $(2pn + p + t)k$;
here the summation index is shifted to start at $n = 0$.

Source: Thomas Koshy and Zhenguang Gao, *Sums Involving a Family of Jacobsthal Polynomial
Squares*, The Fibonacci Quarterly 62 (2024), Article koshy12202023,
Theorem 2.1 (`fq-2024-koshy12202023-thm-2.1`). -/
public theorem tsum_gibonacciPoly_sq_sub_family {x : ℝ} (hx : 0 < x) {k p r t : ℕ}
    (hk : 0 < k) (hp : 0 < p) (hr : 0 < r) (ht₀ : 0 < t) (ht : t ≤ 2 * p) :
    ∑' n : ℕ, (-1) ^ (t * k) * aeval x (𝔣 r) * aeval x (𝔣 (2 * p * k)) /
        (aeval x (𝔣 ((2 * p * n + p + t) * k)) ^ 2 - (-1) ^ (t * k) * aeval x (𝔣 (p * k)) ^ 2) =
      aeval x (𝔣 (t * k + r)) / aeval x (𝔣 (t * k)) - ((x + √(x ^ 2 + 4)) / 2) ^ r ∧
    ∑' n : ℕ, (-1) ^ (t * k + 1) * (x ^ 2 + 4) * aeval x (𝔣 r) * aeval x (𝔣 (2 * p * k)) /
        (aeval x (𝔩 ((2 * p * n + p + t) * k)) ^ 2 +
          (-1) ^ (t * k) * (x ^ 2 + 4) * aeval x (𝔣 (p * k)) ^ 2) =
      aeval x (𝔩 (t * k + r)) / aeval x (𝔩 (t * k)) - ((x + √(x ^ 2 + 4)) / 2) ^ r := by
  constructor
  · simpa only [mul_one] using
      tsum_gibonacciPoly_sq_sub_family_of_catalan hx 𝔣 1 (Or.inl rfl)
        (by simp) hk hp hr ht₀ ht
  · simpa only [pow_succ (-1 : ℝ) (t * k), mul_neg, mul_neg_one, neg_mul, sub_neg_eq_add,
      mul_assoc, one_mul] using
      tsum_gibonacciPoly_sq_sub_family_of_catalan hx 𝔩 (-(x ^ 2 + 4)) (Or.inr rfl)
        (by norm_num [generalizedFibonacciPolynomial, map_ofNat]; ring) hk hp hr ht₀ ht

end MetaMathlibExt
