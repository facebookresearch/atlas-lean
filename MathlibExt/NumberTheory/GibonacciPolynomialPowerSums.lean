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
import Mathlib.Tactic.LinearCombination
import MathlibExt.NumberTheory.Recurrences.HoradamGeneralizedCatalanIdentity

/-!
# Identities and inverse power sums for gibonacci polynomials

The Fibonacci and Lucas polynomials satisfy Catalan-type identities.

For the Fibonacci and Lucas polynomials at a positive real argument, the series of differences
of reciprocal powers sums to its initial block for odd indices with an odd shift and for even
indices with an even shift.
-/

namespace MetaMathlibExt

open Polynomial

local notation "𝔣" => generalizedFibonacciPolynomial 0 1 X 1
local notation "𝔩" => generalizedFibonacciPolynomial 2 X X 1

-- Apply Horadam's identity first at the initial pair and then at the lower index n - k.
private theorem gibonacciPoly_catalan (a b : ℤ[X]) {n k : ℕ} (hk : k ≤ n) :
    generalizedFibonacciPolynomial a b X 1 (n + k) *
        generalizedFibonacciPolynomial a b X 1 (n - k) -
        generalizedFibonacciPolynomial a b X 1 n ^ 2 =
      (-1) ^ (n + k) * (a ^ 2 + X * a * b - b ^ 2) * 𝔣 k ^ 2 := by
  let g := generalizedFibonacciPolynomial a b X 1
  change g (n + k) * g (n - k) - g n ^ 2 = _
  have hrec : ∀ j, g (j + 2) = X * g (j + 1) + 1 * g j :=
    generalizedFibonacciPolynomial_add_two a b X 1
  have catalan := horadam_generalized_catalan_identity X 1 g g 𝔣 hrec hrec
    (generalizedFibonacciPolynomial_add_two 0 1 X 1)
    (generalizedFibonacciPolynomial_zero 0 1 X 1) (generalizedFibonacciPolynomial_one 0 1 X 1)
  have hbase : g 1 * g k - g 0 * g (k + 1) = -(a ^ 2 + X * a * b - b ^ 2) * 𝔣 k := by
    have h := catalan 0 k 1
    simp only [Nat.zero_add, pow_zero, one_mul] at h
    rw [mul_comm (g 1) (g k), h]
    change (b * b - a * g 2) * 𝔣 k = _
    rw [hrec 0]
    change (b * b - a * (X * b + 1 * a)) * 𝔣 k = _
    ring
  have h := catalan (n - k) k k
  rw [Nat.sub_add_cancel hk, hbase] at h
  have hsign : (-1 : ℤ[X]) ^ (n + k) = (-1 : ℤ[X]) ^ (n - k) := by
    have hindex : n + k = (n - k) + 2 * k := by omega
    rw [hindex, pow_add, pow_mul, neg_one_sq, one_pow, mul_one]
  rw [hsign]
  linear_combination -h

/-- **Catalan-type identities for Fibonacci and Lucas polynomials.** Let $f_i$ and $\ell_i$ be
the Fibonacci and Lucas polynomials in $\mathbb{Z}[x]$, defined by $f_0 = 0$, $f_1 = 1$,
$\ell_0 = 2$, $\ell_1 = x$ and $g_{i+2} = x g_{i+1} + g_i$ for $g = f, \ell$. For all natural
numbers $k \le n$,
$$
f_{n+k} f_{n-k} - f_n^2 = (-1)^{n+k+1} f_k^2
\quad\text{and}\quad
\ell_{n+k} \ell_{n-k} - \ell_n^2 = (-1)^{n+k} (x^2 + 4) f_k^2
$$
in $\mathbb{Z}[x]$.

The source quotes this lemma from Koshy.

Source: Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
The Fibonacci Quarterly 62 (2024), Article linzhou02172024,
Lemma 2.1 (`fq-2024-linzhou02172024-lem-2.1`). -/
public theorem gibonacciPoly_mul_sub_sq {n k : ℕ} (hk : k ≤ n) :
    𝔣 (n + k) * 𝔣 (n - k) - 𝔣 n ^ 2 = (-1) ^ (n + k + 1) * 𝔣 k ^ 2 ∧
      𝔩 (n + k) * 𝔩 (n - k) - 𝔩 n ^ 2 = (-1) ^ (n + k) * (X ^ 2 + 4) * 𝔣 k ^ 2 := by
  constructor
  · rw [gibonacciPoly_catalan 0 1 hk, pow_succ (-1 : ℤ[X]) (n + k)]
    ring
  · rw [gibonacciPoly_catalan 2 X hk]
    ring

namespace tsum_inv_pow_gibonacciPoly_sub_odd

private theorem summable_odd_inv_pow {a : ℕ → ℝ} {x : ℝ} (hx : 0 < x)
    (h₀ : 0 ≤ a 0) (h₁ : 0 < a 1) (hrec : ∀ n, a (n + 2) = x * a (n + 1) + a n)
    {lam : ℕ} (hlam : 0 < lam) :
    Summable fun n : ℕ ↦ 1 / a (2 * n + 1) ^ lam := by
  have hpos (n : ℕ) : 0 ≤ a n ∧ 0 < a (n + 1) := by
    induction n with
    | zero => exact ⟨h₀, h₁⟩
    | succ n ih =>
      exact ⟨ih.2.le, hrec n ▸ add_pos_of_pos_of_nonneg (mul_pos hx ih.2) ih.1⟩
  -- Two steps of the recurrence increase each odd term by a factor of at least 1 + x².
  have hgrowth (n : ℕ) : (1 + x ^ 2) * a (2 * n + 1) ≤ a (2 * (n + 1) + 1) := by
    rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega, hrec (2 * n + 1), hrec (2 * n)]
    nlinarith [mul_nonneg hx.le (hpos (2 * n)).1]
  have hfactor : 1 < (1 + x ^ 2) ^ lam := one_lt_pow₀ (by linarith [sq_pos_of_pos hx]) hlam.ne'
  apply summable_of_ratio_norm_eventually_le (inv_lt_one_of_one_lt₀ hfactor)
  apply Filter.Eventually.of_forall
  intro n
  simp only [norm_div, norm_one, norm_pow, Real.norm_eq_abs, abs_of_pos (hpos _).2,
    ← one_div, one_div_mul_one_div, ← mul_pow]
  have hbase := mul_pos (show 0 < 1 + x ^ 2 by positivity) (hpos (2 * n)).2
  exact one_div_le_one_div_of_le (pow_pos hbase _) (pow_le_pow_left₀ hbase.le (hgrowth n) _)

end tsum_inv_pow_gibonacciPoly_sub_odd

-- The telescoping identity holds for every shift `k`; the oddness hypothesis `hk` is kept, under
-- its wanted name, for fidelity to the source's statement.
set_option linter.unusedVariables false in
/-- **Telescoping inverse-power series of gibonacci polynomials at odd indices, odd shift.**
Let $x > 0$ be real, and let $g_n$ denote either the Fibonacci polynomials, given by $g_0 = 0$ and
$g_1 = 1$, or the Lucas polynomials, given by $g_0 = 2$ and $g_1 = x$, both satisfying
$g_{n+2} = x g_{n+1} + g_n$ and evaluated at $x$. Let $k$ be an odd natural number and
$\lambda$ a positive integer. Then
$$\sum_{n=0}^{\infty} \left(\frac{1}{g_{2n+1}^{\lambda}} - \frac{1}{g_{2n+1+2k}^{\lambda}}\right) =
\sum_{r=1}^{k} \frac{1}{g_{2r-1}^{\lambda}}.$$

The source quotes this lemma from Koshy as the sum over $n \ge (k + 1)/2$ of
$1/g_{2n-k}^{\lambda} - 1/g_{2n+k}^{\lambda}$; here the summation index is shifted to start at $0$.

Source: Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
The Fibonacci Quarterly 62 (2024), Article linzhou02172024,
Lemma 2.2 (`fq-2024-linzhou02172024-lem-2.2`). -/
public theorem tsum_inv_pow_gibonacciPoly_sub_odd {x : ℝ} (hx : 0 < x)
    {g : ℕ → ℤ[X]} (hg : g = 𝔣 ∨ g = 𝔩) {k lam : ℕ} (hk : Odd k) (hlam : 0 < lam) :
    ∑' n : ℕ, (1 / aeval x (g (2 * n + 1)) ^ lam - 1 / aeval x (g (2 * n + 1 + 2 * k)) ^ lam) =
      ∑ r ∈ Finset.Icc 1 k, 1 / aeval x (g (2 * r - 1)) ^ lam := by
  let a (n : ℕ) : ℝ := aeval x (g n)
  let f (n : ℕ) := 1 / a (2 * n + 1) ^ lam
  have hs : Summable f := by
    apply tsum_inv_pow_gibonacciPoly_sub_odd.summable_odd_inv_pow (a := a) hx ?_ ?_ ?_ hlam
    · rcases hg with rfl | rfl <;> norm_num [a, map_ofNat]
    · rcases hg with rfl | rfl <;> simp [a, hx]
    · intro n
      rcases hg with rfl | rfl <;> simp [a]
  calc
    _ = ∑' n : ℕ, (f n - f (n + k)) := by
      simp only [f, a, show ∀ n : ℕ, 2 * (n + k) + 1 = 2 * n + 1 + 2 * k by omega]
    _ = ∑ n ∈ Finset.range k, f n := by
      rw [hs.tsum_sub ((summable_nat_add_iff k).2 hs)]
      exact sub_eq_of_eq_add (hs.sum_add_tsum_nat_add k).symm
    _ = _ := by
      rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
      simp only [Nat.add_sub_cancel, f, a, show ∀ n : ℕ, 2 * (1 + n) - 1 = 2 * n + 1 by omega]

-- The source's reindexing uses evenness. The shifted identity holds for every `k`.
set_option linter.unusedVariables false in
/-- **Telescoping inverse-power series of gibonacci polynomials at even indices, even shift.**
Let $x > 0$ be real, and let $g_n$ denote either the Fibonacci polynomials, given by $g_0 = 0$ and
$g_1 = 1$, or the Lucas polynomials, given by $g_0 = 2$ and $g_1 = x$, both satisfying
$g_{n+2} = x g_{n+1} + g_n$ and evaluated at $x$. Let $k$ be an even natural number and
$\lambda$ a positive integer. Then
$$\sum_{n=0}^{\infty} \left(\frac{1}{g_{2n+2}^{\lambda}} - \frac{1}{g_{2n+2+2k}^{\lambda}}\right) =
\sum_{r=1}^{k} \frac{1}{g_{2r}^{\lambda}}.$$

The source quotes this lemma from Koshy as the sum over $n \ge k/2 + 1$ of
$1/g_{2n-k}^{\lambda} - 1/g_{2n+k}^{\lambda}$; here the summation index is shifted to start at $0$.

Source: Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
The Fibonacci Quarterly 62 (2024), Article linzhou02172024,
Lemma 2.3 (`fq-2024-linzhou02172024-lem-2.3`). -/
public theorem tsum_inv_pow_gibonacciPoly_sub_even {x : ℝ} (hx : 0 < x)
    {g : ℕ → ℤ[X]} (hg : g = 𝔣 ∨ g = 𝔩) {k lam : ℕ} (hk : Even k) (hlam : 0 < lam) :
    ∑' n : ℕ, (1 / aeval x (g (2 * n + 2)) ^ lam - 1 / aeval x (g (2 * n + 2 + 2 * k)) ^ lam) =
      ∑ r ∈ Finset.Icc 1 k, 1 / aeval x (g (2 * r)) ^ lam := by
  let a (n : ℕ) : ℝ := aeval x (g n)
  let f (n : ℕ) := 1 / a (2 * n + 2) ^ lam
  have hrec (n : ℕ) : a (n + 2) = x * a (n + 1) + a n := by
    rcases hg with rfl | rfl <;> simp [a]
  have hinit : 0 ≤ a 0 ∧ 0 < a 1 := by
    rcases hg with rfl | rfl <;> norm_num [a, hx, map_ofNat]
  -- Shifting the recurrence by one makes the even terms the odd terms of the shifted sequence.
  have hs : Summable f := by
    apply tsum_inv_pow_gibonacciPoly_sub_odd.summable_odd_inv_pow
      (a := fun n ↦ a (n + 1)) hx hinit.2.le ?_ (fun n ↦ hrec (n + 1)) hlam
    change 0 < a (0 + 2)
    rw [hrec]
    exact add_pos_of_pos_of_nonneg (mul_pos hx hinit.2) hinit.1
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
