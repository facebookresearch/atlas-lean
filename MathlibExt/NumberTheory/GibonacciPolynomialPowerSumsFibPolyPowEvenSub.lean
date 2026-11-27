/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.GeneralizedFibonacciPolynomial
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.LinearCombination
import MathlibExt.NumberTheory.BinetClosedForm

/-!
# Even powers of Fibonacci polynomials

For `k ≤ n`, `(X ^ 2 + 4) ^ (m - 1)` times the difference of the `2m`-th powers
of the Fibonacci polynomials at `n + k` and `n - k` is a signed, binomially weighted
finite sum of products `f_{2k(m-j)} f_{2n(m-j)}`.

Source: Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
The Fibonacci Quarterly 62 (2024), no. 2, 147–156, Lemma 3.1.
-/

namespace MetaMathlibExt

open Polynomial

local notation "𝔣" => generalizedFibonacciPolynomial 0 1 X 1

private theorem sum_pair (f : ℕ → ℝ) (m : ℕ) :
    (∑ j ∈ Finset.range (2 * m + 1), f j) =
      (∑ j ∈ Finset.range m, (f j + f (2 * m - j))) + f m := by
  have hr : (∑ j ∈ Finset.range m, f (m + (j + 1))) =
      ∑ j ∈ Finset.range m, f (2 * m - j) := by
    rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    have := Finset.mem_range.mp hj
    omega
  rw [show 2 * m + 1 = m + (m + 1) by omega, Finset.sum_range_add,
    Finset.sum_range_succ', hr, Finset.sum_add_distrib]
  simp only [Nat.add_zero]
  ring

private theorem even_binomial (a b : ℝ) (m : ℕ) :
    (a - b) ^ (2 * m) =
      (∑ j ∈ Finset.range m, ((2 * m).choose j : ℝ) * (-a * b) ^ j *
        (a ^ (2 * (m - j)) + b ^ (2 * (m - j)))) +
      ((2 * m).choose m : ℝ) * (-a * b) ^ m := by
  rw [sub_pow, sum_pair]
  have hs (j : ℕ) (hj : j < m) :
      (-1 : ℝ) ^ (j + 2 * m) * a ^ j * b ^ (2 * m - j) * (2 * m).choose j +
      (-1 : ℝ) ^ (2 * m - j + 2 * m) * a ^ (2 * m - j) *
        b ^ (2 * m - (2 * m - j)) * (2 * m).choose (2 * m - j) =
      ((2 * m).choose j : ℝ) * (-a * b) ^ j *
        (a ^ (2 * (m - j)) + b ^ (2 * (m - j))) := by
    have hj' : j ≤ 2 * m := by omega
    have he : 2 * m - j = j + 2 * (m - j) := by omega
    have hp : (-1 : ℝ) ^ (2 * m - j + 2 * m) = (-1) ^ j := by
      rw [show 2 * m - j + 2 * m = j + 2 * (2 * m - j) by omega, pow_add]
      simp
    rw [Nat.choose_symm hj', Nat.sub_sub_self hj', hp, he, pow_add]
    rw [mul_pow (-a) b, neg_pow a]
    simp only [pow_add]
    simp
    ring
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    exact hs j (Finset.mem_range.mp hj)
  · rw [show 2 * m - m = m by omega]
    rw [mul_pow (-a) b, neg_pow a]
    simp only [pow_add]
    simp
    ring

private theorem even_cross (a b : ℝ) (hab : a * b = -1) {n k : ℕ}
    (hk : k ≤ n) (t : ℕ) :
    a ^ (2 * k * t) * b ^ (2 * n * t) = b ^ (2 * (n - k) * t) := by
  have he : 2 * n * t = 2 * (n - k) * t + 2 * k * t := by
    conv_lhs => rw [← Nat.sub_add_cancel hk]
    ring
  rw [he, pow_add]
  calc
    _ = (a * b) ^ (2 * k * t) * b ^ (2 * (n - k) * t) := by
      rw [mul_pow]
      ring
    _ = _ := by
      rw [hab, show 2 * k * t = 2 * (k * t) by ring]
      simp

private theorem root_even_sub (a b : ℝ) (hab : a * b = -1) {n k : ℕ}
    (hk : k ≤ n) (m : ℕ) :
    (a ^ (n + k) - b ^ (n + k)) ^ (2 * m) -
        (a ^ (n - k) - b ^ (n - k)) ^ (2 * m) =
      ∑ j ∈ Finset.range m, ((2 * m).choose j : ℝ) * (-1) ^ ((n + k + 1) * j) *
        (a ^ (2 * k * (m - j)) - b ^ (2 * k * (m - j))) *
        (a ^ (2 * n * (m - j)) - b ^ (2 * n * (m - j))) := by
  have hs (r j : ℕ) : (-a ^ r * b ^ r) ^ j = (-1 : ℝ) ^ ((r + 1) * j) := by
    rw [neg_mul, ← mul_pow, hab]
    have he : -(-1 : ℝ) ^ r = (-1) ^ (r + 1) := by
      rw [pow_succ]
      ring
    rw [he, ← pow_mul]
  have hsign (j : ℕ) : (-1 : ℝ) ^ ((n - k + 1) * j) =
      (-1) ^ ((n + k + 1) * j) := by
    rw [pow_mul, pow_mul, show n + k + 1 = n - k + 1 + 2 * k by omega,
      pow_add (-1 : ℝ) (n - k + 1) (2 * k)]
    simp
  rw [even_binomial, even_binomial]
  simp_rw [hs, hsign]
  rw [add_sub_add_right_eq_sub, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have he (r : ℕ) : (a ^ r) ^ (2 * (m - j)) = a ^ (2 * r * (m - j)) := by
    rw [← pow_mul]
    congr 1
    ring
  have he' (r : ℕ) : (b ^ r) ^ (2 * (m - j)) = b ^ (2 * r * (m - j)) := by
    rw [← pow_mul]
    congr 1
    ring
  simp only [he, he']
  have hp : 2 * (n + k) * (m - j) = 2 * n * (m - j) + 2 * k * (m - j) := by
    ring
  have hx := even_cross a b hab hk (m - j)
  have hx' := even_cross b a (by simpa [mul_comm] using hab) hk (m - j)
  rw [hp, pow_add, pow_add]
  linear_combination
    ((2 * m).choose j : ℝ) * (-1) ^ ((n + k + 1) * j) * (hx + hx')

private theorem fib_even_eval (x : ℝ) {n k : ℕ} (hk : k ≤ n) (m : ℕ) :
    (x ^ 2 + 4) ^ (m - 1) *
        (aeval x (𝔣 (n + k)) ^ (2 * m) - aeval x (𝔣 (n - k)) ^ (2 * m)) =
      ∑ j ∈ Finset.range m, ((2 * m).choose j : ℝ) * (-1) ^ ((n + k + 1) * j) *
        aeval x (𝔣 (2 * k * (m - j))) * aeval x (𝔣 (2 * n * (m - j))) := by
  by_cases hm : m = 0
  · simp [hm]
  let u (r : ℕ) : ℝ := aeval x (𝔣 r)
  let s := Real.sqrt (x ^ 2 + 4)
  let a := (x + s) / 2
  let b := (x - s) / 2
  have hs : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hs2 : s ^ 2 = x ^ 2 + 4 := Real.sq_sqrt (by positivity)
  have hab : a * b = -1 := by
    dsimp [a, b]
    nlinarith [hs2]
  have ha : a ^ 2 - x * a + (-1) = 0 := by
    dsimp [a]
    nlinarith [hs2]
  have hb : b ^ 2 - x * b + (-1) = 0 := by
    dsimp [b]
    nlinarith [hs2]
  have hsub : a - b = s := by dsimp [a, b]; ring
  have hne : a ≠ b := sub_ne_zero.mp (hsub ▸ hs.ne')
  have hrec (r : ℕ) : u (r + 2) = x * u (r + 1) - (-1) * u r := by
    simp [u]
  have hu (r : ℕ) : u r * s = a ^ r - b ^ r := by
    have h := binet_closed_form_second_order u x (-1) a b ha hb hne hrec r
    have h₀ : u 0 = 0 := by simp [u]
    have h₁ : u 1 = 1 := by simp [u]
    simpa [h₀, h₁, hsub] using (eq_div_iff (sub_ne_zero.mpr hne)).mp h
  have h := root_even_sub a b hab hk m
  simp_rw [← hu, mul_pow] at h
  have hscale : s ^ 2 * (x ^ 2 + 4) ^ (m - 1) = s ^ (2 * m) := by
    rw [← hs2, ← pow_succ', ← pow_mul]
    congr 1
    omega
  apply mul_left_cancel₀ (pow_ne_zero 2 hs.ne')
  rw [← mul_assoc, hscale, Finset.mul_sum]
  change s ^ (2 * m) * (u (n + k) ^ (2 * m) - u (n - k) ^ (2 * m)) =
    ∑ j ∈ Finset.range m, s ^ 2 * (((2 * m).choose j : ℝ) *
      (-1) ^ ((n + k + 1) * j) * u (2 * k * (m - j)) * u (2 * n * (m - j)))
  calc
    _ = ∑ j ∈ Finset.range m, ((2 * m).choose j : ℝ) *
        (-1) ^ ((n + k + 1) * j) * (u (2 * k * (m - j)) * s) *
        (u (2 * n * (m - j)) * s) := by
      linear_combination h
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      ring

@[expose] public section

/-- **Even powers of Fibonacci polynomials at $n \pm k$.** Let $f_i \in \mathbb{Z}[x]$ be the
Fibonacci polynomials, defined by $f_0 = 0$, $f_1 = 1$ and $f_{i+2} = x f_{i+1} + f_i$. For all
natural numbers $k \le n$ and every natural number $m$,
$$
(x^2 + 4)^{m-1} \bigl(f_{n+k}^{2m} - f_{n-k}^{2m}\bigr) =
\sum_{j=0}^{m-1} \binom{2m}{j} (-1)^{(n+k+1)j} f_{2k(m-j)} f_{2n(m-j)}
$$
in $\mathbb{Z}[x]$, where for $m = 0$ the exponent $m - 1$ is read as $0$ (both sides are then
$0$).

Source: Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
The Fibonacci Quarterly 62 (2024), Article linzhou02172024,
Lemma 3.1 (`fq-2024-linzhou02172024-lem-3.1`). -/
public theorem fibPoly_pow_even_sub {n k : ℕ} (hk : k ≤ n) (m : ℕ) :
    (X ^ 2 + 4) ^ (m - 1) * (𝔣 (n + k) ^ (2 * m) - 𝔣 (n - k) ^ (2 * m)) =
      ∑ j ∈ Finset.range m, ((2 * m).choose j : ℤ[X]) * (-1) ^ ((n + k + 1) * j) *
        𝔣 (2 * k * (m - j)) * 𝔣 (2 * n * (m - j))
    := by
  apply Polynomial.map_injective (Int.castRingHom ℝ) Int.cast_injective
  apply Polynomial.funext
  intro x
  simp only [eval_map]
  change aeval x ((X ^ 2 + 4) ^ (m - 1) *
      (𝔣 (n + k) ^ (2 * m) - 𝔣 (n - k) ^ (2 * m))) =
    aeval x (∑ j ∈ Finset.range m, ((2 * m).choose j : ℤ[X]) *
      (-1) ^ ((n + k + 1) * j) * 𝔣 (2 * k * (m - j)) * 𝔣 (2 * n * (m - j)))
  simpa only [map_mul, map_pow, map_sub, map_add, map_sum, map_natCast,
    map_ofNat, map_neg, map_one, aeval_X] using fib_even_eval x hk m

end

end MetaMathlibExt
