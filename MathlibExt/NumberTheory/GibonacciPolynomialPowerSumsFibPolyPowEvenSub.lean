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
import MathlibExt.NumberTheory.FibonacciPolynomialBinet

/-!
# Even powers of Fibonacci and Lucas polynomials

For natural numbers `k ≤ n` and `m`, the differences of the `2m`-th powers at `n + k` and
`n - k` have signed, binomially weighted expansions in products `f_{2k(m-j)} f_{2n(m-j)}`.
The Fibonacci identity scales the difference by `(X ^ 2 + 4) ^ (m - 1)`; the Lucas identity
scales the sum by `X ^ 2 + 4`. Both identities also cover `m = 0` (the sum is empty and the
zeroth powers agree) and `k = 0` (the indices agree and every summand has a factor `f_0`).

## References

* Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
  The Fibonacci Quarterly 62 (2024), no. 2, 147–156, Lemmas 3.1 and 3.2.
* Thomas Koshy, *Fibonacci and Lucas Numbers with Applications*, vol. 2,
  John Wiley & Sons, 2019 (Binet formulas, as cited by Lin and Zhou in §2).
* `MathlibExt.NumberTheory.FibonacciPolynomialBinet` supplies `fib_binet`, `lucas_binet`,
  `root_mul_other` and `root_diff_sq` in the quadratic algebra over `ℤ[X]`.
-/

namespace MetaMathlibExt

open Polynomial FibonacciPolynomialBinet

local notation "𝔣" => generalizedFibonacciPolynomial 0 1 X 1
local notation "𝔩" => generalizedFibonacciPolynomial 2 X X 1

private theorem sum_pair {R : Type*} [AddCommMonoid R] (f : ℕ → R) (m : ℕ) :
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
    Finset.sum_range_succ', hr, Finset.sum_add_distrib, Nat.add_zero]
  ac_rfl

private theorem even_binomial {R : Type*} [CommSemiring R] (a b : R) (m : ℕ) :
    (a + b) ^ (2 * m) =
      (∑ j ∈ Finset.range m, ((2 * m).choose j : R) * (a * b) ^ j *
        (a ^ (2 * (m - j)) + b ^ (2 * (m - j)))) +
      ((2 * m).choose m : R) * (a * b) ^ m := by
  rw [add_pow, sum_pair]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have he : 2 * m - j = j + 2 * (m - j) := by omega
    rw [Nat.choose_symm (by omega : j ≤ 2 * m), Nat.sub_sub_self (by omega), he,
      pow_add a, pow_add b, mul_pow]
    ring
  · rw [show 2 * m - m = m by omega, mul_pow]
    ring

private theorem even_cross {R : Type*} [CommRing R] (a b : R) (hab : a * b = -1) {n k : ℕ}
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

-- `s = 0` gives the Lucas root sum and `s = 1` the Fibonacci root difference.
private theorem root_even_sub {R : Type*} [CommRing R] (a b : R) (hab : a * b = -1)
    {n k : ℕ} (hk : k ≤ n) (m s : ℕ) :
    (a ^ (n + k) + (-1) ^ s * b ^ (n + k)) ^ (2 * m) -
        (a ^ (n - k) + (-1) ^ s * b ^ (n - k)) ^ (2 * m) =
      ∑ j ∈ Finset.range m, ((2 * m).choose j : R) * (-1) ^ ((n + k + s) * j) *
        (a ^ (2 * k * (m - j)) - b ^ (2 * k * (m - j))) *
        (a ^ (2 * n * (m - j)) - b ^ (2 * n * (m - j))) := by
  have hexp (r : ℕ) :
      (a ^ r + (-1) ^ s * b ^ r) ^ (2 * m) =
        (∑ j ∈ Finset.range m, ((2 * m).choose j : R) * (-1) ^ ((r + s) * j) *
          (a ^ (2 * r * (m - j)) + b ^ (2 * r * (m - j)))) +
        ((2 * m).choose m : R) * (-1) ^ ((r + s) * m) := by
    have hprod : a ^ r * ((-1) ^ s * b ^ r) = (-1 : R) ^ (r + s) := by
      calc
        _ = (a * b) ^ r * (-1) ^ s := by rw [mul_pow]; ac_rfl
        _ = _ := by rw [hab, pow_add]
    have hs (t : ℕ) : ((-1 : R) ^ s) ^ (2 * t) = 1 := by
      rw [← pow_mul, show s * (2 * t) = 2 * (s * t) by ring, pow_mul, neg_one_sq, one_pow]
    have hindex (t : ℕ) : r * (2 * t) = 2 * r * t := by ring
    rw [even_binomial, hprod]
    simp_rw [mul_pow ((-1 : R) ^ s), hs, one_mul, ← pow_mul, hindex]
  have hsign (j : ℕ) : (-1 : R) ^ ((n - k + s) * j) = (-1) ^ ((n + k + s) * j) := by
    rw [pow_mul, pow_mul, show n + k + s = n - k + s + 2 * k by omega,
      pow_add (-1 : R) (n - k + s) (2 * k), pow_mul (-1 : R) 2, neg_one_sq, one_pow, mul_one]
  rw [hexp, hexp]
  simp_rw [hsign]
  rw [add_sub_add_right_eq_sub, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have hp : 2 * (n + k) * (m - j) = 2 * n * (m - j) + 2 * k * (m - j) := by ring
  have hx := even_cross a b hab hk (m - j)
  have hx' := even_cross b a (by simpa [mul_comm] using hab) hk (m - j)
  rw [hp, pow_add, pow_add]
  linear_combination ((2 * m).choose j : R) * (-1) ^ ((n + k + s) * j) * (hx + hx')

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
  have h := root_even_sub a b hab hk m 1
  simp only [pow_one, neg_one_mul, ← sub_eq_add_neg] at h
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

open scoped QuadraticAlgebra

local notation "A" => QuadraticAlgebra ℤ[X] (1 : ℤ[X]) X
local notation "ι" => algebraMap ℤ[X] A
local notation "α" => (QuadraticAlgebra.omega : A)
local notation "β" => (ι X - α)

/-- **Even powers of Lucas polynomials at $n \pm k$.** Let $f_i$ and $\ell_i$ be the
Fibonacci and Lucas polynomials in $\mathbb{Z}[x]$, defined by $f_0 = 0$, $f_1 = 1$, $\ell_0 = 2$,
$\ell_1 = x$ and $g_{i+2} = x g_{i+1} + g_i$ for $g = f, \ell$. For all natural numbers
$k \le n$ and every natural number $m$,
$$
\ell_{n+k}^{2m} - \ell_{n-k}^{2m} =
(x^2 + 4) \sum_{j=0}^{m-1} \binom{2m}{j} (-1)^{(n+k)j} f_{2k(m-j)} f_{2n(m-j)}
$$
in $\mathbb{Z}[x]$.

Source: Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
The Fibonacci Quarterly 62 (2024), Article linzhou02172024,
Lemma 3.2 (`fq-2024-linzhou02172024-lem-3.2`). -/
public theorem lucasPoly_pow_even_sub {n k : ℕ} (hk : k ≤ n) (m : ℕ) :
    𝔩 (n + k) ^ (2 * m) - 𝔩 (n - k) ^ (2 * m) =
      (X ^ 2 + 4) * ∑ j ∈ Finset.range m, ((2 * m).choose j : ℤ[X]) * (-1) ^ ((n + k) * j) *
        𝔣 (2 * k * (m - j)) * 𝔣 (2 * n * (m - j)) := by
  apply QuadraticAlgebra.algebraMap_injective (a := (1 : ℤ[X])) (b := X)
  have h := root_even_sub α β root_mul_other hk m 0
  simp only [pow_zero, one_mul, add_zero] at h
  rw [map_sub, map_pow, map_pow, lucas_binet, lucas_binet, h, map_mul, ← root_diff_sq,
    map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [map_mul, map_natCast, map_pow, map_neg, map_one, ← fib_binet]
  ring

end MetaMathlibExt
