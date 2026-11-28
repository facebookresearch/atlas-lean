/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.GeneralizedFibonacciPolynomial
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.FibonacciPolynomialBinet

/-!
# Differences of odd powers of Fibonacci polynomials

Pairing complementary terms in the binomial expansion gives the odd-power identity for both
parities of the shift. The Binet formulas are used in a quadratic algebra over `ℤ[X]`, so
no division by the root difference is needed.

## References

* Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
  The Fibonacci Quarterly 62 (2024), no. 2, 147–156, Lemma 4.1.
* Thomas Koshy, *Fibonacci and Lucas Numbers with Applications*, vol. 2,
  John Wiley & Sons, 2019, §31.1 (Binet formulas; see Lin and Zhou, §2).
* `MathlibExt.NumberTheory.FibonacciPolynomialBinet` provides the quadratic-algebra Binet formulas
  and root identities used here.
-/

namespace MetaMathlibExt

open Polynomial

local notation "𝔣" => generalizedFibonacciPolynomial 0 1 X 1
local notation "𝔩" => generalizedFibonacciPolynomial 2 X X 1

-- In the upper half of the binomial sum, reflect the index about the midpoint.
private theorem sub_pow_odd_pair {R : Type*} [CommRing R] (a b : R) (m : ℕ) :
    (a - b) ^ (2 * m + 1) =
      ∑ j ∈ Finset.range (m + 1), ((2 * m + 1).choose j : R) * (-(a * b)) ^ j *
        (a ^ (2 * m + 1 - 2 * j) - b ^ (2 * m + 1 - 2 * j)) := by
  rw [sub_eq_add_neg, add_pow]
  let f (j : ℕ) : R := a ^ j * (-b) ^ (2 * m + 1 - j) * (2 * m + 1).choose j
  change ∑ j ∈ Finset.range (2 * m + 1 + 1), f j = _
  have hpair : (∑ j ∈ Finset.range (2 * m + 1 + 1), f j) =
      ∑ j ∈ Finset.range (m + 1), (f j + f (2 * m + 1 - j)) := by
    rw [show 2 * m + 1 + 1 = (m + 1) + (m + 1) by omega,
      Finset.sum_range_add, Finset.sum_add_distrib]
    congr 1
    rw [← Finset.sum_range_reflect (fun j ↦ f (m + 1 + j))]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_range.mp hj
    congr 1
    omega
  rw [hpair]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_range.mp hj
  let d := 2 * m + 1 - 2 * j
  have hd : Odd d := ⟨m - j, by dsimp [d]; omega⟩
  have hsplit : 2 * m + 1 - j = j + d := by dsimp [d]; omega
  have hreflect : 2 * m + 1 - (2 * m + 1 - j) = j := by omega
  change f j + f (2 * m + 1 - j) =
    ((2 * m + 1).choose j : R) * (-(a * b)) ^ j * (a ^ d - b ^ d)
  dsimp only [f]
  rw [hreflect, Nat.choose_symm (by omega : j ≤ 2 * m + 1), hsplit, pow_add, pow_add,
    ← mul_neg, mul_pow, hd.neg_pow]
  ring

private theorem root_sub_pow_odd {R : Type*} [CommRing R] {a b : R} (hab : a * b = -1)
    (r m : ℕ) :
    (a ^ r - b ^ r) ^ (2 * m + 1) =
      ∑ j ∈ Finset.range (m + 1), ((2 * m + 1).choose j : R) * (-1) ^ ((r + 1) * j) *
        (a ^ (r * (2 * m + 1 - 2 * j)) - b ^ (r * (2 * m + 1 - 2 * j))) := by
  rw [sub_pow_odd_pair]
  have hsign : -(a ^ r * b ^ r) = (-1 : R) ^ (r + 1) := by
    rw [← mul_pow, hab, pow_succ, mul_neg_one]
  simp only [hsign, pow_mul]

-- The sign of the shift decides which factor is a sum of root powers.
private theorem root_diff_shift {R : Type*} [CommRing R] {a b : R} (hab : a * b = -1)
    {n k : ℕ} (hk : k ≤ n) :
    (a ^ (n + k) - b ^ (n + k)) - (a ^ (n - k) - b ^ (n - k)) =
      (a ^ n + (-1) ^ k * b ^ n) * (a ^ k - (-1) ^ k * b ^ k) := by
  have hcross (u v : R) (huv : u * v = -1) :
      u ^ n * v ^ k * (-1) ^ k = u ^ (n - k) := by
    conv_lhs => rw [← Nat.sub_add_cancel hk, pow_add]
    calc
      _ = u ^ (n - k) * ((u * v) ^ k * (-1) ^ k) := by rw [mul_pow]; ring
      _ = _ := by rw [huv, ← mul_pow]; simp
  have hsign : ((-1 : R) ^ k) ^ 2 = 1 := by rw [← pow_mul, Nat.mul_comm, pow_mul]; simp
  calc
    _ = a ^ n * a ^ k - b ^ n * b ^ k -
        (a ^ n * b ^ k * (-1) ^ k - b ^ n * a ^ k * (-1) ^ k) := by
      rw [pow_add, pow_add, hcross a b hab, hcross b a (by rwa [mul_comm])]
    _ = a ^ n * a ^ k - ((-1) ^ k) ^ 2 * (b ^ n * b ^ k) -
        (a ^ n * b ^ k * (-1) ^ k - b ^ n * a ^ k * (-1) ^ k) := by rw [hsign, one_mul]
    _ = _ := by ring

open scoped QuadraticAlgebra

local notation "A" => QuadraticAlgebra ℤ[X] (1 : ℤ[X]) X
local notation "ι" => algebraMap ℤ[X] A
local notation "α" => (QuadraticAlgebra.omega : A)
local notation "β" => (ι X - α)

open FibonacciPolynomialBinet

-- The coefficient of the formal root in `(α - β) * ι p` is `2 * p`.
private theorem cancel_root_diff {p q : ℤ[X]} (h : (α - β) * ι p = (α - β) * ι q) : p = q := by
  have hc := congrArg QuadraticAlgebra.im h
  simp only [QuadraticAlgebra.im_mul, QuadraticAlgebra.im_sub, QuadraticAlgebra.im_omega,
    QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im, mul_zero, zero_add,
    sub_neg_eq_add, zero_sub, add_zero, one_add_one_eq_two] at hc
  have htwo : (2 : ℤ[X]) ≠ 0 := by
    rw [← Polynomial.C_ofNat, Polynomial.C_ne_zero]
    decide
  exact mul_left_cancel₀ htwo hc

private theorem root_diff_mul_discriminant (m r : ℕ) :
    (α - β) * ι ((X ^ 2 + 4) ^ m * 𝔣 r ^ (2 * m + 1)) =
      (α ^ r - β ^ r) ^ (2 * m + 1) := by
  rw [← fib_binet, mul_pow, pow_succ (α - β) (2 * m), pow_mul (α - β) 2 m, root_diff_sq,
    map_mul, map_pow, map_pow]
  ring

private theorem shifted_expansion {n k : ℕ} (hk : k ≤ n) (m : ℕ) :
    (α - β) * ι ((X ^ 2 + 4) ^ m * (𝔣 (n + k) ^ (2 * m + 1) - 𝔣 (n - k) ^ (2 * m + 1))) =
      ∑ j ∈ Finset.range (m + 1), ((2 * m + 1).choose j : A) * (-1) ^ ((n + k + 1) * j) *
        ((α ^ ((n + k) * (2 * m + 1 - 2 * j)) - β ^ ((n + k) * (2 * m + 1 - 2 * j))) -
          (α ^ ((n - k) * (2 * m + 1 - 2 * j)) - β ^ ((n - k) * (2 * m + 1 - 2 * j)))) := by
  have hsign : (-1 : A) ^ (n + k + 1) = (-1) ^ (n - k + 1) := by
    rw [show n + k + 1 = (n - k + 1) + 2 * k by omega, pow_add, pow_mul _ 2, neg_one_sq,
      one_pow, mul_one]
  rw [mul_sub, map_sub, mul_sub, root_diff_mul_discriminant, root_diff_mul_discriminant,
    root_sub_pow_odd root_mul_other, root_sub_pow_odd root_mul_other, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_mul _ (n + k + 1), pow_mul _ (n - k + 1), hsign, ← mul_sub]

private theorem neg_one_pow_mul_odd {R : Type*} [CommRing R] {k d : ℕ} (hd : Odd d) :
    (-1 : R) ^ (k * d) = (-1) ^ k := by
  rw [Nat.mul_comm, pow_mul, hd.neg_one_pow]

/-- **Odd powers of Fibonacci polynomials at $n \pm k$.** Let $f_i$ and $\ell_i$ be the
Fibonacci and Lucas polynomials in $\mathbb{Z}[x]$, defined by $f_0 = 0$, $f_1 = 1$, $\ell_0 = 2$,
$\ell_1 = x$ and $g_{i+2} = x g_{i+1} + g_i$ for $g = f, \ell$. Let $k \le n$ and $m$ be natural
numbers. In $\mathbb{Z}[x]$, if $k$ is odd then
$$
(x^2 + 4)^m \bigl(f_{n+k}^{2m+1} - f_{n-k}^{2m+1}\bigr) =
\sum_{j=0}^{m} \binom{2m+1}{j} (-1)^{nj} f_{n(2m+1-2j)} \ell_{k(2m+1-2j)},
$$
and if $k$ is even then
$$
(x^2 + 4)^m \bigl(f_{n+k}^{2m+1} - f_{n-k}^{2m+1}\bigr) =
\sum_{j=0}^{m} \binom{2m+1}{j} (-1)^{(n+1)j} \ell_{n(2m+1-2j)} f_{k(2m+1-2j)}.
$$

Source: Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
The Fibonacci Quarterly 62 (2024), Article linzhou02172024,
Lemma 4.1 (`fq-2024-linzhou02172024-lem-4.1`). -/
public theorem fibPoly_pow_odd_sub {n k : ℕ} (hk : k ≤ n) (m : ℕ) :
    (Odd k → (X ^ 2 + 4) ^ m * (𝔣 (n + k) ^ (2 * m + 1) - 𝔣 (n - k) ^ (2 * m + 1)) =
      ∑ j ∈ Finset.range (m + 1), ((2 * m + 1).choose j : ℤ[X]) * (-1) ^ (n * j) *
        𝔣 (n * (2 * m + 1 - 2 * j)) * 𝔩 (k * (2 * m + 1 - 2 * j))) ∧
    (Even k → (X ^ 2 + 4) ^ m * (𝔣 (n + k) ^ (2 * m + 1) - 𝔣 (n - k) ^ (2 * m + 1)) =
      ∑ j ∈ Finset.range (m + 1), ((2 * m + 1).choose j : ℤ[X]) * (-1) ^ ((n + 1) * j) *
        𝔩 (n * (2 * m + 1 - 2 * j)) * 𝔣 (k * (2 * m + 1 - 2 * j))) := by
  have hshift (j : ℕ) (hj : j ∈ Finset.range (m + 1)) :
      let d := 2 * m + 1 - 2 * j
      (α ^ ((n + k) * d) - β ^ ((n + k) * d)) - (α ^ ((n - k) * d) - β ^ ((n - k) * d)) =
        (α ^ (n * d) + (-1) ^ k * β ^ (n * d)) * (α ^ (k * d) - (-1) ^ k * β ^ (k * d)) := by
    have hj' := Finset.mem_range.mp hj
    let d := 2 * m + 1 - 2 * j
    have hd : Odd d := ⟨m - j, by dsimp [d]; omega⟩
    simpa only [← Nat.add_mul, ← Nat.sub_mul, neg_one_pow_mul_odd hd] using
      root_diff_shift root_mul_other (Nat.mul_le_mul_right d hk)
  constructor
  · intro hodd
    have hs : (-1 : A) ^ (n + k + 1) = (-1) ^ n := by
      rw [add_assoc, pow_add, pow_succ _ k, hodd.neg_one_pow, neg_one_mul, neg_neg, mul_one]
    apply cancel_root_diff
    rw [shifted_expansion hk, map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hshift j hj, pow_mul _ (n + k + 1), hs, ← pow_mul]
    simp only [map_mul, map_pow, map_natCast, map_neg, map_one, hodd.neg_one_pow,
      neg_one_mul, ← sub_eq_add_neg, sub_neg_eq_add]
    rw [← fib_binet, ← lucas_binet]
    ring
  · intro heven
    have hs : (-1 : A) ^ (n + k + 1) = (-1) ^ (n + 1) := by
      rw [add_right_comm, pow_add, heven.neg_one_pow, mul_one]
    apply cancel_root_diff
    rw [shifted_expansion hk, map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hshift j hj, pow_mul _ (n + k + 1), hs, ← pow_mul]
    simp only [map_mul, map_pow, map_natCast, map_neg, map_one, heven.neg_one_pow, one_mul]
    rw [← fib_binet, ← lucas_binet]
    ring

end MetaMathlibExt
