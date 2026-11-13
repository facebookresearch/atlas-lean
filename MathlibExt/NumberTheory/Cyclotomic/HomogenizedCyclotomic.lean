/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

/-!
# Homogenized cyclotomic values

`homogenizedCyclotomic n a b = ∑ᵢ cᵢ aⁱ b^(φ(n) - i)` for the integer coefficients `cᵢ` of the
`n`-th cyclotomic polynomial, i.e. `b ^ φ(n) Φ_n(a / b)` when `b ≠ 0`. It is the integer
`Φ_n(a, b)` in the factorization `aⁿ - bⁿ = ∏_{d ∣ n} Φ_d(a, b)` used by Zsigmondy-type
arguments (`MathlibExt.NumberTheory.BangZsigmondy`).

## Main definitions

* `MetaMathlibExt.homogenizedCyclotomic`
-/

@[expose] public section

namespace MetaMathlibExt

open Polynomial

/-- **Homogenized cyclotomic value.** For a natural number $n$ and integers $a, b$, let
$c_0, \dots, c_{\varphi(n)}$ be the integer coefficients of the $n$-th cyclotomic polynomial,
whose degree is $\varphi(n)$, where $\varphi$ is Euler's totient function. The homogenized
cyclotomic value is the integer
$$\Phi_n(a, b) = \sum_{i=0}^{\varphi(n)} c_i \, a^i \, b^{\varphi(n) - i}.$$

When $b \neq 0$ it equals $b^{\varphi(n)} \Phi_n(a/b)$, where $\Phi_n$ is the $n$-th cyclotomic
polynomial.

Source: Ömer Avcı, *Large Zsigmondy Primes*, INTEGERS 24 (2024), Article A62, Section 2
(notation `Φ_n(a, b)`, Lemma 3 and the explicit values in the proof of Theorem 1). -/
public noncomputable def homogenizedCyclotomic (n : ℕ) (a b : ℤ) : ℤ :=
  ∑ i ∈ Finset.range (Nat.totient n + 1),
    (cyclotomic n ℤ).coeff i * a ^ i * b ^ (Nat.totient n - i)

/-- **Homogenized cyclotomic value of index one.** For all integers $a$ and $b$, the
homogenized cyclotomic value $\Phi_1(a, b)$ equals $a - b$.

Source: Ömer Avcı, *Large Zsigmondy Primes*, INTEGERS 24 (2024), Article A62, Lemma 3 (v)
(the case `n = 1`). -/
public theorem homogenizedCyclotomic_one (a b : ℤ) : homogenizedCyclotomic 1 a b = a - b := by
  simp [homogenizedCyclotomic, cyclotomic_one, Finset.sum_range_succ, coeff_X, coeff_one]
  ring

/-- **Homogenized cyclotomic value of index two.** For all integers $a$ and $b$, the
homogenized cyclotomic value $\Phi_2(a, b)$ equals $a + b$.

Source: Ömer Avcı, *Large Zsigmondy Primes*, INTEGERS 24 (2024), Article A62, Lemma 3 (v)
(the case `n = 2`). -/
public theorem homogenizedCyclotomic_two (a b : ℤ) : homogenizedCyclotomic 2 a b = a + b := by
  simp [homogenizedCyclotomic, cyclotomic_two, Finset.sum_range_succ, coeff_X, coeff_one]
  ring

/-- **Homogenized cyclotomic value with second argument one.** For every natural number $n$
and every integer $a$, the homogenized cyclotomic value $\Phi_n(a, 1)$ equals $\Phi_n(a)$, the
value at $a$ of the $n$-th cyclotomic polynomial with integer coefficients.

Source: Ömer Avcı, *Large Zsigmondy Primes*, INTEGERS 24 (2024), Article A62, Section 2
(notation `Φ_n(a, b)`). -/
public theorem homogenizedCyclotomic_one_right (n : ℕ) (a : ℤ) :
    homogenizedCyclotomic n a 1 = (cyclotomic n ℤ).eval a := by
  rw [homogenizedCyclotomic, eval_eq_sum_range, natDegree_cyclotomic]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [one_pow, mul_one]

/-- **Homogenized cyclotomic value in a field.** Let $K$ be a field, $n$ a natural number and
$a, b$ integers such that the image of $b$ in $K$ is nonzero. Then the image in $K$ of the
homogenized cyclotomic value $\Phi_n(a, b)$ equals $b^{\varphi(n)} \Phi_n(a/b)$, where $\Phi_n$
is the $n$-th cyclotomic polynomial over $K$, $\varphi$ is Euler's totient function, and $b$
and $a/b$ are computed in $K$.

Source: Ömer Avcı, *Large Zsigmondy Primes*, INTEGERS 24 (2024), Article A62, Section 2
(notation `Φ_n(a, b)`). -/
public theorem homogenizedCyclotomic_cast {K : Type*} [Field K] (n : ℕ) (a b : ℤ)
    (hb : (b : K) ≠ 0) :
    ((homogenizedCyclotomic n a b : ℤ) : K) =
      (b : K) ^ Nat.totient n * (cyclotomic n K).eval ((a : K) / (b : K)) := by
  rw [homogenizedCyclotomic, Int.cast_sum, eval_eq_sum_range, natDegree_cyclotomic,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hle : i ≤ Nat.totient n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hcoeff : (cyclotomic n K).coeff i = (((cyclotomic n ℤ).coeff i : ℤ) : K) := by
    rw [← map_cyclotomic n (Int.castRingHom K), coeff_map]
    rfl
  rw [hcoeff, div_pow]
  push_cast
  rw [pow_sub₀ _ hb hle, div_eq_mul_inv]
  ring

end MetaMathlibExt
