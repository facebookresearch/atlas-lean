/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.RingTheory.PowerSeries.Inverse
public import MathlibExt.Combinatorics.Enumerative.Partition.QEulerProduct

/-!
# Congruences for generalized cubic partitions modulo primes

Statements from Russelle Guadalupe, *A Note on Congruences for Generalized Cubic Partitions
Modulo Primes*, INTEGERS 25 (2025), Article A20.

A generalized cubic partition of `n` (Amdeberhan, Sellers, and Singh) is a partition of `n`
whose even parts may appear in `c ≥ 1` colors; `a_c(n)` counts them, with
`∑ a_c(n) qⁿ = 1/(f_1 f_2^{c-1})`, where `f_k = (q^k; q^k)_∞` is `qEulerProduct k`, written
`𝔣 k` below. We define `a_c(n)` as the `n`th coefficient of that quotient in `ℤ⟦X⟧` (the
denominator has constant coefficient `1`, so it is a unit). `c = 1` gives the partition
function and `c = 2` Chan's cubic partitions.
-/

open PowerSeries

namespace MetaMathlibExt

@[expose] public section

local notation "𝔣" => qEulerProduct

/-- **Generating function of generalized cubic partitions.** Let
$f_k = \prod_{m \ge 1} (1 - q^{km})$ be the Euler products. For a natural number $c$, this is
the integer power series $1/(f_1 f_2^{c-1})$ in $q$, the inverse of $f_1 f_2^{c-1}$ (whose
constant term is $1$). For $c \ge 1$ its coefficient of $q^n$ is the number of partitions of
$n$ whose even parts may each come in $c$ colors. For $c = 0$ the exponent $c - 1$ is
truncated to $0$, so the series is then the inverse of $f_1$.

Source: Russelle Guadalupe, *A Note on Congruences for Generalized Cubic Partitions Modulo
Primes*, INTEGERS 25 (2025), Article A20, Section 1. -/
public noncomputable def generalizedCubicPartitionSeries (c : ℕ) : ℤ⟦X⟧ :=
  invOfUnit (𝔣 1 * 𝔣 2 ^ (c - 1)) 1

/-- **Generalized cubic partition numbers.** Let $f_k = \prod_{m \ge 1} (1 - q^{km})$ be the
Euler products. For natural numbers $c$ and $n$, $a_c(n)$ is the integer coefficient of $q^n$
in the generating function of generalized cubic partitions, the power series
$1/(f_1 f_2^{c-1})$. For $c \ge 1$ it is the number of partitions of $n$ whose even parts may
each come in $c$ colors; $c = 1$ gives the partition numbers and $c = 2$ Chan's cubic
partition numbers. For $c = 0$ the exponent $c - 1$ is truncated to $0$, so $a_0(n)$ is also
the number of partitions of $n$.

Source: Russelle Guadalupe, *A Note on Congruences for Generalized Cubic Partitions Modulo
Primes*, INTEGERS 25 (2025), Article A20, Section 1. -/
public noncomputable def generalizedCubicPartitionCount (c n : ℕ) : ℤ :=
  coeff n (generalizedCubicPartitionSeries c)

/-- **Generating function identity for generalized cubic partition numbers.** Let
$f_k = \prod_{m \ge 1} (1 - q^{km})$ be the Euler products and $a_c(n)$ the generalized cubic
partition numbers. For every natural number $c$,
$f_1 f_2^{c-1} \sum_{n \ge 0} a_c(n) q^n = 1$ as integer power series in $q$, where for
$c = 0$ the exponent $c - 1$ is truncated to $0$.

Source: Russelle Guadalupe, *A Note on Congruences for Generalized Cubic Partitions Modulo
Primes*, INTEGERS 25 (2025), Article A20, Section 1. -/
public theorem generalizedCubicPartitionCount_generatingFunction (c : ℕ) :
    𝔣 1 * 𝔣 2 ^ (c - 1) * PowerSeries.mk (generalizedCubicPartitionCount c) = 1 := by
  have hmk : PowerSeries.mk (generalizedCubicPartitionCount c) =
      generalizedCubicPartitionSeries c := by
    ext n
    simp [generalizedCubicPartitionCount]
  have hc : constantCoeff (𝔣 1 * 𝔣 2 ^ (c - 1)) = ((1 : ℤˣ) : ℤ) := by
    simp [constantCoeff_qEulerProduct (le_refl 1),
      constantCoeff_qEulerProduct (by norm_num : 1 ≤ 2)]
  rw [hmk, generalizedCubicPartitionSeries, mul_invOfUnit _ _ hc]

/-- **Generalized cubic partitions of zero.** For every natural number $c$, the generalized
cubic partition number $a_c(0)$ equals $1$.

Source: Russelle Guadalupe, *A Note on Congruences for Generalized Cubic Partitions Modulo
Primes*, INTEGERS 25 (2025), Article A20, Section 1. -/
public theorem generalizedCubicPartitionCount_zero (c : ℕ) :
    generalizedCubicPartitionCount c 0 = 1 := by
  have h := congrArg (coeff 0) (generalizedCubicPartitionCount_generatingFunction c)
  simp only [coeff_zero_eq_constantCoeff, map_mul, map_pow,
    constantCoeff_qEulerProduct (le_refl 1), constantCoeff_qEulerProduct (by norm_num : 1 ≤ 2),
    one_pow, one_mul, map_one] at h
  simpa using h

/-- **Amdeberhan–Sellers–Singh congruences.** For every natural number $n$, the generalized
cubic partition numbers satisfy $a_3(7n + 4) \equiv 0 \pmod{7}$ and
$a_5(11n + 10) \equiv 0 \pmod{11}$.

Source: Russelle Guadalupe, *A Note on Congruences for Generalized Cubic Partitions Modulo
Primes*, INTEGERS 25 (2025), Article A20, Theorem 1 (quoting Amdeberhan, Sellers, and
Singh), Equations (1) and (2). -/
public theorem_wanted generalizedCubicPartitionCount_seven_eleven (n : ℕ) :
    (7 : ℤ) ∣ generalizedCubicPartitionCount 3 (7 * n + 4) ∧
      (11 : ℤ) ∣ generalizedCubicPartitionCount 5 (11 * n + 10)

/-- **Generalized cubic partition congruences for primes $p \equiv 5, 7 \pmod 8$.** Let $a_c(n)$
be the generalized cubic partition numbers, let $p$ be a prime with $p \equiv 5$ or
$p \equiv 7 \pmod 8$, and let $l$ be a natural number with $p \mid 8l + 3$. Then
$a_{p-4}(pn + l) \equiv 0 \pmod p$ for every natural number $n$.

The source assumes $0 \le l \le p - 1$; the statement for a larger $l$ follows from the one for
$l \bmod p$, which satisfies the same divisibility.

Source: Russelle Guadalupe, *A Note on Congruences for Generalized Cubic Partitions Modulo
Primes*, INTEGERS 25 (2025), Article A20, Theorem 2, Equation (9). -/
public theorem_wanted generalizedCubicPartitionCount_prime_five_seven_mod_eight {p : ℕ}
    (hp : p.Prime) (hp8 : p % 8 = 5 ∨ p % 8 = 7) {l : ℕ} (hdvd : p ∣ 8 * l + 3) (n : ℕ) :
    (p : ℤ) ∣ generalizedCubicPartitionCount (p - 4) (p * n + l)

/-- **Generalized cubic partition congruences modulo primes $p \ge 7$, $p \equiv 3, 7 \pmod 8$.**
Let $a_c(n)$ be the generalized cubic partition numbers and let $p \ge 7$ be a prime with
$p \equiv 3$ or $p \equiv 7 \pmod 8$. Then
$a_{p-6}\bigl(pn + 13(p^2 - 1)/24\bigr) \equiv 0 \pmod p$ for every natural number $n$.

Since $24 \mid p^2 - 1$, the shift $13(p^2 - 1)/24$ is a natural number.

Source: Russelle Guadalupe, *A Note on Congruences for Generalized Cubic Partitions Modulo
Primes*, INTEGERS 25 (2025), Article A20, Theorem 3, Equation (13). -/
public theorem_wanted generalizedCubicPartitionCount_prime_three_seven_mod_eight {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hp8 : p % 8 = 3 ∨ p % 8 = 7) (n : ℕ) :
    (p : ℤ) ∣ generalizedCubicPartitionCount (p - 6) (p * n + 13 * (p ^ 2 - 1) / 24)

end

end MetaMathlibExt
