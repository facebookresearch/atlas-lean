/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.Data.Int.Interval
public import MathlibExt.Combinatorics.Enumerative.Partition.KTupleRegularPartitions
public import MathlibExt.Combinatorics.Enumerative.Partition.QEulerProductCongruence
public import MathlibExt.Combinatorics.Enumerative.Partition.SignedEulerProduct
import Mathlib

namespace MetaMathlibExt

@[expose] public section

/--
**Bounded bilateral series.** Given functions $e, w : \mathbb{Z} \to \mathbb{Z}$, the
bounded bilateral series of $e$ and $w$ is the power series over $\mathbb{Z}$ whose
coefficient of $q^n$, for each natural number $n$, is the sum of $w(m)$ over the integers
$m$ with $-n-1 \le m \le n+1$ and $e(m) = n$.

It agrees with the bilateral series $\sum_{m \in \mathbb{Z}} w(m) q^{e(m)}$ whenever $e$
takes no negative values and, for every natural number $n$, every integer $m$ with $e(m) = n$
satisfies $|m| \le n + 1$, as holds for the quadratic exponents used in Lemmas 1, 3 and 5 of
the source; it is not intended for other exponents.

Source: Bishnu Paudel, James A. Sellers, and Haiyang Wang, *Extending Recent Work of Nath, Saikia,
and Sarma on k-Tuple ℓ-Regular Partitions*, INTEGERS 26 (2026), Article A4, Encoding for Lemmas 1,
3, and 5.
-/
public def boundedBilateralSeries (exponent weight : ℤ → ℤ) : PowerSeries ℤ :=
  PowerSeries.mk fun n =>
    ∑ m ∈ Finset.Icc (-(n : ℤ) - 1) ((n : ℤ) + 1),
      if exponent m = (n : ℤ) then weight m else 0

/--
**Coefficients of the bounded bilateral series.** For all functions
$e, w : \mathbb{Z} \to \mathbb{Z}$ and every natural number $n$, the coefficient of $q^n$ in
the bounded bilateral series of $e$ and $w$ equals the sum of $w(m)$ over the integers $m$
with $-n-1 \le m \le n+1$ and $e(m) = n$.

Source: Bishnu Paudel, James A. Sellers, and Haiyang Wang, *Extending Recent Work of Nath, Saikia,
and Sarma on k-Tuple ℓ-Regular Partitions*, INTEGERS 26 (2026), Article A4, Encoding for Lemmas 1,
3, and 5.
-/
public theorem coeff_boundedBilateralSeries (exponent weight : ℤ → ℤ) (n : ℕ) :
    PowerSeries.coeff n (boundedBilateralSeries exponent weight) =
      ∑ m ∈ Finset.Icc (-(n : ℤ) - 1) ((n : ℤ) + 1),
        if exponent m = (n : ℤ) then weight m else 0 := by
  simp [boundedBilateralSeries]

/--
**Truncated one-sided series.** For functions $e : \mathbb{N} \to \mathbb{N}$ and
$w : \mathbb{N} \to \mathbb{Z}$, this is the integer power series whose coefficient of $q^n$ is
the sum of $w(m)$ over the integers $m$ with $1 \le m \le n$ and $e(m) = n$.

When $e(m) \ge m$ for every $m \ge 1$, as for the square exponents in Lemma 5 and
Corollary 3, this series is $\sum_{m \ge 1} w(m) q^{e(m)}$.

Source: Bishnu Paudel, James A. Sellers, and Haiyang Wang, *Extending Recent Work of Nath, Saikia,
and Sarma on k-Tuple ℓ-Regular Partitions*, INTEGERS 26 (2026), Article A4, Encoding for Lemma 5
and Corollary 3.
-/
public def positiveUnilateralSeries (exponent : ℕ → ℕ) (weight : ℕ → ℤ) : PowerSeries ℤ :=
  PowerSeries.mk fun n =>
    ∑ m ∈ Finset.Icc 1 n, if exponent m = n then weight m else 0

/--
**Coefficients of the positive unilateral series.** For all functions
$e : \mathbb{N} \to \mathbb{N}$ and $w : \mathbb{N} \to \mathbb{Z}$ and every natural number
$n$, the coefficient of $q^n$ in the positive unilateral series of $e$ and $w$ equals the sum
of $w(m)$ over the natural numbers $m$ with $1 \le m \le n$ and $e(m) = n$.

Source: Bishnu Paudel, James A. Sellers, and Haiyang Wang, *Extending Recent Work of Nath, Saikia,
and Sarma on k-Tuple ℓ-Regular Partitions*, INTEGERS 26 (2026), Article A4, Encoding for Lemma 5
and Corollary 3.
-/
public theorem coeff_positiveUnilateralSeries (exponent : ℕ → ℕ) (weight : ℕ → ℤ) (n : ℕ) :
    PowerSeries.coeff n (positiveUnilateralSeries exponent weight) =
      ∑ m ∈ Finset.Icc 1 n, if exponent m = n then weight m else 0 := by
  simp [positiveUnilateralSeries]

/--
**Congruences modulo 24 for triples of 2-regular partitions.** Let $T_2(n)$ be the number of
triples of 2-regular partitions (partitions with no even part) whose sizes add up to $n$. If
$t$ is a positive integer with $\gcd(t, 6) = 1$ and $N \in \{33, 57\}$, then for every natural
number $n$,
$$T_2\left(9n + \frac{N t^2 - 1}{8}\right) \equiv 0 \pmod{24}.$$
Here $N t^2 - 1$ is divisible by $8$, so the fraction is an integer.

Source: Bishnu Paudel, James A. Sellers, and Haiyang Wang, *Extending Recent Work of Nath, Saikia,
and Sarma on k-Tuple ℓ-Regular Partitions*, INTEGERS 26 (2026), Article A4, Theorem 1, equation
T29n24.
-/
public theorem_wanted tripleTwo_mod_twentyFour (t n N : ℕ) (ht : 0 < t)
    (hcoprime : Nat.gcd t 6 = 1) (hN : N = 33 ∨ N = 57) :
    Nat.ModEq 24 (tripleRegularPartitionCount 2 (9 * n + (N * t ^ 2 - 1) / 8)) 0

/--
**The Nath–Saikia–Sarma conjecture.** Let $T_2(n)$ be the number of triples of 2-regular
partitions (partitions with no even part) whose sizes add up to $n$. Let $p \ge 5$ be a prime
with Legendre symbol $\left(\frac{-2}{p}\right) = -1$, and let $t$ be a positive integer with
$\gcd(t, 6) = 1$ and $p \mid t$. Then for every natural number $n$ and every $j$ with
$1 \le j \le p - 1$,
$$T_2\left(9t^2 n + \frac{9t^2 j}{p} + \frac{57t^2 - 1}{8}\right) \equiv 0 \pmod{6}.$$
Both fractions are integers under these hypotheses.

Source: Bishnu Paudel, James A. Sellers, and Haiyang Wang, *Extending Recent Work of Nath, Saikia,
and Sarma on k-Tuple ℓ-Regular Partitions*, INTEGERS 26 (2026), Article A4, Corollary 1
(Conjecture conj.nss).
-/
public theorem_wanted nathSaikiaSarma_conjecture (p t n j : ℕ) [Fact (Nat.Prime p)]
    (hp : 5 ≤ p) (hlegendre : legendreSym p (-2) = -1) (ht : 0 < t)
    (hcoprime : Nat.gcd t 6 = 1) (hpt : p ∣ t) (hj₁ : 1 ≤ j) (hjp : j ≤ p - 1) :
    Nat.ModEq 6
      (tripleRegularPartitionCount 2
        (9 * t ^ 2 * n + 9 * t ^ 2 * j / p + (57 * t ^ 2 - 1) / 8)) 0

/--
**Congruences modulo 8 and 24 for triples of 2-regular partitions.** Let $T_2(n)$ be the
number of triples of $2$-regular partitions (partitions with no even part) whose sizes add up to
$n$. Let $p$ be a prime with $p \equiv 3$, $5$ or $7 \pmod 8$, and let $n$ and $\alpha$ be
natural numbers with $p \nmid n$. Then
$$T_2\left(p^{2\alpha+1} n + \frac{p^{2\alpha+2}-1}{8}\right) \equiv 0 \pmod 8,$$
and if moreover $3 \nmid n$, this value is also $\equiv 0 \pmod{24}$.

The division by $8$ is exact because $p$ is odd.

Source: Bishnu Paudel, James A. Sellers, and Haiyang Wang, *Extending Recent Work of Nath, Saikia,
and Sarma on k-Tuple ℓ-Regular Partitions*, INTEGERS 26 (2026), Article A4, Theorem 2, equations
thm.p357mod8 and mod24.
-/
public theorem_wanted tripleTwo_primePower_mod_eight_and_twentyFour (p n α : ℕ)
    (hp : Nat.Prime p) (hres : p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7) (hpn : ¬ p ∣ n) :
    let index := p ^ (2 * α + 1) * n + (p ^ (2 * α + 2) - 1) / 8
    Nat.ModEq 8 (tripleRegularPartitionCount 2 index) 0 ∧
      (¬ 3 ∣ n → Nat.ModEq 24 (tripleRegularPartitionCount 2 index) 0)

/--
**Prime-power congruences modulo 24 for triples of 2-regular partitions.** Let $T_2(n)$ be
the number of triples of 2-regular partitions (partitions with no even part) whose sizes add up
to $n$. Let $p \ne 3$ be a prime with $p \equiv 3$, $5$ or $7 \pmod 8$. Then for all natural
numbers $n$ and $\alpha$ with $p \nmid n$,
$$T_2\left(9 p^{2\alpha+1} n + \frac{9 p^{2\alpha+2} - 1}{8}\right) \equiv 0 \pmod{24}.$$
Since $p$ is odd, the fraction is an integer.

Source: Bishnu Paudel, James A. Sellers, and Haiyang Wang, *Extending Recent Work of Nath, Saikia,
and Sarma on k-Tuple ℓ-Regular Partitions*, INTEGERS 26 (2026), Article A4, Corollary 2, equation
cor.9pmod24.
-/
public theorem_wanted tripleTwo_nine_primePower_mod_twentyFour (p n α : ℕ)
    (hp : Nat.Prime p) (hres : p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7)
    (hp3 : p ≠ 3) (hpn : ¬ p ∣ n) :
    Nat.ModEq 24
      (tripleRegularPartitionCount 2
        (9 * p ^ (2 * α + 1) * n + (9 * p ^ (2 * α + 2) - 1) / 8)) 0

/--
**A fifth-power Euler product identity.** Write $f_k = \prod_{i \ge 1} (1 - q^{ki})$ for the
Euler products, as integer power series in $q$. Then
$$f_1^5 = f_2^2 \sum_{m \in \mathbb{Z}} (6m + 1)\, q^{m(3m+1)/2}.$$
This is the identity $f_1^5 / f_2^2 = \sum_{m \in \mathbb{Z}} (6m + 1)\, q^{m(3m+1)/2}$ with the
denominator cleared. The coefficient of $q^n$ in the sum is computed over the integers $m$ with
$|m| \le n + 1$, which include every solution of $m(3m+1)/2 = n$.

Source: Bishnu Paudel, James A. Sellers, and Haiyang Wang, *Extending Recent Work of Nath, Saikia,
and Sarma on k-Tuple ℓ-Regular Partitions*, INTEGERS 26 (2026), Article A4, Lemma 3, equation
f15/f22.
-/
public theorem_wanted qEulerProduct_fifth_power_identity :
    qEulerProduct 1 ^ 5 = qEulerProduct 2 ^ 2 * boundedBilateralSeries
      (fun m => m * (3 * m + 1) / 2) (fun m => 6 * m + 1)

/--
**Gauss's theta identity for the Euler products.** Write $f_k = \prod_{i \ge 1} (1 - q^{ki})$
for the Euler products, as integer power series in $q$, and let
$\theta = \sum_{m \in \mathbb{Z}} (-1)^m q^{m^2}$. Then $f_1^2 = f_2\, \theta$ and
$\theta = 1 + 2 \sum_{m \ge 1} (-1)^m q^{m^2}$.

The coefficient of $q^n$ in each sum is computed over the indices $m$ with $|m| \le n + 1$
(respectively $1 \le m \le n$), which include every solution of $m^2 = n$.

Source: Bishnu Paudel, James A. Sellers, and Haiyang Wang, *Extending Recent Work of Nath, Saikia,
and Sarma on k-Tuple ℓ-Regular Partitions*, INTEGERS 26 (2026), Article A4, Lemma 5, equation
f12/f2.
-/
public theorem_wanted qEulerProduct_square_theta_identity :
    let theta := boundedBilateralSeries (fun m => m ^ 2) (fun m => (-1 : ℤ) ^ m.natAbs)
    qEulerProduct 1 ^ 2 = qEulerProduct 2 * theta ∧
      theta = 1 + 2 * positiveUnilateralSeries (fun m => m ^ 2) (fun m => (-1 : ℤ) ^ m)

/--
**The theta identity for the second Euler product.** Write
$f_k = \prod_{i \ge 1} (1 - q^{ki})$ for the Euler products, as integer power series in $q$. Then
$$f_2^2 = f_4 \left(1 + 2 \sum_{n \ge 1} (-1)^n q^{2n^2}\right).$$
This is the identity for $f_2^2 / f_4$ with the denominator cleared.

Source: Bishnu Paudel, James A. Sellers, and Haiyang Wang, *Extending Recent Work of Nath, Saikia,
and Sarma on k-Tuple ℓ-Regular Partitions*, INTEGERS 26 (2026), Article A4, Corollary 3, equation
f22/f4.
-/
public theorem_wanted qEulerProduct_two_square_identity :
    qEulerProduct 2 ^ 2 = qEulerProduct 4 *
      (1 + 2 * positiveUnilateralSeries (fun n => 2 * n ^ 2) (fun n => (-1 : ℤ) ^ n))

/--
**Prime-power congruences for $k$-tuples of $\ell$-regular partitions.** Write $T_{\ell,k}(n)$
for the number of $k$-tuples of $\ell$-regular partitions with total $n$. Let $p$ be a prime,
let $m$, $\ell$ and $s$ be positive integers, let $\alpha \ge s$ and $r$ be natural numbers
with $1 \le r \le p^s - 1$. Then for every natural number $n$,
$$T_{\ell,p^\alpha m}(p^s n + r) \equiv 0 \pmod{p^{\alpha - s + 1}}.$$

Since $s$ is positive, the hypothesis $\alpha \ge s$ also gives $\alpha \ge 1$.

Source: Bishnu Paudel, James A. Sellers, and Haiyang Wang, *Extending Recent Work of Nath, Saikia,
and Sarma on k-Tuple ℓ-Regular Partitions*, INTEGERS 26 (2026), Article A4, Theorem 3, equation
thm.gen1.1.
-/
public theorem_wanted kTupleRegularPartition_primePower_congruent (p m ℓ α s r n : ℕ)
    (hp : Nat.Prime p) (hm : 0 < m) (hℓ : 0 < ℓ) (hs : 0 < s) (hsα : s ≤ α) (hr₁ : 1 ≤ r) (hrp : r ≤
        p ^ s - 1) :
    Nat.ModEq (p ^ (α - s + 1))
      (kTupleRegularPartitionCount ℓ (p ^ α * m) (p ^ s * n + r)) 0

end

end MetaMathlibExt
