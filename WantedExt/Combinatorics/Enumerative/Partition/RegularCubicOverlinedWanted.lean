/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse
public import MathlibExt.Combinatorics.Enumerative.Partition.QEulerProduct

/-!
# Congruences for `ℓ`-regular cubic partitions with odd parts overlined (statements)

Statements from Pujashree Buragohain and Nipen Saikia, *Some New Congruences for l-Regular
Cubic Partitions with Odd Parts Overlined*, INTEGERS 24 (2024), Article A101.

Naika and Harishkumar's `a_ℓ(n)` counts the `ℓ`-regular cubic partitions of `n` in which the
first occurrence of each distinct odd part may be overlined; for `ℓ > 2` its generating
function is `∑ a_ℓ(n) qⁿ = f_2 f_ℓ² f_{4ℓ} / (f_1² f_4 f_{2ℓ})` (paper, eq. (2)), where
`f_k = (q^k; q^k)_∞` is `qEulerProduct k`, written `𝔣 k` below. We define `a_ℓ(n)` as the
`n`th coefficient of that quotient in `ℤ⟦X⟧` (the denominator has constant coefficient `1`).
Ramanujan's `ψ(q^k) = f_{2k}² / f_k` (paper, eq. (3)); congruences between power series are
stated coefficientwise, with a unit denominator `f_k` cleared by multiplying both sides
(this preserves congruences, since `f_k` and its inverse have integer coefficients).

Already stated elsewhere in this library: Lemma 1 (Cui–Gu `p`-dissection of `f_1`, with the
non-congruence) is `eulerProduct_p_dissection`; Lemma 2 (`p`-dissection of `ψ`) is
`ramanujanPsi_prime_dissection`; Lemma 4 is the case `k = 1` of
`qEulerProduct_pow_prime_pow_congruence`. Of Lemma 3, identities (5), (6), (7), (8), (11),
(12), (15) are `one_div_f1_sq_two_dissection`, the first conjunct of
`one_div_f1_pow_four_eight_twelve_two_dissection`, `f1_sq_two_dissection`,
`f2_sq_div_f1_dissection`, `f3_div_f1_cube_two_dissection`, `f4_div_f1_dissection` and
`f9_div_f1_two_dissection`; the remaining (9), (10), (13), (14) are
`f3_f5_quotients_two_dissection` below.
-/

open PowerSeries

namespace MetaMathlibExt

@[expose] public section

local notation "𝔣" => qEulerProduct

/-- **Generating function of ℓ-regular cubic partitions with odd parts overlined.** For a natural
number $\ell$, this is the integer power series
$$\frac{f_2 f_\ell^2 f_{4\ell}}{f_1^2 f_4 f_{2\ell}}, \qquad f_k = \prod_{m \ge 1} (1 - q^{km}).$$
It is meaningful for $\ell \ge 1$, where the denominator has constant term $1$ and so is
invertible. For $\ell > 2$, the range the paper considers, its coefficient of $q^n$ is the number
of $\ell$-regular cubic partitions of $n$ with odd parts overlined.

Source: Pujashree Buragohain and Nipen Saikia, *Some New Congruences for l-Regular Cubic
Partitions with Odd Parts Overlined*, INTEGERS 24 (2024), Article A101, Section 1, eq. (2). -/
public noncomputable def regularCubicOverlinedSeries (l : ℕ) : ℤ⟦X⟧ :=
  𝔣 2 * 𝔣 l ^ 2 * 𝔣 (4 * l) * invOfUnit (𝔣 1 ^ 2 * 𝔣 4 * 𝔣 (2 * l)) 1

/-- **ℓ-regular cubic partitions with odd parts overlined.** For natural numbers $\ell$ and $n$,
$a_\ell(n)$ is the coefficient of $q^n$ in the integer power series
$$\frac{f_2 f_\ell^2 f_{4\ell}}{f_1^2 f_4 f_{2\ell}}, \qquad f_k = \prod_{m \ge 1} (1 - q^{km}).$$
The quotient is meaningful for $\ell \ge 1$, where the denominator has constant term $1$. For
$\ell > 2$, the range the paper considers, $a_\ell(n)$ is the number of $\ell$-regular cubic
partitions of $n$ in which the first occurrence of each distinct odd part may be overlined; for
example, $a_3(5) = 18$.

Source: Pujashree Buragohain and Nipen Saikia, *Some New Congruences for l-Regular Cubic
Partitions with Odd Parts Overlined*, INTEGERS 24 (2024), Article A101, Section 1, eq. (2). -/
public noncomputable def regularCubicOverlinedCount (l n : ℕ) : ℤ :=
  coeff n (regularCubicOverlinedSeries l)

/-- **Generating function for $\ell$-regular cubic partitions with odd parts overlined.** Let
$\ell \ge 1$, write $f_k = \prod_{m \ge 1} (1 - q^{km})$ for the Euler products in the ring of
integer power series in $q$, and let $a_\ell(n)$ be the $n$th coefficient of
$f_2 f_\ell^2 f_{4\ell} / (f_1^2 f_4 f_{2\ell})$ (the denominator has constant term $1$, so it
is invertible). Then
$$
f_1^2 f_4 f_{2\ell} \sum_{n \ge 0} a_\ell(n) q^n = f_2 f_\ell^2 f_{4\ell}.
$$

For $\ell > 2$ the paper identifies $a_\ell(n)$ with the number of $\ell$-regular cubic
partitions of $n$ with odd parts overlined.

Source: Pujashree Buragohain and Nipen Saikia, *Some New Congruences for l-Regular Cubic
Partitions with Odd Parts Overlined*, INTEGERS 24 (2024), Article A101, Section 1, eq. (2). -/
public theorem regularCubicOverlinedCount_generatingFunction {l : ℕ} (hl : 1 ≤ l) :
    𝔣 1 ^ 2 * 𝔣 4 * 𝔣 (2 * l) * PowerSeries.mk (regularCubicOverlinedCount l) =
      𝔣 2 * 𝔣 l ^ 2 * 𝔣 (4 * l) := by
  have hmk : PowerSeries.mk (regularCubicOverlinedCount l) = regularCubicOverlinedSeries l := by
    ext n
    simp [regularCubicOverlinedCount]
  have hc : constantCoeff (𝔣 1 ^ 2 * 𝔣 4 * 𝔣 (2 * l)) = ((1 : ℤˣ) : ℤ) := by
    simp [constantCoeff_qEulerProduct (le_refl 1),
      constantCoeff_qEulerProduct (by norm_num : 1 ≤ 4),
      constantCoeff_qEulerProduct (by omega : 1 ≤ 2 * l)]
  rw [hmk, regularCubicOverlinedSeries, mul_comm, mul_assoc, invOfUnit_mul _ _ hc, mul_one]

/-- **Constant term of the overlined ℓ-regular cubic partition numbers.** For every natural number
$\ell \ge 1$, the coefficient $a_\ell(0)$ of $q^0$ in the generating function of $\ell$-regular
cubic partitions with odd parts overlined equals $1$.

Source: Pujashree Buragohain and Nipen Saikia, *Some New Congruences for l-Regular Cubic
Partitions with Odd Parts Overlined*, INTEGERS 24 (2024), Article A101, Section 1, eq. (2). -/
public theorem regularCubicOverlinedCount_zero {l : ℕ} (hl : 1 ≤ l) :
    regularCubicOverlinedCount l 0 = 1 := by
  have h := congrArg (coeff 0) (regularCubicOverlinedCount_generatingFunction hl)
  simp only [coeff_zero_eq_constantCoeff, map_mul, map_pow,
    constantCoeff_qEulerProduct (le_refl 1), constantCoeff_qEulerProduct (by norm_num : 1 ≤ 2),
    constantCoeff_qEulerProduct (by norm_num : 1 ≤ 4), constantCoeff_qEulerProduct hl,
    constantCoeff_qEulerProduct (by omega : 1 ≤ 2 * l),
    constantCoeff_qEulerProduct (by omega : 1 ≤ 4 * l), one_pow, one_mul, mul_one] at h
  simpa using h

/-- **Four 2-dissections of quotients of Euler products.** Write
$f_k = \prod_{m \ge 1} (1 - q^{km})$ for the Euler products in the ring of integer power series
in $q$. Then
$$
f_3 f_2^2 f_8 f_{12} f_{16} f_{24} f_{48} =
f_1 \left(f_4 f_6 f_{16}^2 f_{24}^3 + q f_6 f_8^3 f_{12} f_{48}^2\right),
$$
$$
f_1^3 f_4 f_6^2 f_{12} = f_3 \left(f_4^4 f_6^2 - 3 q f_2^2 f_{12}^4\right),
$$
$$
f_5 f_2^3 f_8 f_{20} f_{40} = f_1 \left(f_2 f_8^2 f_{20}^3 + q f_4^3 f_{10} f_{40}^2\right),
$$
$$
f_1 f_4 f_8 f_{10}^3 f_{40} = f_5 \left(f_2 f_8^2 f_{20}^3 - q f_4^3 f_{10} f_{40}^2\right).
$$

These are the 2-dissections of $f_3 / f_1$, $f_1^3 / f_3$, $f_5 / f_1$ and $f_1 / f_5$ with the
denominators cleared; for example, the first is
$f_3 / f_1 = \frac{f_4 f_6 f_{16} f_{24}^2}{f_2^2 f_8 f_{12} f_{48}} +
q \frac{f_6 f_8^2 f_{48}}{f_2^2 f_{16} f_{24}}$ multiplied by
$f_1 f_2^2 f_8 f_{12} f_{16} f_{24} f_{48}$.

Source: Pujashree Buragohain and Nipen Saikia, *Some New Congruences for l-Regular Cubic
Partitions with Odd Parts Overlined*, INTEGERS 24 (2024), Article A101, Lemma 3, eqs. (9),
(10), (13), (14) (`integers-2024-A101-lem-3`). -/
public theorem_wanted f3_f5_quotients_two_dissection :
    𝔣 3 * 𝔣 2 ^ 2 * 𝔣 8 * 𝔣 12 * 𝔣 16 * 𝔣 24 * 𝔣 48 =
        𝔣 1 * (𝔣 4 * 𝔣 6 * 𝔣 16 ^ 2 * 𝔣 24 ^ 3 + X * 𝔣 6 * 𝔣 8 ^ 3 * 𝔣 12 * 𝔣 48 ^ 2) ∧
      𝔣 1 ^ 3 * 𝔣 4 * 𝔣 6 ^ 2 * 𝔣 12 =
        𝔣 3 * (𝔣 4 ^ 4 * 𝔣 6 ^ 2 - 3 * X * 𝔣 2 ^ 2 * 𝔣 12 ^ 4) ∧
      𝔣 5 * 𝔣 2 ^ 3 * 𝔣 8 * 𝔣 20 * 𝔣 40 =
        𝔣 1 * (𝔣 2 * 𝔣 8 ^ 2 * 𝔣 20 ^ 3 + X * 𝔣 4 ^ 3 * 𝔣 10 * 𝔣 40 ^ 2) ∧
      𝔣 1 * 𝔣 4 * 𝔣 8 * 𝔣 10 ^ 3 * 𝔣 40 =
        𝔣 5 * (𝔣 2 * 𝔣 8 ^ 2 * 𝔣 20 ^ 3 - X * 𝔣 4 ^ 3 * 𝔣 10 * 𝔣 40 ^ 2)

/-- **Congruences modulo 4 for regular cubic partitions with odd parts overlined.** Write
$f_k = \prod_{m \ge 1} (1 - q^{km})$ for the Euler products in the ring of integer power series
in $q$. For $\ell \ge 1$ let $a_\ell(n)$ be the $n$th coefficient of
$f_2 f_\ell^2 f_{4\ell} / (f_1^2 f_4 f_{2\ell})$; for $\ell > 2$ this is the number of
$\ell$-regular cubic partitions of $n$ with odd parts overlined. Then for all natural numbers
$k$ and $n$: (i) if $k > 1$, then $4$ divides $a_{2k}(4n + 3)$; (ii) if $k \ge 1$, then $4$
divides $a_{2k+1}(4n + 2)$; (iii) if $k > 0$, then $4$ divides $a_{4k}(4n + 2)$; (iv) if
$k > 0$, then $4$ divides $a_{4k+1}(4n + 3)$.

Source: Pujashree Buragohain and Nipen Saikia, *Some New Congruences for l-Regular Cubic
Partitions with Odd Parts Overlined*, INTEGERS 24 (2024), Article A101, Theorem 5,
eqs. (17)–(20) (`integers-2024-A101-thm-5`). -/
public theorem_wanted regularCubicOverlinedCount_mod_four (k n : ℕ) :
    (1 < k → (4 : ℤ) ∣ regularCubicOverlinedCount (2 * k) (4 * n + 3)) ∧
      (1 ≤ k → (4 : ℤ) ∣ regularCubicOverlinedCount (2 * k + 1) (4 * n + 2)) ∧
      (0 < k → (4 : ℤ) ∣ regularCubicOverlinedCount (4 * k) (4 * n + 2)) ∧
      (0 < k → (4 : ℤ) ∣ regularCubicOverlinedCount (4 * k + 1) (4 * n + 3))

/-- **Congruences modulo 12 for 3-regular cubic partitions with odd parts overlined.** Let
$a_3(n)$ be the number of $3$-regular cubic partitions of $n$ with odd parts overlined, and let
$f_k = \prod_{m \ge 1} (1 - q^{km})$. Let $p \ge 5$ be a prime with Legendre symbol
$\left(\frac{-6}{p}\right) = -1$, and let $\delta \ge 0$. Then for every $n \ge 0$,
$$a_3\left(8p^{2\delta} n + \frac{10p^{2\delta} - 1}{3}\right) \equiv 6c_n \pmod{12},$$
where $c_n$ is the coefficient of $q^n$ in $f_4 f_6$, and for all $n \ge 0$ and all $t$ with
$1 \le t \le p - 1$,
$$a_3\left(8p^{2\delta+2} n + 8p^{2\delta+1} t + \frac{10p^{2\delta+2} - 1}{3}\right)
\equiv 0 \pmod{12}.$$
The divisions by $3$ are exact.

Source: Pujashree Buragohain and Nipen Saikia, *Some New Congruences for l-Regular Cubic
Partitions with Odd Parts Overlined*, INTEGERS 24 (2024), Article A101, Theorem 6,
eqs. (26), (27) (`integers-2024-A101-thm-6`). -/
public theorem_wanted regularCubicOverlinedCount_three_prime_mod_twelve (p : ℕ) [Fact p.Prime]
    (hp : 5 ≤ p) (hleg : legendreSym p (-6) = -1) (δ : ℕ) :
    (∀ n : ℕ, regularCubicOverlinedCount 3 (8 * p ^ (2 * δ) * n + (10 * p ^ (2 * δ) - 1) / 3) ≡
        6 * coeff n (𝔣 4 * 𝔣 6) [ZMOD 12]) ∧
      ∀ n t : ℕ, 1 ≤ t → t ≤ p - 1 →
        regularCubicOverlinedCount 3 (8 * p ^ (2 * δ + 2) * n + 8 * p ^ (2 * δ + 1) * t +
          (10 * p ^ (2 * δ + 2) - 1) / 3) ≡ 0 [ZMOD 12]

/-- **Congruences modulo 18 and 12 for 3-regular cubic partitions with odd parts overlined.**
Let $a_3(n)$ be the number of $3$-regular cubic partitions of $n$ with odd parts overlined.
For every $n \ge 0$, $a_3(8n + 5)$ is divisible by $18$, and $a_3(16n + 11)$ and
$a_3(16n + 15)$ are divisible by $12$.

Source: Pujashree Buragohain and Nipen Saikia, *Some New Congruences for l-Regular Cubic
Partitions with Odd Parts Overlined*, INTEGERS 24 (2024), Article A101, Corollary 1,
eqs. (39)–(41) (`integers-2024-A101-cor-1`). -/
public theorem_wanted regularCubicOverlinedCount_three_mod_eighteen_twelve (n : ℕ) :
    (18 : ℤ) ∣ regularCubicOverlinedCount 3 (8 * n + 5) ∧
      (12 : ℤ) ∣ regularCubicOverlinedCount 3 (16 * n + 11) ∧
      (12 : ℤ) ∣ regularCubicOverlinedCount 3 (16 * n + 15)

/-- **Congruences modulo 6 for 3-regular cubic partitions with odd parts overlined.** Let
$a_3(n)$ be the number of $3$-regular cubic partitions of $n$ with odd parts overlined, and let
$f_k = \prod_{m \ge 1} (1 - q^{km})$. Let $p \ge 5$ be a prime with Legendre symbol
$\left(\frac{-3}{p}\right) = -1$, and let $\delta \ge 0$. Then for every $n \ge 0$,
$$a_3\left(8p^{2\delta} n + \frac{4p^{2\delta} - 1}{3}\right) \equiv 2c_n \pmod 6,$$
where $c_n$ is the coefficient of $q^n$ in $f_1 f_3$, and for all $n \ge 0$ and all $t$ with
$1 \le t \le p - 1$,
$$a_3\left(8p^{2\delta+2} n + 8p^{2\delta+1} t + \frac{4p^{2\delta+2} - 1}{3}\right)
\equiv 0 \pmod 6.$$
The divisions by $3$ are exact.

Source: Pujashree Buragohain and Nipen Saikia, *Some New Congruences for l-Regular Cubic
Partitions with Odd Parts Overlined*, INTEGERS 24 (2024), Article A101, Theorem 7, eq. (46)
and the unnumbered congruence after it (`integers-2024-A101-thm-7`). -/
public theorem_wanted regularCubicOverlinedCount_three_prime_mod_six (p : ℕ) [Fact p.Prime]
    (hp : 5 ≤ p) (hleg : legendreSym p (-3) = -1) (δ : ℕ) :
    (∀ n : ℕ, regularCubicOverlinedCount 3 (8 * p ^ (2 * δ) * n + (4 * p ^ (2 * δ) - 1) / 3) ≡
        2 * coeff n (𝔣 1 * 𝔣 3) [ZMOD 6]) ∧
      ∀ n t : ℕ, 1 ≤ t → t ≤ p - 1 →
        regularCubicOverlinedCount 3 (8 * p ^ (2 * δ + 2) * n + 8 * p ^ (2 * δ + 1) * t +
          (4 * p ^ (2 * δ + 2) - 1) / 3) ≡ 0 [ZMOD 6]

/-- **Congruences modulo 4 for 4-regular cubic partitions with odd parts overlined.** Write
$f_k = \prod_{m \ge 1} (1 - q^{km})$ for the Euler products in the ring of integer power series
in $q$, and $a_4(n)$ for the $n$th coefficient of $f_2 f_4^2 f_{16} / (f_1^2 f_4 f_8)$, the
number of $4$-regular cubic partitions of $n$ with odd parts overlined. Let $p \ge 5$ be a prime
with Legendre symbol $\left(\frac{-2}{p}\right) = -1$ and let $\delta \ge 0$. Then for every
$n \ge 0$, $a_4(4p^{2\delta} n + (3p^{2\delta} - 1)/2)$ is congruent modulo $4$ to twice the
coefficient of $q^n$ in $f_1 f_8$, and for all $n \ge 0$ and $1 \le t \le p - 1$,
$$
a_4\left(4p^{2\delta+2} n + 4p^{2\delta+1} t + \frac{3p^{2\delta+2} - 1}{2}\right) \equiv 0
\pmod{4}.
$$

The divisions by $2$ are exact.

Source: Pujashree Buragohain and Nipen Saikia, *Some New Congruences for l-Regular Cubic
Partitions with Odd Parts Overlined*, INTEGERS 24 (2024), Article A101, Theorem 8, eq. (49)
and the unnumbered congruence after it (`integers-2024-A101-thm-8`). -/
public theorem_wanted regularCubicOverlinedCount_four_prime_mod_four (p : ℕ) [Fact p.Prime]
    (hp : 5 ≤ p) (hleg : legendreSym p (-2) = -1) (δ : ℕ) :
    (∀ n : ℕ, regularCubicOverlinedCount 4 (4 * p ^ (2 * δ) * n + (3 * p ^ (2 * δ) - 1) / 2) ≡
        2 * coeff n (𝔣 1 * 𝔣 8) [ZMOD 4]) ∧
      ∀ n t : ℕ, 1 ≤ t → t ≤ p - 1 →
        regularCubicOverlinedCount 4 (4 * p ^ (2 * δ + 2) * n + 4 * p ^ (2 * δ + 1) * t +
          (3 * p ^ (2 * δ + 2) - 1) / 2) ≡ 0 [ZMOD 4]

/-- **Congruences modulo 8, 56 and 24 for 4-regular cubic partitions with odd parts overlined.**
Let $a_4(n)$ be the number of $4$-regular cubic partitions of $n$ with odd parts overlined, that
is, the $n$th coefficient of $f_2 f_4^2 f_{16} / (f_1^2 f_4 f_8)$, where
$f_k = \prod_{m \ge 1} (1 - q^{km})$. Then for every $n \ge 0$, $8$ divides $a_4(4n + 3)$, $56$
divides $a_4(28n + 4j + 3)$ for each $j = 1, \ldots, 6$, and $24$ divides $a_4(36n + 19)$.

Source: Pujashree Buragohain and Nipen Saikia, *Some New Congruences for l-Regular Cubic
Partitions with Odd Parts Overlined*, INTEGERS 24 (2024), Article A101, Corollary 2,
eqs. (55)–(57) (`integers-2024-A101-cor-2`). -/
public theorem_wanted regularCubicOverlinedCount_four_mod_eight_fiftySix_twentyFour (n : ℕ) :
    (8 : ℤ) ∣ regularCubicOverlinedCount 4 (4 * n + 3) ∧
      (∀ j ∈ Finset.Icc 1 6, (56 : ℤ) ∣ regularCubicOverlinedCount 4 (28 * n + 4 * j + 3)) ∧
      (24 : ℤ) ∣ regularCubicOverlinedCount 4 (36 * n + 19)

/-- **Congruences modulo 8 for 5-regular cubic partitions with odd parts overlined.** Write
$f_k = \prod_{m \ge 1} (1 - q^{km})$ for the Euler products in the ring of integer power series
in $q$, and $a_5(n)$ for the $n$th coefficient of $f_2 f_5^2 f_{20} / (f_1^2 f_4 f_{10})$, the
number of $5$-regular cubic partitions of $n$ with odd parts overlined. Let $p \ge 5$ be a prime
with Legendre symbol $\left(\frac{-3}{p}\right) = -1$, let $s = (p - 1)/6$ if $p \equiv 1 \pmod 6$
and $s = (-p - 1)/6$ otherwise, and let $\delta \ge 0$. Then, comparing coefficients of power
series in $q$,
$$
\sum_{n \ge 0} a_5\left(10p^{2\delta} n + \frac{5p^{2\delta} - 2}{3}\right) q^n \equiv
2 (-1)^{\delta s} f_2^2 \pmod{8},
$$
$$
f_4 \sum_{n \ge 0} a_5\left(40p^{2\delta} n + \frac{65p^{2\delta} - 2}{3}\right) q^n \equiv
4 (-1)^{\delta s} f_1 f_8^2 \pmod{8},
$$
and for all $n \ge 0$ and $1 \le t \le p - 1$,
$$
a_5\left(10p^{2\delta+2} n + 10p^{2\delta+1} t + \frac{5p^{2\delta+2} - 2}{3}\right) \equiv 0
\pmod{8},
$$
$$
a_5\left(40p^{2\delta+2} n + 40p^{2\delta+1} t + \frac{65p^{2\delta+2} - 2}{3}\right) \equiv 0
\pmod{8}.
$$

The divisions by $3$ are exact. With $\psi(q) = f_2^2 / f_1$ and $\psi(q^4) = f_8^2 / f_4$, the
power series congruences are the paper's $\sum_n a_5(\ldots) q^n \equiv 2 (-1)^{\delta s} f_1
\psi(q) \pmod{8}$ and $\sum_n a_5(\ldots) q^n \equiv 4 (-1)^{\delta s} f_1 \psi(q^4) \pmod{8}$,
the second multiplied by $f_4$.

Source: Pujashree Buragohain and Nipen Saikia, *Some New Congruences for l-Regular Cubic
Partitions with Odd Parts Overlined*, INTEGERS 24 (2024), Article A101, Theorem 9,
eqs. (64)–(67) (`integers-2024-A101-thm-9`). -/
public theorem_wanted regularCubicOverlinedCount_five_prime_mod_eight (p : ℕ) [Fact p.Prime]
    (hp : 5 ≤ p) (hleg : legendreSym p (-3) = -1)
    (s : ℤ) (hs : s = if p % 6 = 1 then ((p : ℤ) - 1) / 6 else (-(p : ℤ) - 1) / 6) (δ : ℕ) :
    (∀ n : ℕ, regularCubicOverlinedCount 5 (10 * p ^ (2 * δ) * n + (5 * p ^ (2 * δ) - 2) / 3) ≡
        2 * (-1) ^ ((δ : ℤ) * s).natAbs * coeff n (𝔣 2 ^ 2) [ZMOD 8]) ∧
      (∀ n t : ℕ, 1 ≤ t → t ≤ p - 1 →
        regularCubicOverlinedCount 5 (10 * p ^ (2 * δ + 2) * n + 10 * p ^ (2 * δ + 1) * t +
          (5 * p ^ (2 * δ + 2) - 2) / 3) ≡ 0 [ZMOD 8]) ∧
      (∀ n : ℕ, coeff n (𝔣 4 * PowerSeries.mk fun m =>
          regularCubicOverlinedCount 5 (40 * p ^ (2 * δ) * m + (65 * p ^ (2 * δ) - 2) / 3)) ≡
        4 * (-1) ^ ((δ : ℤ) * s).natAbs * coeff n (𝔣 1 * 𝔣 8 ^ 2) [ZMOD 8]) ∧
      ∀ n t : ℕ, 1 ≤ t → t ≤ p - 1 →
        regularCubicOverlinedCount 5 (40 * p ^ (2 * δ + 2) * n + 40 * p ^ (2 * δ + 1) * t +
          (65 * p ^ (2 * δ + 2) - 2) / 3) ≡ 0 [ZMOD 8]

/-- **Congruences modulo 16 and 8 for 5-regular cubic partitions with odd parts overlined.** Let
$a_5(n)$ be the number of $5$-regular cubic partitions of $n$ with odd parts overlined, that is,
the $n$th coefficient of $f_2 f_5^2 f_{20} / (f_1^2 f_4 f_{10})$, where
$f_k = \prod_{m \ge 1} (1 - q^{km})$. Then for every $n \ge 0$, $16$ divides $a_5(8n + 7)$, and
$8$ divides $a_5(20n + 2j + 1)$ for each $j = 1, \ldots, 9$.

Source: Pujashree Buragohain and Nipen Saikia, *Some New Congruences for l-Regular Cubic
Partitions with Odd Parts Overlined*, INTEGERS 24 (2024), Article A101, Corollary 3,
eqs. (76), (77) (`integers-2024-A101-cor-3`). -/
public theorem_wanted regularCubicOverlinedCount_five_mod_sixteen_eight (n : ℕ) :
    (16 : ℤ) ∣ regularCubicOverlinedCount 5 (8 * n + 7) ∧
      ∀ j ∈ Finset.Icc 1 9, (8 : ℤ) ∣ regularCubicOverlinedCount 5 (20 * n + 2 * j + 1)

/-- **Congruences modulo 4 for 5-regular cubic partitions with odd parts overlined.** Write
$f_k = \prod_{m \ge 1} (1 - q^{km})$ for the Euler products in the ring of integer power series
in $q$, and $a_5(n)$ for the $n$th coefficient of $f_2 f_5^2 f_{20} / (f_1^2 f_4 f_{10})$, the
number of $5$-regular cubic partitions of $n$ with odd parts overlined. Let $p \ge 5$ be a prime
with Legendre symbol $\left(\frac{-15}{p}\right) = -1$, let $s = (p - 1)/6$ if
$p \equiv 1 \pmod 6$ and $s = (-p - 1)/6$ otherwise, and let $\delta \ge 0$. Then, comparing
coefficients of power series in $q$,
$$
f_{20} \sum_{n \ge 0} a_5\left(16p^{2\delta+2} n + \frac{122p^{2\delta+2} - 2}{3}\right) q^n
\equiv 2 (-1)^{(\delta+1) s} f_1 f_{40}^2 \pmod{4},
$$
and for all $n \ge 0$ and $1 \le t \le p - 1$,
$$
a_5\left(16p^{2\delta+2} n + 16p^{2\delta+1} t + \frac{122p^{2\delta+2} - 2}{3}\right) \equiv 0
\pmod{4}.
$$

The divisions by $3$ are exact. With $\psi(q^{20}) = f_{40}^2 / f_{20}$, the first congruence is
the paper's $\sum_n a_5(\ldots) q^n \equiv 2 (-1)^{(\delta+1) s} f_1 \psi(q^{20}) \pmod{4}$
multiplied by $f_{20}$.

Source: Pujashree Buragohain and Nipen Saikia, *Some New Congruences for l-Regular Cubic
Partitions with Odd Parts Overlined*, INTEGERS 24 (2024), Article A101, Theorem 10,
eqs. (80), (81) (`integers-2024-A101-thm-10`). -/
public theorem_wanted regularCubicOverlinedCount_five_prime_mod_four (p : ℕ) [Fact p.Prime]
    (hp : 5 ≤ p) (hleg : legendreSym p (-15) = -1)
    (s : ℤ) (hs : s = if p % 6 = 1 then ((p : ℤ) - 1) / 6 else (-(p : ℤ) - 1) / 6) (δ : ℕ) :
    (∀ n : ℕ, coeff n (𝔣 20 * PowerSeries.mk fun m =>
          regularCubicOverlinedCount 5
            (16 * p ^ (2 * δ + 2) * m + (122 * p ^ (2 * δ + 2) - 2) / 3)) ≡
        2 * (-1) ^ (((δ : ℤ) + 1) * s).natAbs * coeff n (𝔣 1 * 𝔣 40 ^ 2) [ZMOD 4]) ∧
      ∀ n t : ℕ, 1 ≤ t → t ≤ p - 1 →
        regularCubicOverlinedCount 5 (16 * p ^ (2 * δ + 2) * n + 16 * p ^ (2 * δ + 1) * t +
          (122 * p ^ (2 * δ + 2) - 2) / 3) ≡ 0 [ZMOD 4]

/-- **Congruences modulo 4 and 8 for 8-regular cubic partitions with odd parts overlined.** Write
$f_k = \prod_{m \ge 1} (1 - q^{km})$ for the Euler products in the ring of integer power series
in $q$, and $a_8(n)$ for the $n$th coefficient of $f_2 f_8^2 f_{32} / (f_1^2 f_4 f_{16})$, the
number of $8$-regular cubic partitions of $n$ with odd parts overlined. Let $p \ge 5$ be a prime
with Legendre symbol $\left(\frac{-3}{p}\right) = -1$, let $s = (p - 1)/6$ if $p \equiv 1 \pmod 6$
and $s = (-p - 1)/6$ otherwise, and let $\delta \ge 0$. Then, comparing coefficients of power
series in $q$,
$$
f_4 \sum_{n \ge 0} a_8\left(4p^{2\delta} n + \frac{13p^{2\delta} - 7}{6}\right) q^n \equiv
2 (-1)^{\delta s} f_1 f_8^2 \pmod{4},
$$
$$
f_1 \sum_{n \ge 0} a_8\left(4p^{2\delta} n + \frac{19p^{2\delta} - 7}{6}\right) q^n \equiv
4 (-1)^{\delta s} f_2^2 f_{16} \pmod{8},
$$
and for all $n \ge 0$ and $1 \le t \le p - 1$,
$$
a_8\left(4p^{2\delta+2} n + 4p^{2\delta+1} t + \frac{13p^{2\delta+2} - 7}{6}\right) \equiv 0
\pmod{4},
$$
$$
a_8\left(4p^{2\delta+2} n + 4p^{2\delta+1} t + \frac{19p^{2\delta+2} - 7}{6}\right) \equiv 0
\pmod{8}.
$$

The divisions by $6$ are exact. With $\psi(q) = f_2^2 / f_1$ and $\psi(q^4) = f_8^2 / f_4$, the
power series congruences are the paper's $\sum_n a_8(\ldots) q^n \equiv 2 (-1)^{\delta s} f_1
\psi(q^4) \pmod{4}$ and $\sum_n a_8(\ldots) q^n \equiv 4 (-1)^{\delta s} \psi(q) f_{16} \pmod{8}$,
multiplied by $f_4$ and by $f_1$.

Source: Pujashree Buragohain and Nipen Saikia, *Some New Congruences for l-Regular Cubic
Partitions with Odd Parts Overlined*, INTEGERS 24 (2024), Article A101, Theorem 11,
eqs. (93)–(96) (`integers-2024-A101-thm-11`). -/
public theorem_wanted regularCubicOverlinedCount_eight_prime_mod_four_eight (p : ℕ)
    [Fact p.Prime] (hp : 5 ≤ p) (hleg : legendreSym p (-3) = -1)
    (s : ℤ) (hs : s = if p % 6 = 1 then ((p : ℤ) - 1) / 6 else (-(p : ℤ) - 1) / 6) (δ : ℕ) :
    (∀ n : ℕ, coeff n (𝔣 4 * PowerSeries.mk fun m =>
          regularCubicOverlinedCount 8 (4 * p ^ (2 * δ) * m + (13 * p ^ (2 * δ) - 7) / 6)) ≡
        2 * (-1) ^ ((δ : ℤ) * s).natAbs * coeff n (𝔣 1 * 𝔣 8 ^ 2) [ZMOD 4]) ∧
      (∀ n t : ℕ, 1 ≤ t → t ≤ p - 1 →
        regularCubicOverlinedCount 8 (4 * p ^ (2 * δ + 2) * n + 4 * p ^ (2 * δ + 1) * t +
          (13 * p ^ (2 * δ + 2) - 7) / 6) ≡ 0 [ZMOD 4]) ∧
      (∀ n : ℕ, coeff n (𝔣 1 * PowerSeries.mk fun m =>
          regularCubicOverlinedCount 8 (4 * p ^ (2 * δ) * m + (19 * p ^ (2 * δ) - 7) / 6)) ≡
        4 * (-1) ^ ((δ : ℤ) * s).natAbs * coeff n (𝔣 2 ^ 2 * 𝔣 16) [ZMOD 8]) ∧
      ∀ n t : ℕ, 1 ≤ t → t ≤ p - 1 →
        regularCubicOverlinedCount 8 (4 * p ^ (2 * δ + 2) * n + 4 * p ^ (2 * δ + 1) * t +
          (19 * p ^ (2 * δ + 2) - 7) / 6) ≡ 0 [ZMOD 8]

/-- **Congruences modulo 16 for 8-regular cubic partitions with odd parts overlined.** Write
$f_k = \prod_{m \ge 1} (1 - q^{km})$ for the Euler products in the ring of integer power series
in $q$, and $a_8(n)$ for the $n$th coefficient of $f_2 f_8^2 f_{32} / (f_1^2 f_4 f_{16})$, the
number of $8$-regular cubic partitions of $n$ with odd parts overlined. Let $p \ge 5$ be a prime
with Legendre symbol $\left(\frac{-6}{p}\right) = -1$, let $s = (p - 1)/6$ if $p \equiv 1 \pmod 6$
and $s = (-p - 1)/6$ otherwise, and let $\delta \ge 0$. Then, comparing coefficients of power
series in $q$,
$$
f_8 \sum_{n \ge 0} a_8\left(4p^{2\delta} n + \frac{25p^{2\delta} - 7}{6}\right) q^n \equiv
8 (-1)^{\delta s} f_1 f_{16}^2 \pmod{16},
$$
and for all $n \ge 0$ and $1 \le t \le p - 1$,
$$
a_8\left(4p^{2\delta+2} n + 4p^{2\delta+1} t + \frac{25p^{2\delta+2} - 7}{6}\right) \equiv 0
\pmod{16}.
$$

The divisions by $6$ are exact. With $\psi(q^8) = f_{16}^2 / f_8$, the first congruence is
the paper's $\sum_n a_8(\ldots) q^n \equiv 8 (-1)^{\delta s} f_1 \psi(q^8) \pmod{16}$
multiplied by $f_8$.

Source: Pujashree Buragohain and Nipen Saikia, *Some New Congruences for l-Regular Cubic
Partitions with Odd Parts Overlined*, INTEGERS 24 (2024), Article A101, Theorem 12,
eqs. (105), (106) (`integers-2024-A101-thm-12`). -/
public theorem_wanted regularCubicOverlinedCount_eight_prime_mod_sixteen (p : ℕ) [Fact p.Prime]
    (hp : 5 ≤ p) (hleg : legendreSym p (-6) = -1)
    (s : ℤ) (hs : s = if p % 6 = 1 then ((p : ℤ) - 1) / 6 else (-(p : ℤ) - 1) / 6) (δ : ℕ) :
    (∀ n : ℕ, coeff n (𝔣 8 * PowerSeries.mk fun m =>
          regularCubicOverlinedCount 8 (4 * p ^ (2 * δ) * m + (25 * p ^ (2 * δ) - 7) / 6)) ≡
        8 * (-1) ^ ((δ : ℤ) * s).natAbs * coeff n (𝔣 1 * 𝔣 16 ^ 2) [ZMOD 16]) ∧
      ∀ n t : ℕ, 1 ≤ t → t ≤ p - 1 →
        regularCubicOverlinedCount 8 (4 * p ^ (2 * δ + 2) * n + 4 * p ^ (2 * δ + 1) * t +
          (25 * p ^ (2 * δ + 2) - 7) / 6) ≡ 0 [ZMOD 16]

/-- **Congruences modulo 4 for 9-regular cubic partitions with odd parts overlined.** Let
$a_9(n)$ be the number of $9$-regular cubic partitions of $n$ with odd parts overlined, and let
$f_k = \prod_{m \ge 1} (1 - q^{km})$. Let $p \ge 5$ be a prime with Legendre symbol
$\left(\frac{-2}{p}\right) = -1$, and let $\delta \ge 0$. Then for every $n \ge 0$,
$$a_9\left(8p^{2\delta} n + \frac{19p^{2\delta} - 4}{3}\right) \equiv 2c_n \pmod 4,$$
where $c_n$ is the coefficient of $q^n$ in $f_1 f_{18}$, and for all $n \ge 0$ and all $t$ with
$1 \le t \le p - 1$,
$$a_9\left(8p^{2\delta+2} n + 8p^{2\delta+1} t + \frac{19p^{2\delta+2} - 4}{3}\right)
\equiv 0 \pmod 4.$$
The divisions by $3$ are exact.

Source: Pujashree Buragohain and Nipen Saikia, *Some New Congruences for l-Regular Cubic
Partitions with Odd Parts Overlined*, INTEGERS 24 (2024), Article A101, Theorem 13, eq. (110)
and the unnumbered congruence after it (`integers-2024-A101-thm-13`). -/
public theorem_wanted regularCubicOverlinedCount_nine_prime_mod_four (p : ℕ) [Fact p.Prime]
    (hp : 5 ≤ p) (hleg : legendreSym p (-2) = -1) (δ : ℕ) :
    (∀ n : ℕ, regularCubicOverlinedCount 9 (8 * p ^ (2 * δ) * n + (19 * p ^ (2 * δ) - 4) / 3) ≡
        2 * coeff n (𝔣 1 * 𝔣 18) [ZMOD 4]) ∧
      ∀ n t : ℕ, 1 ≤ t → t ≤ p - 1 →
        regularCubicOverlinedCount 9 (8 * p ^ (2 * δ + 2) * n + 8 * p ^ (2 * δ + 1) * t +
          (19 * p ^ (2 * δ + 2) - 4) / 3) ≡ 0 [ZMOD 4]

/-- **Congruence modulo 8 for 9-regular cubic partitions with odd parts overlined.** For every
$n \ge 0$, the number $a_9(4n + 3)$ of $9$-regular cubic partitions of $4n + 3$ with odd parts
overlined is divisible by $8$.

Source: Pujashree Buragohain and Nipen Saikia, *Some New Congruences for l-Regular Cubic
Partitions with Odd Parts Overlined*, INTEGERS 24 (2024), Article A101, Corollary 4,
eq. (118) (`integers-2024-A101-cor-4`). -/
public theorem_wanted regularCubicOverlinedCount_nine_four_mul_add_three (n : ℕ) :
    (8 : ℤ) ∣ regularCubicOverlinedCount 9 (4 * n + 3)

/-- **Congruences modulo 16 for 16-regular cubic partitions with odd parts overlined.** Let
$a_{16}(n)$ be the number of $16$-regular cubic partitions of $n$ with odd parts overlined, and
let $f_k = \prod_{m \ge 1} (1 - q^{km})$. Let $p \ge 5$ be a prime with Legendre symbol
$\left(\frac{-2}{p}\right) = -1$, and let $\delta \ge 0$. Then for every $n \ge 0$,
$$a_{16}\left(4p^{2\delta} n + \frac{11p^{2\delta} - 5}{2}\right) \equiv 8c_n \pmod{16},$$
where $c_n$ is the coefficient of $q^n$ in $f_1 f_{32}$, and for all $n \ge 0$ and all $t$ with
$1 \le t \le p - 1$,
$$a_{16}\left(4p^{2\delta+2} n + 4p^{2\delta+1} t + \frac{11p^{2\delta+2} - 5}{2}\right)
\equiv 0 \pmod{16}.$$
The divisions by $2$ are exact.

Source: Pujashree Buragohain and Nipen Saikia, *Some New Congruences for l-Regular Cubic
Partitions with Odd Parts Overlined*, INTEGERS 24 (2024), Article A101, Theorem 14, eq. (119)
and the unnumbered congruence after it (`integers-2024-A101-thm-14`). -/
public theorem_wanted regularCubicOverlinedCount_sixteen_prime_mod_sixteen (p : ℕ)
    [Fact p.Prime] (hp : 5 ≤ p) (hleg : legendreSym p (-2) = -1) (δ : ℕ) :
    (∀ n : ℕ, regularCubicOverlinedCount 16 (4 * p ^ (2 * δ) * n + (11 * p ^ (2 * δ) - 5) / 2) ≡
        8 * coeff n (𝔣 1 * 𝔣 32) [ZMOD 16]) ∧
      ∀ n t : ℕ, 1 ≤ t → t ≤ p - 1 →
        regularCubicOverlinedCount 16 (4 * p ^ (2 * δ + 2) * n + 4 * p ^ (2 * δ + 1) * t +
          (11 * p ^ (2 * δ + 2) - 5) / 2) ≡ 0 [ZMOD 16]

end

end MetaMathlibExt
