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
# Congruences modulo powers of 2 for 2-regular partitions with designated summands

Statements from James A. Sellers, *New Infinite Families of Congruences Modulo Powers of 2 for
2-Regular Partitions with Designated Summands*, INTEGERS 24 (2024), Article A16.

`PD_2(n)` (Andrews, Lewis, and Lovejoy's `PDO(n)`) counts the partitions of `n` with designated
summands in which every part is odd: in a partition into odd parts, exactly one occurrence of
each distinct part is designated, so `PD_2(4) = 5`. Its generating function is
`∑ PD_2(n) q^n = f_4 f_6^2 / (f_1 f_3 f_12)` (the paper's eq. (1), quoted from Andrews, Lewis,
and Lovejoy), where `f_k = (q^k; q^k)_∞` is `qEulerProduct k`, written `𝔣 k` below. We define
`PD_2(n)` as the `n`th coefficient of that quotient in `ℤ⟦X⟧` (the denominator has constant
coefficient `1`, so it is a unit). Eta-quotient identities are stated with denominators cleared;
a congruence `∑ a(n) q^n ≡ N / D (mod m)` between power series is stated coefficientwise as
`D · ∑ a(n) q^n ≡ N (mod m)`, which is equivalent because `D` is a unit of `ℤ⟦X⟧`.

The statements were checked against the arXiv version (arXiv:2306.15130v1, whose journal
reference is this article); the arXiv text numbers results by section (Theorem 1.2, Lemma 2.1,
...), and the labels below are the journal labels of the Drive corpus records.

The paper's Lemmas 1, 2 and 4 are already stated in this library:
`one_div_f1_pow_four_eight_twelve_two_dissection` (first conjunct),
`f1_sq_two_dissection`, and `qEulerProduct_pow_prime_pow_congruence`; the first identity of its
Lemma 3 is `one_div_f1_f3_two_dissection`.
-/

open PowerSeries
open scoped PowerSeries.WithPiTopology

namespace MetaMathlibExt

@[expose] public section

local notation "𝔣" => qEulerProduct

/-- **Generating function of odd designated-summand partitions.** For $k \ge 1$ let
$f_k = \prod_{m \ge 1} (1 - q^{km})$ be the Euler product. This is the integer power series
$f_4 f_6^2 / (f_1 f_3 f_{12})$ in $q$, where the denominator $f_1 f_3 f_{12}$ is invertible
because its constant coefficient is $1$. It is the generating function
$\sum_{n \ge 0} \mathrm{PD}_2(n) q^n$ of the numbers $\mathrm{PD}_2(n)$ of partitions of $n$ with
designated summands into odd parts.

Source: James A. Sellers, *New Infinite Families of Congruences Modulo Powers of 2 for 2-Regular
Partitions with Designated Summands*, INTEGERS 24 (2024), Article A16, Section 2, eq. (1)
(quoting G. E. Andrews, R. P. Lewis, and J. Lovejoy, *Partitions with designated summands*,
Acta Arith. 105 (2002)). -/
noncomputable def oddDesignatedSummandsSeries : ℤ⟦X⟧ :=
  𝔣 4 * 𝔣 6 ^ 2 * invOfUnit (𝔣 1 * 𝔣 3 * 𝔣 12) 1

/-- **The odd designated-summand partition function.** For a natural number $n$, the integer
$\mathrm{PD}_2(n)$ is defined as the coefficient of $q^n$ in the integer power series
$f_4 f_6^2 / (f_1 f_3 f_{12})$, where $f_k = \prod_{m \ge 1} (1 - q^{km})$ is the Euler product
(the denominator has constant coefficient $1$, so it is invertible). It counts the partitions of
$n$ with designated summands in which all parts are odd.

Source: James A. Sellers, *New Infinite Families of Congruences Modulo Powers of 2 for 2-Regular
Partitions with Designated Summands*, INTEGERS 24 (2024), Article A16, Sections 1-2, eq. (1). -/
noncomputable def oddDesignatedSummandsCount (n : ℕ) : ℤ :=
  coeff n oddDesignatedSummandsSeries

/-- **Generating function for partitions with designated summands into odd parts.** Let
$f_k = \prod_{m \ge 1} (1 - q^{km})$ in the ring of integer power series in $q$, and let $PD_2(n)$
be the number of partitions of $n$ with designated summands in which every part is odd, defined as
the coefficient of $q^n$ in $f_4 f_6^2 / (f_1 f_3 f_{12})$. Then
$f_1 f_3 f_{12} \sum_{n \ge 0} PD_2(n) q^n = f_4 f_6^2$.

Source: James A. Sellers, *New Infinite Families of Congruences Modulo Powers of 2 for 2-Regular
Partitions with Designated Summands*, INTEGERS 24 (2024), Article A16, Section 2, eq. (1). -/
theorem oddDesignatedSummandsCount_generatingFunction :
    𝔣 1 * 𝔣 3 * 𝔣 12 * PowerSeries.mk oddDesignatedSummandsCount = 𝔣 4 * 𝔣 6 ^ 2 := by
  have hmk : PowerSeries.mk oddDesignatedSummandsCount = oddDesignatedSummandsSeries := by
    ext n
    simp [oddDesignatedSummandsCount]
  have hc : constantCoeff (𝔣 1 * 𝔣 3 * 𝔣 12) = ((1 : ℤˣ) : ℤ) := by
    simp [constantCoeff_qEulerProduct (le_refl 1),
      constantCoeff_qEulerProduct (by norm_num : 1 ≤ 3),
      constantCoeff_qEulerProduct (by norm_num : 1 ≤ 12)]
  rw [hmk, oddDesignatedSummandsSeries, mul_left_comm, mul_invOfUnit _ _ hc, mul_one]

/-- **Odd designated-summand partitions of zero.** The odd designated-summand partition function
satisfies $\mathrm{PD}_2(0) = 1$.

Source: James A. Sellers, *New Infinite Families of Congruences Modulo Powers of 2 for 2-Regular
Partitions with Designated Summands*, INTEGERS 24 (2024), Article A16, Section 2, eq. (1). -/
theorem oddDesignatedSummandsCount_zero : oddDesignatedSummandsCount 0 = 1 := by
  have h := congrArg (coeff 0) oddDesignatedSummandsCount_generatingFunction
  simp only [coeff_zero_eq_constantCoeff, map_mul, map_pow,
    constantCoeff_qEulerProduct (le_refl 1), constantCoeff_qEulerProduct (by norm_num : 1 ≤ 3),
    constantCoeff_qEulerProduct (by norm_num : 1 ≤ 12),
    constantCoeff_qEulerProduct (by norm_num : 1 ≤ 4),
    constantCoeff_qEulerProduct (by norm_num : 1 ≤ 6), one_pow, one_mul] at h
  simpa using h

/-- **The 2-dissection of $f_1 f_3$.** Let $f_k = \prod_{m \ge 1} (1 - q^{km})$ denote the Euler
products in the ring of integer power series in $q$. Then
$$f_1 f_2 f_3 f_4^2 f_6 f_8^2 f_{12}^2 f_{24}^2 = f_2^2 f_8^4 f_{12}^6 - q f_4^6 f_6^2 f_{24}^4.$$
Since every $f_k$ with $k \ge 1$ has constant term $1$ and so is invertible, this is Hirschhorn's
identity $f_1 f_3 = \frac{f_2 f_8^2 f_{12}^4}{f_4^2 f_6 f_{24}^2} -
q \frac{f_4^4 f_6 f_{24}^2}{f_2 f_8^2 f_{12}^2}$ (*The Power of q*, eq. (30.12.1)) multiplied
through by $f_2 f_4^2 f_6 f_8^2 f_{12}^2 f_{24}^2$.

Source: James A. Sellers, *New Infinite Families of Congruences Modulo Powers of 2 for 2-Regular
Partitions with Designated Summands*, INTEGERS 24 (2024), Article A16, Lemma 3
(`integers-2024-A16-lem-3`). -/
public theorem_wanted f1_mul_f3_two_dissection :
    𝔣 1 * 𝔣 3 * 𝔣 2 * 𝔣 4 ^ 2 * 𝔣 6 * 𝔣 8 ^ 2 * 𝔣 12 ^ 2 * 𝔣 24 ^ 2 =
      𝔣 2 ^ 2 * 𝔣 8 ^ 4 * 𝔣 12 ^ 6 - X * 𝔣 4 ^ 6 * 𝔣 6 ^ 2 * 𝔣 24 ^ 4

/-- **$\mathrm{PD}_2(2^\alpha (4n + 3))$ is divisible by 4.** Write $\mathrm{PD}_2(m)$ for the
number of partitions of $m$ with designated summands in which every part is odd. For all natural
numbers $\alpha$ and $n$, $\mathrm{PD}_2(2^\alpha (4n + 3)) \equiv 0 \pmod 4$.

Source: James A. Sellers, *New Infinite Families of Congruences Modulo Powers of 2 for 2-Regular
Partitions with Designated Summands*, INTEGERS 24 (2024), Article A16, Theorem 1
(`integers-2024-A16-thm-1`). -/
public theorem_wanted oddDesignatedSummandsCount_two_pow_mul_four_mul_add_three (α n : ℕ) :
    oddDesignatedSummandsCount (2 ^ α * (4 * n + 3)) ≡ 0 [ZMOD 4]

/-- **$\mathrm{PD}_2(2^\alpha (8n + 7))$ is divisible by 8.** Write $\mathrm{PD}_2(m)$ for the
number of partitions of $m$ with designated summands in which every part is odd. For all natural
numbers $\alpha$ and $n$, $\mathrm{PD}_2(2^\alpha (8n + 7)) \equiv 0 \pmod 8$.

Source: James A. Sellers, *New Infinite Families of Congruences Modulo Powers of 2 for 2-Regular
Partitions with Designated Summands*, INTEGERS 24 (2024), Article A16, Theorem 2
(`integers-2024-A16-thm-2`). -/
public theorem_wanted oddDesignatedSummandsCount_two_pow_mul_eight_mul_add_seven (α n : ℕ) :
    oddDesignatedSummandsCount (2 ^ α * (8 * n + 7)) ≡ 0 [ZMOD 8]

/-- **The 2-dissection of the generating function of $\mathrm{PD}_2$.** Write $\mathrm{PD}_2(m)$ for
the number of partitions of $m$ with designated summands in which every part is odd, and write
$f_k = \prod_{j \ge 1} (1 - q^{kj})$ for the Euler product. In the ring of integer power series in
$q$, $f_1^2 f_3^2 f_{12}^2 \sum_{n \ge 0} \mathrm{PD}_2(2n) q^n = f_4^2 f_6^4$ and
$f_1^4 f_4^2 f_6^2 \sum_{n \ge 0} \mathrm{PD}_2(2n + 1) q^n = f_2^6 f_{12}^2$.

These are $\sum_{n} \mathrm{PD}_2(2n) q^n = f_4^2 f_6^4 / (f_1^2 f_3^2 f_{12}^2)$ and
$\sum_{n} \mathrm{PD}_2(2n + 1) q^n = f_2^6 f_{12}^2 / (f_1^4 f_4^2 f_6^2)$ with denominators
cleared.

Source: James A. Sellers, *New Infinite Families of Congruences Modulo Powers of 2 for 2-Regular
Partitions with Designated Summands*, INTEGERS 24 (2024), Article A16, Theorem 3
(`integers-2024-A16-thm-3`). -/
public theorem_wanted oddDesignatedSummandsCount_two_dissection :
    𝔣 1 ^ 2 * 𝔣 3 ^ 2 * 𝔣 12 ^ 2 *
        PowerSeries.mk (fun n => oddDesignatedSummandsCount (2 * n)) =
      𝔣 4 ^ 2 * 𝔣 6 ^ 4 ∧
    𝔣 1 ^ 4 * 𝔣 4 ^ 2 * 𝔣 6 ^ 2 *
        PowerSeries.mk (fun n => oddDesignatedSummandsCount (2 * n + 1)) =
      𝔣 2 ^ 6 * 𝔣 12 ^ 2

/-- **The 4-dissection of the generating function of $PD_2$.** Let
$f_k = \prod_{m \ge 1} (1 - q^{km})$ in the ring of integer power series in $q$, and let $PD_2(n)$
be the number of partitions of $n$ with designated summands in which every part is odd. Then
$f_1^8 f_3^4 f_4^4 f_6^4 f_{12}^4 \sum_{n \ge 0} PD_2(4n) q^n =
f_1^4 f_4^8 f_6^{12} + q f_2^{12} f_3^4 f_{12}^8$,
$f_1^8 f_3^2 f_4^4 \sum_{n \ge 0} PD_2(4n + 1) q^n = f_2^{12} f_6^2$,
$f_1^6 f_3^2 \sum_{n \ge 0} PD_2(4n + 2) q^n = 2 f_2^6 f_6^2$, and
$f_1^4 f_3^2 \sum_{n \ge 0} PD_2(4n + 3) q^n = 4 f_4^4 f_6^2$.

Since every $f_k$ with $k \ge 1$ is invertible, these are the source's quotient formulas for the
four generating functions $\sum_{n \ge 0} PD_2(4n + r) q^n$, $r = 0, 1, 2, 3$, with denominators
cleared.

Source: James A. Sellers, *New Infinite Families of Congruences Modulo Powers of 2 for 2-Regular
Partitions with Designated Summands*, INTEGERS 24 (2024), Article A16, Theorem 4
(`integers-2024-A16-thm-4`). -/
public theorem_wanted oddDesignatedSummandsCount_four_dissection :
    𝔣 1 ^ 8 * 𝔣 3 ^ 4 * 𝔣 4 ^ 4 * 𝔣 6 ^ 4 * 𝔣 12 ^ 4 *
        PowerSeries.mk (fun n => oddDesignatedSummandsCount (4 * n)) =
      𝔣 1 ^ 4 * 𝔣 4 ^ 8 * 𝔣 6 ^ 12 + X * 𝔣 2 ^ 12 * 𝔣 3 ^ 4 * 𝔣 12 ^ 8 ∧
    𝔣 1 ^ 8 * 𝔣 3 ^ 2 * 𝔣 4 ^ 4 *
        PowerSeries.mk (fun n => oddDesignatedSummandsCount (4 * n + 1)) =
      𝔣 2 ^ 12 * 𝔣 6 ^ 2 ∧
    𝔣 1 ^ 6 * 𝔣 3 ^ 2 * PowerSeries.mk (fun n => oddDesignatedSummandsCount (4 * n + 2)) =
      2 * 𝔣 2 ^ 6 * 𝔣 6 ^ 2 ∧
    𝔣 1 ^ 4 * 𝔣 3 ^ 2 * PowerSeries.mk (fun n => oddDesignatedSummandsCount (4 * n + 3)) =
      4 * 𝔣 4 ^ 4 * 𝔣 6 ^ 2

/-- **The 2-dissection of $\mathrm{PD}_2$ modulo 4.** Write $\mathrm{PD}_2(m)$ for the number of
partitions of $m$ with designated summands in which every part is odd, and write
$f_k = \prod_{j \ge 1} (1 - q^{kj})$ for the Euler product, an integer power series in $q$. For
every natural number $n$, the $n$th coefficient of
$f_1^2 f_3^2 \sum_{k \ge 0} \mathrm{PD}_2(2k) q^k$ is congruent modulo $4$ to the $n$th coefficient
of $f_4^2$, and $\mathrm{PD}_2(2n + 1)$ is congruent modulo $4$ to the $n$th coefficient of $f_6^2$.

Coefficientwise, these are $\sum_{k} \mathrm{PD}_2(2k) q^k \equiv f_4^2 / (f_1^2 f_3^2) \pmod 4$,
with its denominator cleared, and $\sum_{k} \mathrm{PD}_2(2k + 1) q^k \equiv f_6^2 \pmod 4$.

Source: James A. Sellers, *New Infinite Families of Congruences Modulo Powers of 2 for 2-Regular
Partitions with Designated Summands*, INTEGERS 24 (2024), Article A16, Theorem 5
(`integers-2024-A16-thm-5`). -/
public theorem_wanted oddDesignatedSummandsCount_two_dissection_mod_four (n : ℕ) :
    coeff n (𝔣 1 ^ 2 * 𝔣 3 ^ 2 *
        PowerSeries.mk (fun k => oddDesignatedSummandsCount (2 * k))) ≡
      coeff n (𝔣 4 ^ 2) [ZMOD 4] ∧
    oddDesignatedSummandsCount (2 * n + 1) ≡ coeff n (𝔣 6 ^ 2) [ZMOD 4]

/-- **Congruences modulo 4 for $\mathrm{PD}_2$ at $4n + 3$, $6n + 3$ and $6n + 5$.** Write
$\mathrm{PD}_2(m)$ for the number of partitions of $m$ with designated summands in which every part
is odd. For every natural number $n$, $\mathrm{PD}_2(4n + 3)$, $\mathrm{PD}_2(6n + 3)$ and
$\mathrm{PD}_2(6n + 5)$ are all congruent to $0$ modulo $4$.

Source: James A. Sellers, *New Infinite Families of Congruences Modulo Powers of 2 for 2-Regular
Partitions with Designated Summands*, INTEGERS 24 (2024), Article A16, Corollary 1
(`integers-2024-A16-cor-1`). -/
public theorem_wanted oddDesignatedSummandsCount_odd_args_mod_four (n : ℕ) :
    oddDesignatedSummandsCount (4 * n + 3) ≡ 0 [ZMOD 4] ∧
      oddDesignatedSummandsCount (6 * n + 3) ≡ 0 [ZMOD 4] ∧
      oddDesignatedSummandsCount (6 * n + 5) ≡ 0 [ZMOD 4]

/-- **$PD_2(4n)$ and $PD_2(4n+2)$ modulo 4.** Let $f_k = \prod_{m \ge 1} (1 - q^{km})$ in the ring
of integer power series in $q$, and let $PD_2(n)$ be the number of partitions of $n$ with
designated summands in which every part is odd. For every $n \ge 0$, the coefficient of $q^n$ in
$f_6^2 \sum_{k \ge 0} PD_2(4k) q^k$ is congruent modulo $4$ to the coefficient of $q^n$ in
$f_2^6 + q f_6^2 f_{12}^2$, and $PD_2(4n + 2)$ is congruent modulo $4$ to the coefficient of
$q^n$ in $2 f_2^3 f_6$.

Since $f_6$ is invertible, this says $\sum_{n \ge 0} PD_2(4n) q^n \equiv f_2^6 / f_6^2 + q f_{12}^2$
(the source's eq. (3)) and $\sum_{n \ge 0} PD_2(4n + 2) q^n \equiv 2 f_2^3 f_6$ coefficientwise
modulo $4$.

Source: James A. Sellers, *New Infinite Families of Congruences Modulo Powers of 2 for 2-Regular
Partitions with Designated Summands*, INTEGERS 24 (2024), Article A16, Theorem 6
(`integers-2024-A16-thm-6`). -/
public theorem_wanted oddDesignatedSummandsCount_four_dissection_mod_four (n : ℕ) :
    coeff n (𝔣 6 ^ 2 * PowerSeries.mk (fun k => oddDesignatedSummandsCount (4 * k))) ≡
      coeff n (𝔣 2 ^ 6 + X * 𝔣 6 ^ 2 * 𝔣 12 ^ 2) [ZMOD 4] ∧
    oddDesignatedSummandsCount (4 * n + 2) ≡ coeff n (2 * 𝔣 2 ^ 3 * 𝔣 6) [ZMOD 4]

/-- **$PD_2(8n+6)$ is divisible by 4.** Let $PD_2(n)$ be the number of partitions of $n$ with
designated summands in which every part is odd. For every $n \ge 0$,
$PD_2(8n + 6) \equiv 0 \pmod 4$.

Source: James A. Sellers, *New Infinite Families of Congruences Modulo Powers of 2 for 2-Regular
Partitions with Designated Summands*, INTEGERS 24 (2024), Article A16, Corollary 2
(`integers-2024-A16-cor-2`). -/
public theorem_wanted oddDesignatedSummandsCount_eight_mul_add_six (n : ℕ) :
    oddDesignatedSummandsCount (8 * n + 6) ≡ 0 [ZMOD 4]

/-- **$PD_2(8n)$ and $PD_2(8n+4)$ modulo 4.** Let $f_k = \prod_{m \ge 1} (1 - q^{km})$ in the ring
of integer power series in $q$, and let $PD_2(n)$ be the number of partitions of $n$ with
designated summands in which every part is odd. For every $n \ge 0$, the coefficient of $q^n$ in
$f_3^2 \sum_{k \ge 0} PD_2(8k) q^k$ is congruent modulo $4$ to the coefficient of $q^n$ in
$f_1^6$, and $PD_2(8n + 4)$ is congruent modulo $4$ to the coefficient of $q^n$ in $f_6^2$.

Since $f_3$ is invertible, this says $\sum_{n \ge 0} PD_2(8n) q^n \equiv f_1^6 / f_3^2$ and
$\sum_{n \ge 0} PD_2(8n + 4) q^n \equiv f_6^2$ coefficientwise modulo $4$.

Source: James A. Sellers, *New Infinite Families of Congruences Modulo Powers of 2 for 2-Regular
Partitions with Designated Summands*, INTEGERS 24 (2024), Article A16, Corollary 3
(`integers-2024-A16-cor-3`). -/
public theorem_wanted oddDesignatedSummandsCount_eight_dissection_mod_four (n : ℕ) :
    coeff n (𝔣 3 ^ 2 * PowerSeries.mk (fun k => oddDesignatedSummandsCount (8 * k))) ≡
      coeff n (𝔣 1 ^ 6) [ZMOD 4] ∧
    oddDesignatedSummandsCount (8 * n + 4) ≡ coeff n (𝔣 6 ^ 2) [ZMOD 4]

/-- **$\mathrm{PD}_2(16n + 12)$ is divisible by 4.** Write $\mathrm{PD}_2(m)$ for the number of
partitions of $m$ with designated summands in which every part is odd. For every natural number $n$,
$\mathrm{PD}_2(16n + 12) \equiv 0 \pmod 4$.

Source: James A. Sellers, *New Infinite Families of Congruences Modulo Powers of 2 for 2-Regular
Partitions with Designated Summands*, INTEGERS 24 (2024), Article A16, Corollary 4
(`integers-2024-A16-cor-4`). -/
public theorem_wanted oddDesignatedSummandsCount_sixteen_mul_add_twelve (n : ℕ) :
    oddDesignatedSummandsCount (16 * n + 12) ≡ 0 [ZMOD 4]

/-- **The internal congruence $PD_2(4n) \equiv PD_2(n) \pmod 4$.** Let $PD_2(n)$ be the number of
partitions of $n$ with designated summands in which every part is odd. For every $n \ge 0$,
$PD_2(4n) \equiv PD_2(n) \pmod 4$.

Source: James A. Sellers, *New Infinite Families of Congruences Modulo Powers of 2 for 2-Regular
Partitions with Designated Summands*, INTEGERS 24 (2024), Article A16, Theorem 7
(`integers-2024-A16-thm-7`). -/
public theorem_wanted oddDesignatedSummandsCount_four_mul_mod_four (n : ℕ) :
    oddDesignatedSummandsCount (4 * n) ≡ oddDesignatedSummandsCount n [ZMOD 4]

/-- **$PD_2(4^\alpha (6n+5))$ is divisible by 4.** Let $PD_2(n)$ be the number of partitions of $n$
with designated summands in which every part is odd. For all $\alpha \ge 0$ and $n \ge 0$,
$PD_2(4^\alpha (6n + 5)) \equiv 0 \pmod 4$.

Source: James A. Sellers, *New Infinite Families of Congruences Modulo Powers of 2 for 2-Regular
Partitions with Designated Summands*, INTEGERS 24 (2024), Article A16, Theorem 8
(`integers-2024-A16-thm-8`). -/
public theorem_wanted oddDesignatedSummandsCount_four_pow_mul_six_mul_add_five (α n : ℕ) :
    oddDesignatedSummandsCount (4 ^ α * (6 * n + 5)) ≡ 0 [ZMOD 4]

/-- **$PD_2(8n+7)$ is divisible by 8.** Let $PD_2(n)$ be the number of partitions of $n$ with
designated summands in which every part is odd. For every $n \ge 0$,
$PD_2(8n + 7) \equiv 0 \pmod 8$.

Source: James A. Sellers, *New Infinite Families of Congruences Modulo Powers of 2 for 2-Regular
Partitions with Designated Summands*, INTEGERS 24 (2024), Article A16, Theorem 9
(`integers-2024-A16-thm-9`). -/
public theorem_wanted oddDesignatedSummandsCount_eight_mul_add_seven (n : ℕ) :
    oddDesignatedSummandsCount (8 * n + 7) ≡ 0 [ZMOD 8]

/-- **$\mathrm{PD}_2(16n + 14)$ is divisible by 8.** Write $\mathrm{PD}_2(m)$ for the number of
partitions of $m$ with designated summands in which every part is odd. For every natural number $n$,
$\mathrm{PD}_2(16n + 14) \equiv 0 \pmod 8$.

Source: James A. Sellers, *New Infinite Families of Congruences Modulo Powers of 2 for 2-Regular
Partitions with Designated Summands*, INTEGERS 24 (2024), Article A16, Theorem 10
(`integers-2024-A16-thm-10`). -/
public theorem_wanted oddDesignatedSummandsCount_sixteen_mul_add_fourteen (n : ℕ) :
    oddDesignatedSummandsCount (16 * n + 14) ≡ 0 [ZMOD 8]

/-- **$\mathrm{PD}_2(32n + 28)$ is divisible by 8.** Write $\mathrm{PD}_2(m)$ for the number of
partitions of $m$ with designated summands in which every part is odd. For every natural number $n$,
$\mathrm{PD}_2(32n + 28) \equiv 0 \pmod 8$.

Source: James A. Sellers, *New Infinite Families of Congruences Modulo Powers of 2 for 2-Regular
Partitions with Designated Summands*, INTEGERS 24 (2024), Article A16, Theorem 11
(`integers-2024-A16-thm-11`). -/
public theorem_wanted oddDesignatedSummandsCount_thirtyTwo_mul_add_twentyEight (n : ℕ) :
    oddDesignatedSummandsCount (32 * n + 28) ≡ 0 [ZMOD 8]

/-- **$\mathrm{PD}_2(64n + 56)$ is divisible by 8.** Write $\mathrm{PD}_2(m)$ for the number of
partitions of $m$ with designated summands in which every part is odd. For every natural number $n$,
$\mathrm{PD}_2(64n + 56) \equiv 0 \pmod 8$.

Source: James A. Sellers, *New Infinite Families of Congruences Modulo Powers of 2 for 2-Regular
Partitions with Designated Summands*, INTEGERS 24 (2024), Article A16, Theorem 12
(`integers-2024-A16-thm-12`). -/
public theorem_wanted oddDesignatedSummandsCount_sixtyFour_mul_add_fiftySix (n : ℕ) :
    oddDesignatedSummandsCount (64 * n + 56) ≡ 0 [ZMOD 8]

/-- **Internal congruence $\mathrm{PD}_2(16n) \equiv \mathrm{PD}_2(4n) \pmod 8$.** Write
$\mathrm{PD}_2(m)$ for the number of partitions of $m$ with designated summands in which every part
is odd. For every natural number $n$, $\mathrm{PD}_2(16n) \equiv \mathrm{PD}_2(4n) \pmod 8$.

Source: James A. Sellers, *New Infinite Families of Congruences Modulo Powers of 2 for 2-Regular
Partitions with Designated Summands*, INTEGERS 24 (2024), Article A16, Theorem 13
(`integers-2024-A16-thm-13`). -/
public theorem_wanted oddDesignatedSummandsCount_sixteen_mul_mod_eight (n : ℕ) :
    oddDesignatedSummandsCount (16 * n) ≡ oddDesignatedSummandsCount (4 * n) [ZMOD 8]

/-- **$PD_2(48n+26)$ is divisible by 4.** Let $PD_2(n)$ be the number of partitions of $n$ with
designated summands in which every part is odd. For every $n \ge 0$,
$PD_2(48n + 26) \equiv 0 \pmod 4$.

Source: James A. Sellers, *New Infinite Families of Congruences Modulo Powers of 2 for 2-Regular
Partitions with Designated Summands*, INTEGERS 24 (2024), Article A16, Theorem 14
(`integers-2024-A16-thm-14`). -/
public theorem_wanted oddDesignatedSummandsCount_fortyEight_mul_add_twentySix (n : ℕ) :
    oddDesignatedSummandsCount (48 * n + 26) ≡ 0 [ZMOD 4]

end

end MetaMathlibExt
