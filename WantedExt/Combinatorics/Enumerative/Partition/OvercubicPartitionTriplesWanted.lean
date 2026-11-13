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
# Congruences for overcubic partition triples

Statements from S. Shivaprasada Nayaka, B. N. Dharmendra, and M. C. Mahesh Kumar,
*Divisibility Properties for Overcubic Partition Triples*, INTEGERS 24 (2024), Article A80.

`bt(n)` counts overcubic partition triples of `n`: ordered triples of overcubic partitions
(Kim's overlined cubic partitions) with total size `n`. Its generating function is
`∑ bt(n) q^n = f_4^3 / (f_1^6 f_2^3)`, where `f_k = (q^k; q^k)_∞` is `qEulerProduct k`,
written `𝔣 k` below. We define `bt(n)` as the `n`th coefficient of that quotient in `ℤ⟦X⟧`
(the denominator has constant coefficient `1`, so it is a unit). The paper's `E_k` is `f_k`.
Products of `f_k` are stated with denominators cleared.
-/

open PowerSeries
open scoped PowerSeries.WithPiTopology

namespace MetaMathlibExt

@[expose] public section

local notation "𝔣" => qEulerProduct

/-- **The overcubic partition triple series.** The generating function of overcubic partition
triples is the integer power series $f_4^3 / (f_1^6 f_2^3)$ in $q$, where
$f_k = \prod_{j \ge 1} (1 - q^{kj})$; the inverse of $f_1^6 f_2^3$ exists because its constant
coefficient is $1$.

Source: S. Shivaprasada Nayaka, B. N. Dharmendra, and M. C. Mahesh Kumar, *Divisibility
Properties for Overcubic Partition Triples*, INTEGERS 24 (2024), Article A80, Section 1; the
same generating function is quoted from this paper by Saikia and Sarma (arXiv:2411.00013,
eq. (2)) and by Chen, Jin, and Yao (arXiv:2504.06941, eq. (1.1)). -/
noncomputable def overcubicTripleSeries : ℤ⟦X⟧ :=
  𝔣 4 ^ 3 * invOfUnit (𝔣 1 ^ 6 * 𝔣 2 ^ 3) 1

/-- **Number of overcubic partition triples.** For a natural number $n$, $\mathrm{bt}(n)$, the
number of overcubic partition triples of $n$, is defined as the integer coefficient of $q^n$ in
the power series $f_4^3 / (f_1^6 f_2^3)$, where $f_k = \prod_{j \ge 1} (1 - q^{kj})$.

Source: S. Shivaprasada Nayaka, B. N. Dharmendra, and M. C. Mahesh Kumar, *Divisibility
Properties for Overcubic Partition Triples*, INTEGERS 24 (2024), Article A80, Section 1. -/
noncomputable def overcubicTripleCount (n : ℕ) : ℤ :=
  coeff n overcubicTripleSeries

/-- **Generating function for overcubic partition triples.** For $k \ge 1$ let
$f_k = \prod_{m \ge 1} (1 - q^{km})$, and let $\mathrm{bt}(n)$, the number of overcubic partition
triples of $n$, be the coefficient of $q^n$ in $f_4^3/(f_1^6 f_2^3)$. Then, as integer power
series in $q$,
$$f_1^6 f_2^3 \sum_{n \ge 0} \mathrm{bt}(n) q^n = f_4^3.$$

Source: S. Shivaprasada Nayaka, B. N. Dharmendra, and M. C. Mahesh Kumar, *Divisibility
Properties for Overcubic Partition Triples*, INTEGERS 24 (2024), Article A80, Section 1. -/
theorem overcubicTripleCount_generatingFunction :
    𝔣 1 ^ 6 * 𝔣 2 ^ 3 * PowerSeries.mk overcubicTripleCount = 𝔣 4 ^ 3 := by
  have hmk : PowerSeries.mk overcubicTripleCount = overcubicTripleSeries := by
    ext n
    simp [overcubicTripleCount]
  have hc : constantCoeff (𝔣 1 ^ 6 * 𝔣 2 ^ 3) = ((1 : ℤˣ) : ℤ) := by
    simp [constantCoeff_qEulerProduct (le_refl 1),
      constantCoeff_qEulerProduct (by norm_num : 1 ≤ 2)]
  rw [hmk, overcubicTripleSeries, mul_left_comm, mul_invOfUnit _ _ hc, mul_one]

/-- **Overcubic partition triples of $0$.** The number $\mathrm{bt}(0)$ of overcubic partition
triples of $0$ equals $1$.

Source: S. Shivaprasada Nayaka, B. N. Dharmendra, and M. C. Mahesh Kumar, *Divisibility
Properties for Overcubic Partition Triples*, INTEGERS 24 (2024), Article A80, Section 1. -/
theorem overcubicTripleCount_zero : overcubicTripleCount 0 = 1 := by
  have h := congrArg (coeff 0) overcubicTripleCount_generatingFunction
  simp only [coeff_zero_eq_constantCoeff, map_mul, map_pow,
    constantCoeff_qEulerProduct (le_refl 1), constantCoeff_qEulerProduct (by norm_num : 1 ≤ 2),
    constantCoeff_qEulerProduct (by norm_num : 1 ≤ 4), one_pow, one_mul] at h
  simpa using h

/-- **The 2-dissection of $f_1^2$.** For $k \ge 1$ let $f_k = \prod_{m \ge 1} (1 - q^{km})$, an
integer power series in $q$. Then
$$f_1^2 f_4^2 f_8 f_{16}^2 = f_2 f_8^6 - 2 q f_2 f_4^2 f_{16}^4.$$
Dividing by $f_4^2 f_8 f_{16}^2$ gives
$f_1^2 = \frac{f_2 f_8^5}{f_4^2 f_{16}^2} - 2q \frac{f_2 f_{16}^2}{f_8}$.

Source: S. Shivaprasada Nayaka, B. N. Dharmendra, and M. C. Mahesh Kumar, *Divisibility
Properties for Overcubic Partition Triples*, INTEGERS 24 (2024), Article A80, Lemma 1, eq. (39)
(`integers-2024-A80-lem-1`). -/
public theorem_wanted f1_sq_two_dissection :
    𝔣 1 ^ 2 * 𝔣 4 ^ 2 * 𝔣 8 * 𝔣 16 ^ 2 =
      𝔣 2 * 𝔣 8 ^ 6 - 2 * X * 𝔣 2 * 𝔣 4 ^ 2 * 𝔣 16 ^ 4

/-- **The 2-dissection of $1/f_1^2$.** For $k \ge 1$ let
$f_k = \prod_{m \ge 1} (1 - q^{km})$, an integer power series in $q$. Then
$$f_2^5 f_8 f_{16}^2 = f_1^2 f_8^6 + 2 q f_1^2 f_4^2 f_{16}^4.$$
Dividing by $f_1^2 f_2^5 f_8 f_{16}^2$ gives
$\frac{1}{f_1^2} = \frac{f_8^5}{f_2^5 f_{16}^2} + 2q \frac{f_4^2 f_{16}^2}{f_2^5 f_8}$.

Source: S. Shivaprasada Nayaka, B. N. Dharmendra, and M. C. Mahesh Kumar, *Divisibility
Properties for Overcubic Partition Triples*, INTEGERS 24 (2024), Article A80, Lemma 1, eq. (40)
(`integers-2024-A80-lem-1`). -/
public theorem_wanted one_div_f1_sq_two_dissection :
    𝔣 2 ^ 5 * 𝔣 8 * 𝔣 16 ^ 2 =
      𝔣 1 ^ 2 * 𝔣 8 ^ 6 + 2 * X * 𝔣 1 ^ 2 * 𝔣 4 ^ 2 * 𝔣 16 ^ 4

/-- **The 3-dissection of $f_1^3$.** For $k \ge 1$ let $f_k = \prod_{m \ge 1} (1 - q^{km})$, an
integer power series in $q$. Then
$$
f_1^3 f_3 f_6^2 f_9^3 f_{18}^3 = f_6^3 f_9^9 + 4 q^3 f_3^3 f_{18}^9 - 3 q f_3 f_6^2 f_9^6 f_{18}^3.
$$
Dividing by $f_3 f_6^2 f_9^3 f_{18}^3$ gives
$f_1^3 = \frac{f_6 f_9^6}{f_3 f_{18}^3} + 4q^3 \frac{f_3^2 f_{18}^6}{f_6^2 f_9^3} - 3q f_9^3$.

Source: S. Shivaprasada Nayaka, B. N. Dharmendra, and M. C. Mahesh Kumar, *Divisibility
Properties for Overcubic Partition Triples*, INTEGERS 24 (2024), Article A80, Lemma 2, eq. (41)
(merged into the record `integers-2024-A80-lem-1`). -/
public theorem_wanted f1_cube_three_dissection :
    𝔣 1 ^ 3 * 𝔣 3 * 𝔣 6 ^ 2 * 𝔣 9 ^ 3 * 𝔣 18 ^ 3 =
      𝔣 6 ^ 3 * 𝔣 9 ^ 9 + 4 * X ^ 3 * 𝔣 3 ^ 3 * 𝔣 18 ^ 9
        - 3 * X * 𝔣 3 * 𝔣 6 ^ 2 * 𝔣 9 ^ 6 * 𝔣 18 ^ 3

/-- **Congruences for overcubic partition triples at odd arguments.** Let $\mathrm{bt}(n)$ be the
number of overcubic partition triples of $n$. For all natural numbers $n$ and $\alpha$,
$\mathrm{bt}(8n+7)$ is divisible by $32$, and each of $\mathrm{bt}(8n+5)$, $\mathrm{bt}(72n+33)$,
$\mathrm{bt}(72n+57)$ and $\mathrm{bt}(8 \cdot 9^{\alpha+2} n + 33 \cdot 9^{\alpha+1})$ is divisible
by $8$.

Source: S. Shivaprasada Nayaka, B. N. Dharmendra, and M. C. Mahesh Kumar, *Divisibility
Properties for Overcubic Partition Triples*, INTEGERS 24 (2024), Article A80, Theorem 1,
eqs. (2)-(6) (`integers-2024-A80-thm-1`). -/
public theorem_wanted overcubicTripleCount_congruences_odd_args (n α : ℕ) :
    overcubicTripleCount (8 * n + 7) ≡ 0 [ZMOD 32] ∧
      overcubicTripleCount (8 * n + 5) ≡ 0 [ZMOD 8] ∧
      overcubicTripleCount (72 * n + 33) ≡ 0 [ZMOD 8] ∧
      overcubicTripleCount (72 * n + 57) ≡ 0 [ZMOD 8] ∧
      overcubicTripleCount (8 * 9 ^ (α + 2) * n + 33 * 9 ^ (α + 1)) ≡ 0 [ZMOD 8]

/-- **Overcubic partition triples of $24n+1$ modulo $4$.** For $k \ge 1$ let
$f_k = \prod_{j \ge 1} (1 - q^{kj})$, and let $\mathrm{bt}(m)$ be the number of overcubic
partition triples of $m$, the coefficient of $q^m$ in $f_4^3 / (f_1^6 f_2^3)$. For every natural
number $n$, $\mathrm{bt}(24n+1) \equiv 2 c_n \pmod 4$, where $c_n$ is the coefficient of $q^n$
in $f_1$; equivalently, $\sum_{n \ge 0} \mathrm{bt}(24n+1) q^n \equiv 2 f_1 \pmod 4$
coefficientwise.

This is the case $\alpha = 0$ of the paper's statement.

Source: S. Shivaprasada Nayaka, B. N. Dharmendra, and M. C. Mahesh Kumar, *Divisibility
Properties for Overcubic Partition Triples*, INTEGERS 24 (2024), Article A80, Theorem 2,
eq. (7), case `α = 0` (`integers-2024-A80-thm-2`). -/
public theorem_wanted overcubicTripleCount_twentyFour_mul_add_one (n : ℕ) :
    overcubicTripleCount (24 * n + 1) ≡ 2 * coeff n (𝔣 1) [ZMOD 4]

/-- **Congruences for overcubic partition triples at arguments congruent to 2 modulo 4.** Let
$\mathrm{bt}(n)$ be the number of overcubic partition triples of $n$. For all natural numbers $n$
and $\alpha$, both $\mathrm{bt}(16n+14)$ and $\mathrm{bt}(16n+10)$ are divisible by $16$; each of
$\mathrm{bt}(144n+66)$, $\mathrm{bt}(144n+114)$, $\mathrm{bt}(1296n+594)$, $\mathrm{bt}(1296n+1026)$
and $\mathrm{bt}(16 \cdot 9^{\alpha+3} n + 66 \cdot 9^{\alpha+2})$ is divisible by $8$; and
$\mathrm{bt}(432n+306) \equiv \mathrm{bt}(48n+34) \pmod 8$.

The paper's congruence (16), $\mathrm{bt}(432n+18) \equiv \mathrm{bt}(48n+2) \pmod 8$, is omitted:
it fails at $n = 0$.

Source: S. Shivaprasada Nayaka, B. N. Dharmendra, and M. C. Mahesh Kumar, *Divisibility
Properties for Overcubic Partition Triples*, INTEGERS 24 (2024), Article A80, Theorem 4,
eqs. (9)-(15) and (17) (`integers-2024-A80-thm-4`). -/
public theorem_wanted overcubicTripleCount_congruences_two_mod_four_args (n α : ℕ) :
    overcubicTripleCount (16 * n + 14) ≡ 0 [ZMOD 16] ∧
      overcubicTripleCount (16 * n + 10) ≡ 0 [ZMOD 16] ∧
      overcubicTripleCount (144 * n + 66) ≡ 0 [ZMOD 8] ∧
      overcubicTripleCount (144 * n + 114) ≡ 0 [ZMOD 8] ∧
      overcubicTripleCount (1296 * n + 594) ≡ 0 [ZMOD 8] ∧
      overcubicTripleCount (1296 * n + 1026) ≡ 0 [ZMOD 8] ∧
      overcubicTripleCount (16 * 9 ^ (α + 3) * n + 66 * 9 ^ (α + 2)) ≡ 0 [ZMOD 8] ∧
      overcubicTripleCount (432 * n + 306) ≡ overcubicTripleCount (48 * n + 34) [ZMOD 8]

/-- **Congruences for overcubic partition triples at multiples of 4.** Let $\mathrm{bt}(n)$ be the
number of overcubic partition triples of $n$. For all natural numbers $n$ and $\alpha$, both
$\mathrm{bt}(32n+28)$ and $\mathrm{bt}(32n+20)$ are divisible by $16$, and each of
$\mathrm{bt}(64n+56)$, $\mathrm{bt}(576n+408)$, $\mathrm{bt}(5184n+216)$, $\mathrm{bt}(5184n+3672)$
and $\mathrm{bt}(64 \cdot 81^{\alpha+2} n + 216 \cdot 81^{\alpha+1})$ is divisible by $8$.

Source: S. Shivaprasada Nayaka, B. N. Dharmendra, and M. C. Mahesh Kumar, *Divisibility
Properties for Overcubic Partition Triples*, INTEGERS 24 (2024), Article A80, Theorem 5,
eqs. (18)-(24) (`integers-2024-A80-thm-5`). -/
public theorem_wanted overcubicTripleCount_congruences_four_mul_args (n α : ℕ) :
    overcubicTripleCount (32 * n + 28) ≡ 0 [ZMOD 16] ∧
      overcubicTripleCount (32 * n + 20) ≡ 0 [ZMOD 16] ∧
      overcubicTripleCount (64 * n + 56) ≡ 0 [ZMOD 8] ∧
      overcubicTripleCount (576 * n + 408) ≡ 0 [ZMOD 8] ∧
      overcubicTripleCount (5184 * n + 216) ≡ 0 [ZMOD 8] ∧
      overcubicTripleCount (5184 * n + 3672) ≡ 0 [ZMOD 8] ∧
      overcubicTripleCount (64 * 81 ^ (α + 2) * n + 216 * 81 ^ (α + 1)) ≡ 0 [ZMOD 8]

/-- **Overcubic partition triples of $576n+24$ modulo 8.** Let $\mathrm{bt}(n)$ be the number of
overcubic partition triples of $n$, and let $f_1 = \prod_{m \ge 1} (1 - q^m)$. For every natural
number $n$, $\mathrm{bt}(576n+24) \equiv 4 c_n \pmod 8$, where $c_n$ is the coefficient of $q^n$
in $f_1$; that is, $\sum_{n \ge 0} \mathrm{bt}(576n+24) q^n \equiv 4 f_1 \pmod 8$.

This is the $\alpha = 0$ case of the paper's statement.

Source: S. Shivaprasada Nayaka, B. N. Dharmendra, and M. C. Mahesh Kumar, *Divisibility
Properties for Overcubic Partition Triples*, INTEGERS 24 (2024), Article A80, Theorem 6,
eq. (25), case `α = 0` (`integers-2024-A80-thm-6`). -/
public theorem_wanted overcubicTripleCount_fiveHundredSeventySix_mul_add_twentyFour (n : ℕ) :
    overcubicTripleCount (576 * n + 24) ≡ 4 * coeff n (𝔣 1) [ZMOD 8]

/-- **Congruences for overcubic partition triples at arguments congruent to 8 modulo 16.** Let
$\mathrm{bt}(n)$ be the number of overcubic partition triples of $n$. For all natural numbers $n$
and $\alpha$, each of $\mathrm{bt}(64n+40)$, $\mathrm{bt}(576n+264)$, $\mathrm{bt}(576n+456)$ and
$\mathrm{bt}(64 \cdot 9^{\alpha+2} n + 264 \cdot 9^{\alpha+1})$ is divisible by $8$.

Source: S. Shivaprasada Nayaka, B. N. Dharmendra, and M. C. Mahesh Kumar, *Divisibility
Properties for Overcubic Partition Triples*, INTEGERS 24 (2024), Article A80, Theorem 8,
eqs. (27)-(30) (`integers-2024-A80-thm-8`). -/
public theorem_wanted overcubicTripleCount_congruences_eight_mod_sixteen_args (n α : ℕ) :
    overcubicTripleCount (64 * n + 40) ≡ 0 [ZMOD 8] ∧
      overcubicTripleCount (576 * n + 264) ≡ 0 [ZMOD 8] ∧
      overcubicTripleCount (576 * n + 456) ≡ 0 [ZMOD 8] ∧
      overcubicTripleCount (64 * 9 ^ (α + 2) * n + 264 * 9 ^ (α + 1)) ≡ 0 [ZMOD 8]

/-- **Overcubic partition triples of $192n+8$ modulo $4$.** For $k \ge 1$ let
$f_k = \prod_{j \ge 1} (1 - q^{kj})$, and let $\mathrm{bt}(m)$ be the number of overcubic
partition triples of $m$, the coefficient of $q^m$ in $f_4^3 / (f_1^6 f_2^3)$. For every natural
number $n$, $\mathrm{bt}(192n+8) \equiv 2 c_n \pmod 4$, where $c_n$ is the coefficient of $q^n$
in $f_1$; equivalently, $\sum_{n \ge 0} \mathrm{bt}(192n+8) q^n \equiv 2 f_1 \pmod 4$
coefficientwise.

This is the case $\alpha = 0$ of the paper's statement.

Source: S. Shivaprasada Nayaka, B. N. Dharmendra, and M. C. Mahesh Kumar, *Divisibility
Properties for Overcubic Partition Triples*, INTEGERS 24 (2024), Article A80, Theorem 9,
eq. (31), case `α = 0` (`integers-2024-A80-thm-9`). -/
public theorem_wanted overcubicTripleCount_oneHundredNinetyTwo_mul_add_eight (n : ℕ) :
    overcubicTripleCount (192 * n + 8) ≡ 2 * coeff n (𝔣 1) [ZMOD 4]

/-- **Congruences for overcubic partition triples at multiples of 16.** Let $\mathrm{bt}(n)$ be the
number of overcubic partition triples of $n$. For all natural numbers $n$ and $\alpha$, each of
$\mathrm{bt}(64n+48)$, $\mathrm{bt}(128n+80)$, $\mathrm{bt}(128n+96)$, $\mathrm{bt}(256n+160)$ and
$\mathrm{bt}(256 \cdot 2^{\alpha} n + 192)$ is divisible by $4$, and
$\mathrm{bt}(256n+32) \equiv \mathrm{bt}(128n+16) \pmod 4$.

Source: S. Shivaprasada Nayaka, B. N. Dharmendra, and M. C. Mahesh Kumar, *Divisibility
Properties for Overcubic Partition Triples*, INTEGERS 24 (2024), Article A80, Theorem 11,
eqs. (33)-(38) (`integers-2024-A80-thm-11`). -/
public theorem_wanted overcubicTripleCount_congruences_sixteen_mul_args (n α : ℕ) :
    overcubicTripleCount (64 * n + 48) ≡ 0 [ZMOD 4] ∧
      overcubicTripleCount (128 * n + 80) ≡ 0 [ZMOD 4] ∧
      overcubicTripleCount (128 * n + 96) ≡ 0 [ZMOD 4] ∧
      overcubicTripleCount (256 * n + 160) ≡ 0 [ZMOD 4] ∧
      overcubicTripleCount (256 * n + 32) ≡ overcubicTripleCount (128 * n + 16) [ZMOD 4] ∧
      overcubicTripleCount (256 * 2 ^ α * n + 192) ≡ 0 [ZMOD 4]

end

end MetaMathlibExt
