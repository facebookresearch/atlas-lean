/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Congruences for generalized Frobenius partitions with 4 repetitions

Statements from Bipul Kumar Sarmah and Satyajit Gayan, *Congruences for F-partitions with 4
Repetitions*, INTEGERS 25 (2025), Article A17.

A generalized Frobenius partition (F-partition) of `n` is a two-rowed array of nonnegative
integers with `r` columns whose rows are nonincreasing and with `n = r + Σ aᵢ + Σ bᵢ`.
`φ_k(n)` counts those F-partitions of `n` in which no integer appears more than `k` times in
either row (Andrews); the paper studies `φ₄`.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Fintype.Pi
public import MathlibExt.Combinatorics.Enumerative.Partition.QEulerProduct
public import MathlibExt.NumberTheory.ModularForms.JacobiTheta.Ramanujan

open PowerSeries

namespace MetaMathlibExt

@[expose] public section

local notation "𝔣" => qEulerProduct

/-- **Frobenius partitions with at most $k$ repetitions.** For natural numbers $k$ and $n$,
$\varphi_k(n)$ is the number of generalized Frobenius partitions of $n$ in which each integer
appears at most $k$ times in each row. Concretely, $\varphi_k(n)$ is the number of pairs of
functions $m_1, m_2 \colon \{0, 1, \dots, n\} \to \{0, 1, \dots, k\}$ with
$\sum_i m_1(i) = \sum_i m_2(i)$ and $\sum_i (i + 1)\, m_1(i) + \sum_i i\, m_2(i) = n$.

Here a generalized Frobenius partition of $n$ is a two-rowed array of nonnegative integers with
$r$ columns, both rows nonincreasing, whose entries sum to $n - r$; its entries are at most $n$,
and $m_1(i)$, $m_2(i)$ count how often $i$ appears in the top and bottom rows.

Source: Bipul Kumar Sarmah and Satyajit Gayan, *Congruences for F-partitions with 4
Repetitions*, INTEGERS 25 (2025), Article A17, Section 1 (definition of `φ_k(n)`, after
Andrews). -/
public def frobeniusPartitionRepCount (k n : ℕ) : ℕ :=
  ((Finset.univ : Finset ((Fin (n + 1) → Fin (k + 1)) × (Fin (n + 1) → Fin (k + 1)))).filter
    fun p => ∑ i : Fin (n + 1), (p.1 i : ℕ) = ∑ i : Fin (n + 1), (p.2 i : ℕ) ∧
      ∑ i : Fin (n + 1), (p.1 i : ℕ) * ((i : ℕ) + 1) +
        ∑ i : Fin (n + 1), (p.2 i : ℕ) * (i : ℕ) = n).card

/-- **Initial values of $\varphi_4$.** Let $\varphi_4(n)$ be the number of generalized Frobenius
partitions of $n$ in which each integer appears at most $4$ times in each row. Then
$\varphi_4(0) = 1$ (the empty array) and $\varphi_4(1) = 1$ (the single column with both entries
$0$).

Source: Bipul Kumar Sarmah and Satyajit Gayan, *Congruences for F-partitions with 4
Repetitions*, INTEGERS 25 (2025), Article A17, Section 1 (definition of `φ_k(n)`). -/
public theorem frobeniusPartitionRepCount_four_zero_one :
    frobeniusPartitionRepCount 4 0 = 1 ∧ frobeniusPartitionRepCount 4 1 = 1 := by
  constructor <;> decide +kernel

/-- **$\varphi_4(4n+3)$ is even.** Let $\varphi_4(n)$ be the number of generalized Frobenius
partitions of $n$ in which each integer appears at most $4$ times in each row. For every natural
number $n$, $\varphi_4(4n + 3) \equiv 0 \pmod 2$.

Source: Bipul Kumar Sarmah and Satyajit Gayan, *Congruences for F-partitions with 4
Repetitions*, INTEGERS 25 (2025), Article A17, Theorem 2 (`integers-2025-A17-thm-2`). -/
public theorem_wanted frobeniusPartitionRepCount_four_four_mul_add_three_mod_two (n : ℕ) :
    frobeniusPartitionRepCount 4 (4 * n + 3) ≡ 0 [MOD 2]

/-- **$\varphi_4(2N+1)$ is even when $5 \nmid N$.** Let $\varphi_4(n)$ be the number of generalized
Frobenius partitions of $n$ in which each integer appears at most $4$ times in each row. For every
positive integer $N$ not divisible by $5$, $\varphi_4(2N + 1) \equiv 0 \pmod 2$.

Source: Bipul Kumar Sarmah and Satyajit Gayan, *Congruences for F-partitions with 4
Repetitions*, INTEGERS 25 (2025), Article A17, Theorem 3 (`integers-2025-A17-thm-3`). -/
public theorem_wanted frobeniusPartitionRepCount_four_two_mul_add_one_mod_two {N : ℕ}
    (hN : 0 < N) (h5 : ¬ 5 ∣ N) :
    frobeniusPartitionRepCount 4 (2 * N + 1) ≡ 0 [MOD 2]

/-- **Parity of $\varphi_4(4n+1)$.** Let $\varphi_4(n)$ be the number of generalized Frobenius
partitions of $n$ in which each integer appears at most $4$ times in each row. For every natural
number $n$, $\varphi_4(4n + 1)$ is odd if and only if $2n = 5k(3k + 1)$ for some integer $k$,
that is, $n = 5k(3k \pm 1)/2$ for some integer $k$.

Source: Bipul Kumar Sarmah and Satyajit Gayan, *Congruences for F-partitions with 4
Repetitions*, INTEGERS 25 (2025), Article A17, Theorem 4 (`integers-2025-A17-thm-4`). -/
public theorem_wanted frobeniusPartitionRepCount_four_four_mul_add_one_mod_two (n : ℕ) :
    frobeniusPartitionRepCount 4 (4 * n + 1) % 2 = 1 ↔
      ∃ k : ℤ, 2 * (n : ℤ) = 5 * k * (3 * k + 1)

/-- **$\varphi_4(10n+6)$ is divisible by $5$.** Let $\varphi_4(n)$ be the number of generalized
Frobenius partitions of $n$ in which each integer appears at most $4$ times in each row. For every
natural number $n$, $\varphi_4(10n + 6) \equiv 0 \pmod 5$.

Source: Bipul Kumar Sarmah and Satyajit Gayan, *Congruences for F-partitions with 4
Repetitions*, INTEGERS 25 (2025), Article A17, Theorem 5 (`integers-2025-A17-thm-5`). -/
public theorem_wanted frobeniusPartitionRepCount_four_ten_mul_add_six_mod_five (n : ℕ) :
    frobeniusPartitionRepCount 4 (10 * n + 6) ≡ 0 [MOD 5]

/-- **$\varphi_4(10n+1)$ modulo $5$.** Let $\varphi_4(n)$ be the number of generalized Frobenius
partitions of $n$ in which each integer appears at most $4$ times in each row, and let $n$ be a
natural number. If $n = k(3k + 1)$ for an integer $k$, then
$\varphi_4(10n + 1) \equiv k + 1 \pmod 5$; if there is no such integer $k$, then
$\varphi_4(10n + 1) \equiv 0 \pmod 5$.

Source: Bipul Kumar Sarmah and Satyajit Gayan, *Congruences for F-partitions with 4
Repetitions*, INTEGERS 25 (2025), Article A17, Theorem 6 (`integers-2025-A17-thm-6`). -/
public theorem_wanted frobeniusPartitionRepCount_four_ten_mul_add_one_mod_five (n : ℕ) :
    (∀ k : ℤ, (n : ℤ) = k * (3 * k + 1) →
        (frobeniusPartitionRepCount 4 (10 * n + 1) : ℤ) ≡ k + 1 [ZMOD 5]) ∧
      ((¬ ∃ k : ℤ, (n : ℤ) = k * (3 * k + 1)) →
        frobeniusPartitionRepCount 4 (10 * n + 1) ≡ 0 [MOD 5])

/-- **The 2-dissection of the generating function of $\varphi_4$.** Let $\varphi_4(n)$ be the
number of generalized Frobenius partitions of $n$ in which each integer appears at most $4$ times
in each row, and let $f_k = \prod_{m \ge 1} (1 - q^{km})$ in the ring of integer power series in
$q$. Then
$$f_1^{12} f_4^4 f_5 f_{10}^2 \sum_{n \ge 0} \varphi_4(2n)\, q^n =
f_1^3 f_2^{10} f_4^2 f_5^2 f_{10} + 2q f_2^{15} f_5 f_{20}^2 - 8q f_1^5 f_4^{10} f_{10}^3$$
and
$$f_1^6 f_4^2 f_5^2 \sum_{n \ge 0} \varphi_4(2n + 1)\, q^n = f_2^7 f_{10}^2.$$

Dividing by the Euler products on the left gives the quotient forms of the source, for example
$\sum_{n \ge 0} \varphi_4(2n + 1)\, q^n = f_2^7 f_{10}^2 / (f_1^6 f_4^2 f_5^2)$.

Source: Bipul Kumar Sarmah and Satyajit Gayan, *Congruences for F-partitions with 4
Repetitions*, INTEGERS 25 (2025), Article A17, Theorem 1, eqs. (3) and (4)
(`integers-2025-A17-thm-1`). -/
public theorem_wanted frobeniusPartitionRepCount_four_two_dissection :
    𝔣 1 ^ 12 * 𝔣 4 ^ 4 * 𝔣 5 * 𝔣 10 ^ 2 *
        PowerSeries.mk (fun n => (frobeniusPartitionRepCount 4 (2 * n) : ℤ)) =
      𝔣 1 ^ 3 * 𝔣 2 ^ 10 * 𝔣 4 ^ 2 * 𝔣 5 ^ 2 * 𝔣 10 + 2 * X * 𝔣 2 ^ 15 * 𝔣 5 * 𝔣 20 ^ 2
        - 8 * X * 𝔣 1 ^ 5 * 𝔣 4 ^ 10 * 𝔣 10 ^ 3 ∧
    𝔣 1 ^ 6 * 𝔣 4 ^ 2 * 𝔣 5 ^ 2 *
        PowerSeries.mk (fun n => (frobeniusPartitionRepCount 4 (2 * n + 1) : ℤ)) =
      𝔣 2 ^ 7 * 𝔣 10 ^ 2

/-- **Ramanujan's theta product identity for $ab = cd$.** Let
$f(a,b) = \sum_{n \in \mathbb{Z}} a^{n(n+1)/2} b^{n(n-1)/2}$ be Ramanujan's general theta
function. If $a, b, c, d$ are complex numbers with $a \ne 0$, $|ab| < 1$ and $ab = cd$, then
$$f(a,b)\,f(c,d) = f(ad,bc)\,f(ac,bd) + a\,f(c/a, a^2bd)\,f(d/a, a^2bc).$$

In each of the six theta functions the two arguments have product of modulus $|ab|$ or
$|ab|^2$, which is less than $1$, so every series converges.

Source: Bipul Kumar Sarmah and Satyajit Gayan, *Congruences for F-partitions with 4
Repetitions*, INTEGERS 25 (2025), Article A17, Lemma 1, eq. (12), quoting
Berndt, *Ramanujan's Notebooks, Part III*, p. 45, Entry 29 (`integers-2025-A17-lem-1`). -/
public theorem_wanted ramanujanTheta_mul_of_mul_eq {a b c d : ℂ} (ha : a ≠ 0)
    (hab : ‖a * b‖ < 1) (h : a * b = c * d) :
    ramanujanThetaRaw a b * ramanujanThetaRaw c d =
      ramanujanThetaRaw (a * d) (b * c) * ramanujanThetaRaw (a * c) (b * d) +
        a * ramanujanThetaRaw (c / a) (a ^ 2 * b * d) *
          ramanujanThetaRaw (d / a) (a ^ 2 * b * c)

/-- **A 2-dissection of the reciprocal Euler product of levels 1 and 5.** Let
$f_k = \prod_{m \ge 1} (1 - q^{km})$ in the ring of integer power series in $q$. Then
$$f_2^{10} f_8^2 f_{10}^3 f_{20} = f_1^3 f_2^3 f_4^4 f_5 f_8^2 f_{10}^2 f_{20} -
2q f_1^3 f_2 f_4^6 f_5 f_8^2 f_{20}^3 + 5q f_1^3 f_2^2 f_4^3 f_5 f_8^2 f_{10}^3 f_{20}^2 +
2q^2 f_1^3 f_4^9 f_5 f_{10} f_{40}^2.$$

Dividing both sides by $f_1^3 f_5 f_2^{10} f_8^2 f_{10}^3 f_{20}$ gives the form in the source,
$1/(f_1^3 f_5) = f_4^4/(f_2^7 f_{10}) - 2q f_4^6 f_{20}^2/(f_2^9 f_{10}^3) +
5q f_4^3 f_{20}/f_2^8 + 2q^2 f_4^9 f_{40}^2/(f_2^{10} f_8^2 f_{10}^2 f_{20})$.

Source: Bipul Kumar Sarmah and Satyajit Gayan, *Congruences for F-partitions with 4
Repetitions*, INTEGERS 25 (2025), Article A17, Lemma 4, eq. (15)
(`integers-2025-A17-lem-4`). -/
public theorem_wanted one_div_f1_cube_f5_two_dissection :
    𝔣 2 ^ 10 * 𝔣 8 ^ 2 * 𝔣 10 ^ 3 * 𝔣 20 =
      𝔣 1 ^ 3 * 𝔣 2 ^ 3 * 𝔣 4 ^ 4 * 𝔣 5 * 𝔣 8 ^ 2 * 𝔣 10 ^ 2 * 𝔣 20
        - 2 * X * 𝔣 1 ^ 3 * 𝔣 2 * 𝔣 4 ^ 6 * 𝔣 5 * 𝔣 8 ^ 2 * 𝔣 20 ^ 3
        + 5 * X * 𝔣 1 ^ 3 * 𝔣 2 ^ 2 * 𝔣 4 ^ 3 * 𝔣 5 * 𝔣 8 ^ 2 * 𝔣 10 ^ 3 * 𝔣 20 ^ 2
        + 2 * X ^ 2 * 𝔣 1 ^ 3 * 𝔣 4 ^ 9 * 𝔣 5 * 𝔣 10 * 𝔣 40 ^ 2

/-- **A level-10 Euler-product identity.** Let $f_k = \prod_{m \ge 1} (1 - q^{km})$ in the ring of
integer power series in $q$. Then
$f_2^5 f_5^2 = f_1^5 f_5 f_{10} + 5q f_1^2 f_2 f_{10}^4$.

Dividing both sides by $f_1^5 f_2^2 f_{10}^2$ gives the form in the source,
$f_2^3 f_5^2/(f_1^5 f_{10}^2) = f_5/(f_2^2 f_{10}) + 5q f_{10}^2/(f_1^3 f_2)$.

Source: Bipul Kumar Sarmah and Satyajit Gayan, *Congruences for F-partitions with 4
Repetitions*, INTEGERS 25 (2025), Article A17, Lemma 5, eq. (17)
(`integers-2025-A17-lem-5`). -/
public theorem_wanted f2_cube_f5_sq_quotient_identity :
    𝔣 2 ^ 5 * 𝔣 5 ^ 2 = 𝔣 1 ^ 5 * 𝔣 5 * 𝔣 10 + 5 * X * 𝔣 1 ^ 2 * 𝔣 2 * 𝔣 10 ^ 4

end

end MetaMathlibExt
