/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries
public import Mathlib.Data.Fin.Tuple.NatAntidiagonal
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.ModEq
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Regular partition functions and a generalized tau function

Statements from S. Sriram and A. David Christopher, *Congruences Relating Regular Partition
Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*,
INTEGERS 24 (2024), Article A39 (arXiv:2509.26559).

`generalizedTau k n` is the paper's `τ_k(n)`: `q ∏ (1 - q^m)^k = ∑ τ_k(n) q^n` (Definition 1.1),
built from Mathlib's `PowerSeries.pentagonalSeries ℤ = ∏ (1 - X^m)`, a unit of `ℤ⟦X⟧`, so that
negative `k` make sense. Ramanujan's `τ` is `generalizedTau 24`. The `t`-regular partition count
`R_t(n)` is `#(Nat.Partition.restricted n (¬ t ∣ ·))`, `p(n)` is `Fintype.card (Nat.Partition n)`,
and the generalized pentagonal numbers `(3r² ± r)/2` are Mathlib's `pentagonal r`, `r ∈ ℤ`.
-/

namespace MetaMathlibExt

open PowerSeries

@[expose] public section

/-- **Euler's product has constant term $1$.** The constant coefficient of the integer power
series $\prod_{m \ge 1} (1 - X^m)$ in $\mathbb{Z}[[X]]$ is $1$.

Source: Euler's pentagonal number theorem as used in Sriram and Christopher, *Congruences
Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function
Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, identity (1). -/
public theorem constantCoeff_pentagonalSeries_int :
    constantCoeff (pentagonalSeries ℤ) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  have h := coeff_pentagonalSeries_pentagonal (R := ℤ) 0
  have h0 : pentagonal 0 = 0 := by simp [pentagonal_def]
  rw [h0] at h
  simp [h]

/-- **Euler's product is a unit in $\mathbb{Z}[[X]]$.** Euler's pentagonal series
$\sum_{k \in \mathbb{Z}} (-1)^k X^{k(3k - 1)/2}$, which equals $\prod_{m \ge 1} (1 - X^m)$, is a
unit of the ring $\mathbb{Z}[[X]]$ of formal power series with integer coefficients, so all its
integer powers are defined.

Source: Sriram and Christopher, *Congruences Relating Regular Partition Functions, a Generalized
Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article
A39, Definition 1.1 (negative exponents). -/
public theorem isUnit_pentagonalSeries_int : IsUnit (pentagonalSeries ℤ) := by
  rw [isUnit_iff_constantCoeff, constantCoeff_pentagonalSeries_int]
  exact isUnit_one

/-- **Generalized tau function.** For an integer $k$ and a natural number $n$, the generalized tau
function $\tau_k(n)$ is the coefficient of $q^n$ in the integer power series
$q \prod_{m \ge 1} (1 - q^m)^k$. For negative $k$ the power is taken in the group of units of
$\mathbb{Z}[[q]]$, where $\prod_{m \ge 1} (1 - q^m)$ is invertible because its constant term is $1$.

The paper requires $k \ne 0$; $k = 0$ gives $\tau_0(1) = 1$ and $\tau_0(n) = 0$ for $n \ne 1$.
$\tau_{24}$ is Ramanujan's tau function, and $\tau_1(n + 1)$ is Euler's $\omega(n)$, the
coefficient of $q^n$ in $\prod_{m \ge 1} (1 - q^m)$.

Source: Sriram and Christopher, *Congruences Relating Regular Partition Functions, a Generalized
Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article
A39, Definition 1.1, equation (2). -/
public noncomputable def generalizedTau (k : ℤ) (n : ℕ) : ℤ :=
  coeff n (X * ((isUnit_pentagonalSeries_int.unit ^ k : ℤ⟦X⟧ˣ) : ℤ⟦X⟧))

/-- **Generalized tau function at zero.** For every integer $k$, $\tau_k(0) = 0$, where $\tau_k$
is the generalized tau function: the series $q \prod_{m \ge 1} (1 - q^m)^k$ has no constant term.

Source: Sriram and Christopher, INTEGERS 24 (2024), Article A39, Definition 1.1. -/
public theorem generalizedTau_zero (k : ℤ) : generalizedTau k 0 = 0 := by
  simp [generalizedTau]

/-- **The generalized tau function at $1$.** For every integer $k$, $\tau_k(1) = 1$.

Source: Sriram and Christopher, INTEGERS 24 (2024), Article A39, Definition 1.1. -/
public theorem generalizedTau_one (k : ℤ) : generalizedTau k 1 = 1 := by
  rw [generalizedTau, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply]
  have hu : Units.map (constantCoeff (R := ℤ)).toMonoidHom isUnit_pentagonalSeries_int.unit
      = 1 := by
    ext
    simp [constantCoeff_pentagonalSeries_int]
  have h := congrArg (fun u : ℤˣ => (u : ℤ)) (congrArg (· ^ k) hu)
  simp only [one_zpow, Units.val_one, ← map_zpow, Units.coe_map] at h
  exact h

/-- **The generalized tau function for natural exponents.** For natural numbers $k$ and $n$,
$\tau_k(n)$ is the coefficient of $q^n$ in the integer power series
$q \bigl(\prod_{m \ge 1} (1 - q^m)\bigr)^k$.

Source: Sriram and Christopher, INTEGERS 24 (2024), Article A39, Definition 1.1. -/
public theorem generalizedTau_natCast (k n : ℕ) :
    generalizedTau k n = coeff n (X * pentagonalSeries ℤ ^ k) := by
  simp [generalizedTau]

/-- **Partition formulas for the generalized tau function.** Let $k \ge 1$ and $n \ge 0$ be natural
numbers. For a partition $\lambda$ of $n$ and a part $a$ of $\lambda$, write $f_a$ for the number
of times $a$ occurs in $\lambda$. Then
$$\tau_k(n + 1) = \sum_{\lambda} \prod_{a} (-1)^{f_a} \binom{k}{f_a},$$
where $\lambda$ runs over the partitions of $n$ with $f_a \le k$ for every part $a$ and the
product runs over the distinct parts $a$ of $\lambda$, and
$$\tau_{-k}(n + 1) = \sum_{\lambda} \prod_{a} \binom{f_a + k - 1}{k - 1},$$
where $\lambda$ runs over all partitions of $n$ and the product again runs over the distinct parts
$a$ of $\lambda$.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Theorem 1 (`integers-2024-A39-thm-1`). -/
public theorem_wanted generalizedTau_succ_eq_partition_sum (k : ℕ) (hk : 0 < k) (n : ℕ) :
    (generalizedTau k (n + 1) =
        ∑ p ∈ Finset.univ.filter
            (fun p : Nat.Partition n => ∀ a ∈ p.parts, p.parts.count a ≤ k),
          ∏ a ∈ p.parts.toFinset,
            (-1 : ℤ) ^ p.parts.count a * (k.choose (p.parts.count a) : ℤ)) ∧
      (generalizedTau (-(k : ℤ)) (n + 1) =
        ∑ p : Nat.Partition n,
          ∏ a ∈ p.parts.toFinset, ((p.parts.count a + k - 1).choose (k - 1) : ℤ))

/-- **Parity of the generalized tau function via part frequencies.** Let $k \ge 1$ and $n \ge 0$ be
natural numbers, and let $A$ be the set of integers $a$ with $1 \le a \le k$ and $\binom{k}{a}$
odd. Then $\tau_k(n + 1)$ is congruent modulo $2$ to the number of partitions of $n$ in which the
number of times each part occurs lies in $A$.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Theorem 2 (`integers-2024-A39-thm-2`). -/
public theorem_wanted generalizedTau_succ_modEq_card_frequency_two (k : ℕ) (hk : 0 < k) (n : ℕ) :
    generalizedTau k (n + 1) ≡
      ((Finset.univ.filter fun p : Nat.Partition n =>
        ∀ i ∈ p.parts,
          p.parts.count i ∈ (Finset.Icc 1 k).filter (fun a => Odd (k.choose a))).card : ℤ)
      [ZMOD 2]

/-- **Parity of the $4$-regular partition function.** For a positive integer $n$, let $R_4(n)$ be
the number of partitions of $n$ with no part divisible by $4$. Then $R_4(n)$ is odd if and only if
$n$ is a triangular number, that is, $n = m(m + 1)/2$ for some integer $m \ge 0$.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Theorem 3 (`integers-2024-A39-thm-3`). -/
public theorem_wanted odd_card_four_regular_iff_triangular (n : ℕ) (hn : 0 < n) :
    Odd (Nat.Partition.restricted n (¬ 4 ∣ ·)).card ↔ ∃ m : ℕ, n = m * (m + 1) / 2

/-- **Parity of $\tau_{14}$ and $\tau_6$ at odd arguments.** Let $\tau_k(m)$ be the generalized
tau function, the coefficient of $q^m$ in $q \prod_{j \ge 1} (1 - q^j)^k$, and let $R_8(n)$ be
the number of partitions of $n$ in which no part is divisible by $8$. For every positive integer
$n$: (a) $\tau_{14}(2n + 1) \equiv R_8(n) \pmod 2$; (b) $\tau_6(2n + 1)$ is odd if and only if
$n$ is a triangular number, that is, $n = m(m + 1)/2$ for some natural number $m$.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Theorem 4 (`integers-2024-A39-thm-4`). -/
public theorem_wanted generalizedTau_fourteen_six_odd_index_mod_two (n : ℕ) (hn : 0 < n) :
    generalizedTau 14 (2 * n + 1) ≡ ((Nat.Partition.restricted (n) (¬ 8 ∣ ·)).card : ℤ) [ZMOD 2] ∧
      (Odd (generalizedTau 6 (2 * n + 1)) ↔ ∃ m : ℕ, n = m * (m + 1) / 2)

/-- **$2^s$-regular partitions and the generalized tau function modulo 2.** Let $s$ be a positive
integer and $n$ a natural number. Let $R_{2^s}(n)$ be the number of partitions of $n$ in which no
part is divisible by $2^s$, and let $\tau_k(m)$ be the generalized tau function, the coefficient
of $q^m$ in $q \prod_{j \ge 1} (1 - q^j)^k$. Then $R_{2^s}(n) \equiv \tau_{2^s - 1}(n + 1) \pmod 2$.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Theorem 5 (`integers-2024-A39-thm-5`). -/
public theorem_wanted card_two_pow_regular_modEq_generalizedTau (s : ℕ) (hs : 0 < s) (n : ℕ) :
    ((Nat.Partition.restricted (n) (¬ 2 ^ s ∣ ·)).card : ℤ)
        ≡ generalizedTau ((2 : ℤ) ^ s - 1) (n + 1) [ZMOD 2]

/-- **Ramanujan's $\tau$ modulo $3$ via $9$-regular partitions.** Let $\tau = \tau_{24}$ be
Ramanujan's tau function, where $\tau_k$ is the generalized tau function, and let $R_9(m)$ be
the number of partitions of $m$ with no part divisible by $9$. For every integer $n \ge 1$,
$\tau(n + 1) \equiv R_9(n/3) \pmod 3$ if $3$ divides $n$, and $\tau(n + 1) \equiv 0 \pmod 3$
otherwise.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Theorem 6 (`integers-2024-A39-thm-6`). -/
public theorem_wanted ramanujanTau_succ_modEq_nine_regular (n : ℕ) (hn : 0 < n) :
    generalizedTau 24 (n + 1) ≡
      (if 3 ∣ n then ((Nat.Partition.restricted (n / 3) (¬ 9 ∣ ·)).card : ℤ) else 0) [ZMOD 3]

/-- **Ramanujan's congruence $\tau(3n) \equiv 0 \pmod 3$.** Let $\tau = \tau_{24}$ be Ramanujan's
tau function, where $\tau_k$ is the generalized tau function. For every integer $n \ge 1$,
$\tau(3n) \equiv 0 \pmod 3$.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Corollary 1 (`integers-2024-A39-cor-1`). -/
public theorem_wanted ramanujanTau_three_mul_modEq_zero (n : ℕ) (hn : 0 < n) :
    generalizedTau 24 (3 * n) ≡ 0 [ZMOD 3]

/-- **9-regular partitions modulo 3 and the divisor sum.** Let $R_9(m)$ denote the number of
partitions of $m$ in which no part is divisible by $9$, and let $\sigma(m)$ be the sum of the
positive divisors of $m$. For every positive integer $n$, $R_9(n) \equiv \sigma(3n + 1) \pmod 3$.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Corollary 2 (`integers-2024-A39-cor-2`). -/
public theorem_wanted card_nine_regular_modEq_sigma (n : ℕ) (hn : 0 < n) :
    ((Nat.Partition.restricted (n) (¬ 9 ∣ ·)).card : ℤ)
        ≡ (ArithmeticFunction.sigma 1 (3 * n + 1) : ℤ) [ZMOD 3]

/-- **Ramanujan's $\tau$ modulo $5$ via $25$-regular partitions.** Let $\tau = \tau_{24}$ be
Ramanujan's tau function, where $\tau_k$ is the generalized tau function, and let $R_{25}(n)$ be
the number of partitions of $n$ with no part divisible by $25$. For every integer $n \ge 1$,
$\tau(n + 1) \equiv R_{25}(n) \pmod 5$.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Theorem 7 (`integers-2024-A39-thm-7`). -/
public theorem_wanted ramanujanTau_succ_modEq_twentyfive_regular (n : ℕ) (hn : 0 < n) :
    generalizedTau 24 (n + 1) ≡ ((Nat.Partition.restricted (n) (¬ 25 ∣ ·)).card : ℤ) [ZMOD 5]

/-- **25-regular partitions modulo 5 and the divisor sum.** Let $R_{25}(m)$ denote the number of
partitions of $m$ in which no part is divisible by $25$, and let $\sigma(m)$ be the sum of the
positive divisors of $m$. For every positive integer $n$,
$R_{25}(n) \equiv (n + 1) \, \sigma(n + 1) \pmod 5$.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Corollary 3 (`integers-2024-A39-cor-3`). -/
public theorem_wanted card_twentyfive_regular_modEq_mul_sigma (n : ℕ) (hn : 0 < n) :
    ((Nat.Partition.restricted (n) (¬ 25 ∣ ·)).card : ℤ) ≡ ((n + 1 : ℕ) : ℤ)
        * (ArithmeticFunction.sigma 1 (n + 1) : ℤ) [ZMOD 5]

/-- **Ramanujan's $\tau$ modulo $7$ via triangular numbers.** Let $\tau = \tau_{24}$ be Ramanujan's
tau function, where $\tau_k$ is the generalized tau function. For every integer $n \ge 1$,
$\tau(n + 1)$ is congruent modulo $7$ to the sum of $(-1)^{m + r} (2m + 1)(2r + 1)$ over all
pairs of integers $m, r \ge 0$ with $m(m + 1)/2 + 7r(r + 1)/2 = n$.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Theorem 8 (`integers-2024-A39-thm-8`). -/
public theorem_wanted ramanujanTau_succ_modEq_triangular_sum_seven (n : ℕ) (hn : 0 < n) :
    generalizedTau 24 (n + 1) ≡
      ∑ m ∈ Finset.range (n + 1), ∑ r ∈ Finset.range (n + 1),
        if m * (m + 1) / 2 + 7 * (r * (r + 1) / 2) = n then
          (-1 : ℤ) ^ (m + r) * ((2 * m + 1 : ℕ) : ℤ) * ((2 * r + 1 : ℕ) : ℤ)
        else 0 [ZMOD 7]

/-- **Ramanujan's $\tau$ modulo $11$ via pentagonal numbers.** Let $\tau = \tau_{24}$ be Ramanujan's
tau function, where $\tau_k$ is the generalized tau function, and let $P(r) = r(3r - 1)/2$ for
integers $r$. For every integer $n \ge 1$, $\tau(n + 1)$ is congruent modulo $11$ to the sum of
$(-1)^{l + m + s + r}$ over all quadruples of integers $(l, m, s, r)$ with
$P(l) + P(m) + 11P(s) + 11P(r) = n$.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Theorem 9 (`integers-2024-A39-thm-9`). -/
public theorem_wanted ramanujanTau_succ_modEq_pentagonal_sum_eleven (n : ℕ) (hn : 0 < n) :
    generalizedTau 24 (n + 1) ≡
      ∑ l ∈ Finset.Icc (-(n : ℤ)) n, ∑ m ∈ Finset.Icc (-(n : ℤ)) n, ∑ s ∈ Finset.Icc (-(n : ℤ)) n,
          ∑ r ∈ Finset.Icc (-(n : ℤ)) n,
        if pentagonal l + pentagonal m + 11 * pentagonal s + 11 * pentagonal r = n then
          ((l + m + s + r).negOnePow : ℤ)
        else 0 [ZMOD 11]

/-- **Ramanujan's $\tau$ modulo $13$ via $\tau_{11}$.** Let $\tau = \tau_{24}$ be Ramanujan's tau
function, where $\tau_k$ is the generalized tau function, and let $P(r) = r(3r - 1)/2$ for
integers $r$. For every integer $n \ge 1$,
$$\tau(n + 1) \equiv \sum_{13P(r) \le n} (-1)^r \tau_{11}(n - 13P(r) + 1) \pmod{13},$$
the sum running over all integers $r$ with $13P(r) \le n$.

The source record prints $\tau_{11}(s)$ in place of $\tau_{11}(s + 1)$, where $n = 13P(r) + s$;
that version is false at $n = 1$. The shifted index comes from the identity
$\prod_{m \ge 1} (1 - q^m)^{11} (1 - q^{13m}) = \sum_{r, s} (-1)^r \tau_{11}(s + 1) q^{13P(r) + s}$,
which follows from Definition 1.1 and is used in the proof.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Theorem 10 (`integers-2024-A39-thm-10`). -/
public theorem_wanted ramanujanTau_succ_modEq_pentagonal_tau_eleven (n : ℕ) (hn : 0 < n) :
    generalizedTau 24 (n + 1) ≡
      ∑ r ∈ Finset.Icc (-(n : ℤ)) n,
        if 13 * pentagonal r ≤ n then
          (r.negOnePow : ℤ) * generalizedTau 11 (n - 13 * pentagonal r + 1)
        else 0 [ZMOD 13]

/-- **Ramanujan's $\tau$ modulo $17$ via $\tau_7$.** Let $\tau = \tau_{24}$ be Ramanujan's tau
function, where $\tau_k$ is the generalized tau function, and let $P(r) = r(3r - 1)/2$ for
integers $r$. For every integer $n \ge 1$,
$$\tau(n + 1) \equiv \sum_{17P(r) \le n} (-1)^r \tau_7(n - 17P(r) + 1) \pmod{17},$$
the sum running over all integers $r$ with $17P(r) \le n$.

The source record prints $\tau_7(s)$ in place of $\tau_7(s + 1)$, where $n = 17P(r) + s$;
that version is false at $n = 1$. The shifted index comes from the identity
$\prod_{m \ge 1} (1 - q^m)^7 (1 - q^{17m}) = \sum_{r, s} (-1)^r \tau_7(s + 1) q^{17P(r) + s}$,
which follows from Definition 1.1 and is used in the proof.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Theorem 11 (`integers-2024-A39-thm-11`). -/
public theorem_wanted ramanujanTau_succ_modEq_pentagonal_tau_seven (n : ℕ) (hn : 0 < n) :
    generalizedTau 24 (n + 1) ≡
      ∑ r ∈ Finset.Icc (-(n : ℤ)) n,
        if 17 * pentagonal r ≤ n then
          (r.negOnePow : ℤ) * generalizedTau 7 (n - 17 * pentagonal r + 1)
        else 0 [ZMOD 17]

/-- **Ramanujan's $\tau$ modulo $19$ via $\tau_5$.** Let $\tau = \tau_{24}$ be Ramanujan's tau
function, where $\tau_k$ is the generalized tau function, and let $P(r) = r(3r - 1)/2$ for
integers $r$. For every integer $n \ge 1$,
$$\tau(n + 1) \equiv \sum_{19P(r) \le n} (-1)^r \tau_5(n - 19P(r) + 1) \pmod{19},$$
the sum running over all integers $r$ with $19P(r) \le n$.

The source record prints $\tau_5(s)$ in place of $\tau_5(s + 1)$, where $n = 19P(r) + s$;
that version is false at $n = 1$. The shifted index comes from the identity
$\prod_{m \ge 1} (1 - q^m)^5 (1 - q^{19m}) = \sum_{r, s} (-1)^r \tau_5(s + 1) q^{19P(r) + s}$,
which follows from Definition 1.1 and is used in the proof.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Theorem 12 (`integers-2024-A39-thm-12`). -/
public theorem_wanted ramanujanTau_succ_modEq_pentagonal_tau_five (n : ℕ) (hn : 0 < n) :
    generalizedTau 24 (n + 1) ≡
      ∑ r ∈ Finset.Icc (-(n : ℤ)) n,
        if 19 * pentagonal r ≤ n then
          (r.negOnePow : ℤ) * generalizedTau 5 (n - 19 * pentagonal r + 1)
        else 0 [ZMOD 19]

/-- **Ramanujan's $\tau$ modulo $23$ via pentagonal numbers.** Let $\tau = \tau_{24}$ be
Ramanujan's tau function, where $\tau_k$ is the generalized tau function, and let
$P(r) = r(3r - 1)/2$ for integers $r$. For every integer $n \ge 1$, $\tau(n + 1)$ is congruent
modulo $23$ to the sum of $(-1)^{r + s}$ over all pairs of integers $(r, s)$ with
$P(r) + 23P(s) = n$.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Theorem 13 (`integers-2024-A39-thm-13`). -/
public theorem_wanted ramanujanTau_succ_modEq_pentagonal_sum_twentythree (n : ℕ) (hn : 0 < n) :
    generalizedTau 24 (n + 1) ≡
      ∑ r ∈ Finset.Icc (-(n : ℤ)) n, ∑ s ∈ Finset.Icc (-(n : ℤ)) n,
        if pentagonal r + 23 * pentagonal s = n then ((r + s).negOnePow : ℤ) else 0
      [ZMOD 23]

/-- **Ramanujan's $\tau$ modulo $25$ via $5$-regular partitions.** Let $\tau = \tau_{24}$ be
Ramanujan's tau function, where $\tau_k$ is the generalized tau function. Let $R_5(m)$ be the
number of partitions of $m$ with no part divisible by $5$, and let $P(t) = t(3t - 1)/2$ for
integers $t$. For every integer $n \ge 1$,
$$\tau(n + 1) \equiv \sum (-1)^{s + t} (2s + 1) R_5\big(n - 5s(s + 1)/2 - 5P(t)\big) \pmod{25},$$
the sum running over all integers $s \ge 0$ and $t$ with $5s(s + 1)/2 + 5P(t) \le n$.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Theorem 14 (`integers-2024-A39-thm-14`). -/
public theorem_wanted ramanujanTau_succ_modEq_five_regular_sum_twentyfive (n : ℕ) (hn : 0 < n) :
    generalizedTau 24 (n + 1) ≡
      ∑ s ∈ Finset.range (n + 1), ∑ t ∈ Finset.Icc (-(n : ℤ)) n,
        if 5 * (s * (s + 1) / 2) + 5 * pentagonal t ≤ n then
          (((s : ℤ) + t).negOnePow : ℤ) * ((2 * s + 1 : ℕ) : ℤ) *
            ((Nat.Partition.restricted (n - 5 * (s * (s + 1) / 2) - 5 * pentagonal t)
                (¬ 5 ∣ ·)).card : ℤ)
        else 0 [ZMOD 25]

/-- **Generalized tau at a prime power modulo the prime.** Let $p$ be a prime, let $s \ge 1$ and
$n \ge 0$ be natural numbers, and for an integer $t$ let $P(t) = t(3t - 1)/2$ be the generalized
pentagonal number. Then $\tau_{p^s}(n + 1)$ is congruent modulo $p$ to the sum of $(-1)^t$ over
the integers $t$ with $-n \le t \le n$ and $n = p^s P(t)$.

Since $P$ is injective, this sum has at most one term: $\tau_{p^s}(n + 1) \equiv (-1)^t \pmod{p}$
if $n = p^s P(t)$, and $\tau_{p^s}(n + 1) \equiv 0 \pmod{p}$ if $n$ is not of this form.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Theorem 15 (`integers-2024-A39-thm-15`). -/
public theorem_wanted generalizedTau_prime_pow_succ_modEq (p : ℕ) (hp : p.Prime) (s : ℕ)
    (hs : 0 < s) (n : ℕ) :
    generalizedTau ((p ^ s : ℕ) : ℤ) (n + 1) ≡
      ∑ t ∈ Finset.Icc (-(n : ℤ)) n,
          if n = p ^ s * pentagonal t then (t.negOnePow : ℤ) else 0 [ZMOD p]

/-- **Generalized tau function $\tau_{2p}$ modulo $p$.** Let $p$ be an odd prime, let $\tau_k$ be
the generalized tau function, and for an integer $r$ let $P(r) = r(3r - 1)/2$ be the generalized
pentagonal number. For every integer $n \ge 0$,
$$\tau_{2p}(n + 1) \equiv \sum (-1)^{r + s} \pmod p,$$
the sum running over the pairs of integers $r, s$ with $|r| \le n$, $|s| \le n$ and
$n = p\,(P(r) + P(s))$.

The paper prints the side condition as $n + 1 = p(P(r) + P(s))$, which is false: at $n = 0$ the
left side is $\tau_{2p}(1) = 1$ while that sum is empty. The identity
$\sum_{n \ge 0} \tau_{2p}(n + 1) q^n \equiv \prod_{m \ge 1} (1 - q^{pm})^2 \pmod p$ from the
paper's proof gives $n = p(P(r) + P(s))$.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Theorem 16 (`integers-2024-A39-thm-16`). -/
public theorem_wanted generalizedTau_two_mul_prime_succ_modEq (p : ℕ) (hp : p.Prime) (hodd : Odd p)
    (n : ℕ) :
    generalizedTau (2 * p) (n + 1) ≡
      ∑ r ∈ Finset.Icc (-(n : ℤ)) n, ∑ s ∈ Finset.Icc (-(n : ℤ)) n,
        if n = p * (pentagonal r + pentagonal s) then ((r + s).negOnePow : ℤ) else 0
      [ZMOD p]

/-- **$\tau_{2p}(n + 1)$ vanishes modulo $p$ when $p \nmid n$.** Let $p$ be an odd prime and $n$ a
natural number not divisible by $p$. Then $\tau_{2p}(n + 1) \equiv 0 \pmod{p}$.

The record prints the hypothesis as $p \nmid n + 1$; that is false, and the corollary follows from
Theorem 3.26 (the record's Theorem 16) in its corrected form, which forces $p \mid n$ for a nonzero
residue.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Corollary 4 (`integers-2024-A39-cor-4`). -/
public theorem_wanted generalizedTau_two_mul_prime_succ_modEq_zero (p : ℕ) (hp : p.Prime)
    (hodd : Odd p) (n : ℕ) (hn : ¬ p ∣ n) :
    generalizedTau (2 * p) (n + 1) ≡ 0 [ZMOD p]

/-- **Generalized tau at $2p + 1$ modulo $p$.** Let $p$ be an odd prime and $n$ a natural number,
and for an integer $j$ let $P(j) = j(3j - 1)/2$ be the generalized pentagonal number. Then
$\tau_{2p + 1}(n + 1)$ is congruent modulo $p$ to the sum of $(-1)^{r + s + t}$ over the triples
of integers $(r, s, t)$ with $-n \le r, s, t \le n$ and $n = P(r) + p(P(s) + P(t))$.

The record prints the condition as $n + 1 = P(r) + p(P(s) + P(t))$; that is false, and the
proof's identity $\sum \tau_{2p+1}(n + 1) q^n \equiv \prod (1 - q^m)(1 - q^{pm})^2 \pmod{p}$
gives the index $n$.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Theorem 17 (`integers-2024-A39-thm-17`). -/
public theorem_wanted generalizedTau_two_mul_prime_add_one_succ_modEq (p : ℕ) (hp : p.Prime)
    (hodd : Odd p) (n : ℕ) :
    generalizedTau (2 * p + 1) (n + 1) ≡
      ∑ r ∈ Finset.Icc (-(n : ℤ)) n, ∑ s ∈ Finset.Icc (-(n : ℤ)) n, ∑ t ∈ Finset.Icc (-(n : ℤ)) n,
        if n = pentagonal r + p * (pentagonal s + pentagonal t) then
          ((r + s + t).negOnePow : ℤ)
        else 0 [ZMOD p]

/-- **Generalized tau at $p^2 + 1$ modulo $p$.** Let $p$ be an odd prime and $n$ a natural number,
and for an integer $j$ let $P(j) = j(3j - 1)/2$ be the generalized pentagonal number. Then
$\tau_{p^2 + 1}(n + 1)$ is congruent modulo $p$ to the sum of $(-1)^{r + s}$ over the pairs of
integers $(r, s)$ with $-n \le r, s \le n$ and $n = P(r) + p^2 P(s)$.

The record prints the condition as $n + 1 = P(r) + p^2 P(s)$; that is false, and the proof's
identity $\sum \tau_{p^2+1}(n + 1) q^n \equiv \prod (1 - q^m)(1 - q^{p^2 m}) \pmod{p}$ gives the
index $n$.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Theorem 18 (`integers-2024-A39-thm-18`). -/
public theorem_wanted generalizedTau_prime_sq_add_one_succ_modEq (p : ℕ) (hp : p.Prime)
    (hodd : Odd p) (n : ℕ) :
    generalizedTau (p ^ 2 + 1) (n + 1) ≡
      ∑ r ∈ Finset.Icc (-(n : ℤ)) n, ∑ s ∈ Finset.Icc (-(n : ℤ)) n,
        if n = pentagonal r + p ^ 2 * pentagonal s then ((r + s).negOnePow : ℤ) else 0
      [ZMOD p]

/-- **A congruence for 9-regular partitions at $4n + 1$.** Let $R_9(m)$ denote the number of
partitions of $m$ in which no part is divisible by $9$. For every positive integer $n$,
$R_9(4n + 1) \equiv R_9(n) \pmod 3$.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Theorem 19 (`integers-2024-A39-thm-19`). -/
public theorem_wanted card_nine_regular_four_mul_add_one_modEq (n : ℕ) (hn : 0 < n) :
    ((Nat.Partition.restricted (4 * n + 1) (¬ 9 ∣ ·)).card : ℤ)
    ≡ ((Nat.Partition.restricted (n) (¬ 9 ∣ ·)).card : ℤ) [ZMOD 3]

/-- **Iterated congruences for 9-regular partitions modulo 3.** Let $R_9(m)$ denote the number of
partitions of $m$ in which no part is divisible by $9$, and let $N_s = (4^s - 1)/3$. For all
positive integers $r$ and $s$, $R_9((r - 1) 4^{s-1} + N_s) \equiv R_9(r) \pmod 3$,
$R_9(N_s) \equiv 1 \pmod 3$, $R_9(4^{s-1} + N_s) \equiv 2 \pmod 3$ and
$R_9(2 \cdot 4^{s-1} + N_s) \equiv 0 \pmod 3$.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Corollary 5 (`integers-2024-A39-cor-5`). -/
public theorem_wanted card_nine_regular_iterate_modEq (r s : ℕ) (hr : 0 < r) (hs : 0 < s) :
    ((Nat.Partition.restricted ((r - 1) * 4 ^ (s - 1) + (4 ^ s - 1) / 3) (¬ 9 ∣ ·)).card : ℤ)
        ≡ ((Nat.Partition.restricted (r) (¬ 9 ∣ ·)).card : ℤ) [ZMOD 3] ∧
      ((Nat.Partition.restricted ((4 ^ s - 1) / 3) (¬ 9 ∣ ·)).card : ℤ) ≡ 1 [ZMOD 3] ∧
      ((Nat.Partition.restricted (4 ^ (s - 1) + (4 ^ s - 1) / 3) (¬ 9 ∣ ·)).card : ℤ) ≡ 2 [ZMOD 3] ∧
      ((Nat.Partition.restricted (2 * 4 ^ (s - 1) + (4 ^ s - 1) / 3) (¬ 9 ∣ ·)).card : ℤ)
          ≡ 0 [ZMOD 3]

/-- **Prime-regular partitions and the generalized tau function.** Let $p$ be a prime and $n$ a
natural number. Let $R_p(n)$ be the number of partitions of $n$ in which no part is divisible by
$p$, and let $\tau_k(m)$ be the generalized tau function, the coefficient of $q^m$ in
$q \prod_{j \ge 1} (1 - q^j)^k$. Then $R_p(n) \equiv \tau_{p-1}(n + 1) \pmod p$.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Theorem 20 (`integers-2024-A39-thm-20`). -/
public theorem_wanted card_prime_regular_modEq_generalizedTau_pred (p : ℕ) (hp : p.Prime) (n : ℕ) :
    ((Nat.Partition.restricted (n) (¬ p ∣ ·)).card : ℤ)
        ≡ generalizedTau ((p : ℤ) - 1) (n + 1) [ZMOD p]

/-- **Binomial coefficients $\binom{n+k}{k}$ modulo an odd prime.** Let $l$ be an odd prime, $k$
an integer with $1 \le k < l$, $n$ a natural number, and $r$ the remainder of $n$ modulo $l$. If
$r \le l - k - 1$, then $\binom{n+k}{k} \equiv (-1)^r \binom{l-k-1}{r} \pmod l$; otherwise
$\binom{n+k}{k} \equiv 0 \pmod l$.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Lemma 1 (`integers-2024-A39-lem-1`). -/
public theorem_wanted choose_add_modEq_prime (l : ℕ) (hl : l.Prime) (hodd : Odd l) (k : ℕ)
    (hk : 1 ≤ k) (hkl : k < l) (n : ℕ) :
    ((n + k).choose k : ℤ) ≡
      (if n % l ≤ l - k - 1 then (-1 : ℤ) ^ (n % l) * ((l - k - 1).choose (n % l) : ℤ)
        else 0) [ZMOD l]

/-- **$\tau_{-k}$ and partition convolutions modulo a prime.** Let $l$ be an odd prime, let $k$ be a
natural number with $2 \le k < l$, let $n$ be a natural number, and write $p(s)$ for the number of
partitions of $s$. Then
$$\tau_{-k}(n + 1) \equiv \sum_{s=0}^{\lfloor n/l \rfloor} \tau_{l-k}(n - ls + 1)\, p(s) \pmod{l},$$
and the composition sum $\sum p(a_1) p(a_2) \cdots p(a_k)$, taken over all $k$-tuples
$(a_1, \dots, a_k)$ of natural numbers with $a_1 + \cdots + a_k = n$, is congruent modulo $l$ to
the same right-hand side.

The record prints $\tau_{l-k}(t)$ in place of $\tau_{l-k}(t + 1)$, writing $n = t + ls$; that is
false. The proof's identity
$\prod (1 - q^m)^{-k} \equiv \prod (1 - q^m)^{l-k} (1 - q^{lm})^{-1} \pmod{l}$ together with
Definition 1.1 ($\prod (1 - q^m)^j = \sum \tau_j(t + 1) q^t$) gives $\tau_{l-k}(t + 1)$;
Corollary 4.3 (the record's Corollary 6) uses this shifted form, $\omega(t) = \tau_1(t + 1)$.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Theorem 21 (`integers-2024-A39-thm-21`). -/
public theorem_wanted generalizedTau_neg_succ_modEq_partition_convolution (k : ℕ) (hk : 2 ≤ k)
    (l : ℕ) (hl : l.Prime) (hodd : Odd l) (hkl : k < l) (n : ℕ) :
    generalizedTau (-(k : ℤ)) (n + 1) ≡
        ∑ s ∈ Finset.range (n / l + 1),
          generalizedTau ((l : ℤ) - k) (n - l * s + 1)
              * (Fintype.card (Nat.Partition s) : ℤ) [ZMOD l] ∧
      (∑ a ∈ Finset.Nat.antidiagonalTuple k n,
          ∏ i, (Fintype.card (Nat.Partition (a i)) : ℤ)) ≡
        ∑ s ∈ Finset.range (n / l + 1),
          generalizedTau ((l : ℤ) - k) (n - l * s + 1)
              * (Fintype.card (Nat.Partition s) : ℤ) [ZMOD l]

/-- **Partition convolution modulo $3$.** Let $p(a)$ be the number of partitions of $a$, and let
$\omega(t)$ be the coefficient of $q^t$ in Euler's product $\prod_{m \ge 1} (1 - q^m)$. For every
integer $n \ge 0$,
$$\sum_{a + b = n} p(a)\, p(b) \equiv \sum_{0 \le s \le n/3} \omega(n - 3s)\, p(s) \pmod 3,$$
the left sum running over pairs $(a, b)$ of nonnegative integers and the right one over integers
$s$.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Corollary 6 (`integers-2024-A39-cor-6`). -/
public theorem_wanted partition_convolution_two_modEq_three (n : ℕ) :
    (∑ x ∈ Finset.antidiagonal n,
        (Fintype.card (Nat.Partition x.1) : ℤ) * (Fintype.card (Nat.Partition x.2) : ℤ)) ≡
      ∑ s ∈ Finset.range (n / 3 + 1),
        PowerSeries.coeff (n - 3 * s) (PowerSeries.pentagonalSeries ℤ)
            * (Fintype.card (Nat.Partition s) : ℤ) [ZMOD 3]

/-- **Partition composition sums vanishing modulo a prime.** Let $p(a)$ be the number of
partitions of $a$. Let $\ell \ge 5$ be a prime and $m \ge 0$ an integer such that
$m \not\equiv 0 \pmod{\ell}$ and $m \not\equiv (-1)^r \binom{\ell - 3}{r} \pmod{\ell}$ for every
integer $r$ with $0 \le r \le (\ell - 3)/2$. Then every integer $n \ge 0$ with
$n \equiv m \pmod{\ell}$ satisfies
$$\sum_{a_1 + \cdots + a_{\ell - 3} = n} p(a_1) \cdots p(a_{\ell - 3}) \equiv 0 \pmod{\ell},$$
the sum running over all $(\ell - 3)$-tuples $(a_1, \dots, a_{\ell - 3})$ of nonnegative integers
with sum $n$.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Corollary 7 (`integers-2024-A39-cor-7`). -/
public theorem_wanted partition_composition_sum_modEq_zero (l : ℕ) (hl : l.Prime) (h5 : 5 ≤ l)
    (m : ℕ) (hm0 : ¬ (m : ℤ) ≡ 0 [ZMOD l])
    (hm : ∀ r ≤ (l - 3) / 2, ¬ (m : ℤ) ≡ (-1 : ℤ) ^ r * ((l - 3).choose r : ℤ) [ZMOD l])
    (n : ℕ) (hn : n ≡ m [MOD l]) :
    (∑ a ∈ Finset.Nat.antidiagonalTuple (l - 3) n,
        ∏ i, (Fintype.card (Nat.Partition (a i)) : ℤ)) ≡ 0 [ZMOD l]

/-- **Ramanujan's congruence modulo $7$.** Let $\tau(n) = \tau_{24}(n)$ be Ramanujan's tau
function, the generalized tau function with $k = 24$. For every positive integer $n$,
$\tau(7n) \equiv 0 \pmod 7$.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Corollary 8 (`integers-2024-A39-cor-8`). -/
public theorem_wanted ramanujanTau_seven_mul_modEq_zero (n : ℕ) (hn : 0 < n) :
    generalizedTau 24 (7 * n) ≡ 0 [ZMOD 7]

/-- **Vanishing of $\tau_k(n)$ modulo the prime $k - 1$.** Let $n \ge 1$ and let $k$ be a natural
number such that $k - 1$ is prime. For an integer $t$ let $P(t) = t(3t - 1)/2$ be the generalized
pentagonal number. If $k - 1$ does not divide $n - 1 - P(t)$ for any integer $t$ with
$P(t) \le n - 1$, then the generalized tau function satisfies $\tau_k(n) \equiv 0 \pmod{k - 1}$.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Proposition 1 (`integers-2024-A39-prop-1`). -/
public theorem_wanted generalizedTau_modEq_zero_of_pentagonal (n : ℕ) (hn : 0 < n) (k : ℕ)
    (hk : (k - 1).Prime)
    (h : ∀ t : ℤ, pentagonal t ≤ n - 1 → ¬ (k - 1) ∣ n - 1 - pentagonal t) :
    generalizedTau k n ≡ 0 [ZMOD ((k - 1 : ℕ) : ℤ)]

/-- **Divisibility of $n\,\tau_k(n + 1)$ by $|k|$.** Let $\tau_k$ be the generalized tau function.
For every positive integer $n$ and every integer $k$ with $|k| \ge 2$,
$n\,\tau_k(n + 1) \equiv 0 \pmod{|k|}$.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Proposition 2 (`integers-2024-A39-prop-2`). -/
public theorem_wanted mul_generalizedTau_succ_modEq_zero (n : ℕ) (hn : 0 < n) (k : ℤ) (hk : 2 ≤ |k|)
    :
    (n : ℤ) * generalizedTau k (n + 1) ≡ 0 [ZMOD |k|]

/-- **Vanishing of the generalized tau function modulo $|k|/d$.** Let $\tau_k(n)$ be the
generalized tau function, the coefficient of $q^n$ in $q \prod_{j \ge 1} (1 - q^j)^k$. Let $k$ be
an integer with $|k| \ge 2$ and $d$ a natural number dividing $|k|$ with $d < |k|$. Then for all
natural numbers $m$ and $r$ with $\gcd(r, |k|/d) = 1$,
$\tau_k(|k| m + d r + 1) \equiv 0 \pmod{|k|/d}$.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Proposition 3 (`integers-2024-A39-prop-3`). -/
public theorem_wanted generalizedTau_modEq_zero_of_coprime (m : ℕ) (k : ℤ) (hk : 2 ≤ |k|) (d : ℕ)
    (hd : d ∣ k.natAbs) (hdk : d < k.natAbs) (r : ℕ)
    (hr : Nat.gcd r (k.natAbs / d) = 1) :
    generalizedTau k (k.natAbs * m + d * r + 1) ≡ 0 [ZMOD ((k.natAbs / d : ℕ) : ℤ)]

/-- **Ramanujan's tau function modulo divisors of $24$.** Let $\tau(n) = \tau_{24}(n)$ be
Ramanujan's tau function, the generalized tau function with $k = 24$. For every integer
$m \ge 0$: $\tau(24m + r + 1) \equiv 0 \pmod{24}$ for $r \in \{1, 5, 7, 11, 13, 17, 19, 23\}$;
$\tau(24m + r + 1) \equiv 0 \pmod 6$ for $r \in \{4, 20\}$;
$\tau(24m + r + 1) \equiv 0 \pmod 8$ for $r \in \{3, 6, 9, 15\}$;
$\tau(24m + r + 1) \equiv 0 \pmod 3$ for $r \in \{8, 16\}$; and
$\tau(24m + 13) \equiv 0 \pmod 2$.

The paper prints the moduli of the second, fourth and fifth congruences as $12$, $6$ and $4$,
which is false (for instance $\tau(5) = 4830$ is not divisible by $12$); the moduli used are
$24/\gcd(r, 24)$, which the paper's Proposition 2.4 at $k = 24$ gives. The first and third
congruences are as printed.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Proposition 4 (`integers-2024-A39-prop-4`). -/
public theorem_wanted ramanujanTau_modEq_divisors_twentyfour (m : ℕ) :
    (∀ r ∈ ({1, 5, 7, 11, 13, 17, 19, 23} : Finset ℕ),
        generalizedTau 24 (24 * m + r + 1) ≡ 0 [ZMOD 24]) ∧
      (∀ r ∈ ({4, 20} : Finset ℕ), generalizedTau 24 (24 * m + r + 1) ≡ 0 [ZMOD 6]) ∧
      (∀ r ∈ ({3, 9, 6, 15} : Finset ℕ), generalizedTau 24 (24 * m + r + 1) ≡ 0 [ZMOD 8]) ∧
      (∀ r ∈ ({8, 16} : Finset ℕ), generalizedTau 24 (24 * m + r + 1) ≡ 0 [ZMOD 3]) ∧
      generalizedTau 24 (24 * m + 13) ≡ 0 [ZMOD 2]

end

end MetaMathlibExt
