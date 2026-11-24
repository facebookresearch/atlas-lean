/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Int.Interval
public import Mathlib.SetTheory.Cardinal.Finite
public import MathlibExt.Combinatorics.Enumerative.Partition.Overpartition

/-!
# Linear relations for overpartitions into odd parts (statements)

Statement-only targets from Deepthi G. and S. Chandankumar, *Linear Relations for
Overpartitions into Odd Parts*. `po(m)` is `overpartitionOddPartsCount m`, counted with the
existing `Nat.Overpartition` structure; `p(m)` is `Fintype.card (Nat.Partition m)`. The
paper's sums over all `k` (with `po`, `p` vanishing at negative arguments) become finite
sums over the `k` whose shifted argument is nonnegative. The paper's `p̄(m)` (overpartitions),
`pd(m)` (distinct parts) and `pdo(m)` (distinct odd parts) are `Nat.card (Nat.Overpartition m)`,
`(Nat.Partition.distincts m).card` and `(Nat.Partition.oddDistincts m).card`. Statements of
Theorems 1-2, 6, 8-14 and Corollaries 1, 3-5 were checked against the arXiv version
(arXiv:2403.05866v1, numbered Theorems 1.1-1.2 and 3.1-3.9, Corollaries 3.1-3.5).
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Overpartitions into odd parts.** For a natural number $n$, $\mathrm{po}(n)$ is the
number of overpartitions of $n$ all of whose parts are odd.

Source: Deepthi G. and S. Chandankumar, *Linear Relations for Overpartitions into Odd
Parts*, INTEGERS 26 (2026), Article A60, title and Section 1 (values `po(0), …, po(10)`
listed after Theorem 5). -/
public noncomputable def overpartitionOddPartsCount (n : ℕ) : ℕ :=
  Nat.card {O : Nat.Overpartition n // ∀ a ∈ O.toPartition.parts, Odd a}

/-- **Overpartitions of zero into odd parts.** The number $\mathrm{po}(0)$ of overpartitions
of $0$ into odd parts equals $1$: the empty overpartition is the only one.

Source: Deepthi G. and S. Chandankumar, *Linear Relations for Overpartitions into Odd
Parts*, INTEGERS 26 (2026), Article A60, value `po(0) = 1` listed after Theorem 5. -/
public theorem overpartitionOddPartsCount_zero : overpartitionOddPartsCount 0 = 1 := by
  unfold overpartitionOddPartsCount
  rw [Nat.card_eq_one_iff_exists]
  refine ⟨⟨Nat.Overpartition.ofPartition default, fun a ha => ?_⟩, fun y => ?_⟩
  · simp [Nat.Overpartition.ofPartition_toPartition, Nat.Partition.partition_zero_parts] at ha
  · exact Subtype.ext (Nat.Overpartition.eq_of_zero _ _)

/-- **Pentagonal recurrence for overpartitions into odd parts.** Let $\mathrm{po}(j)$ be the
number of overpartitions of $j$ into odd parts. For every natural number $n$, the sum
$\sum_k (-1)^k \, \mathrm{po}(n - k(3k+1)/2)$ over the integers $k$ with $k(3k+1)/2 \le n$
equals $(-1)^{\lceil m/2 \rceil}$ if $n = m(3m+1)/2$ for some integer $m$, and $0$ otherwise.

Such an $m$ is unique, since the numbers $m(3m+1)/2$ with $m$ an integer are distinct.

Source: Deepthi G. and S. Chandankumar, *Linear Relations for Overpartitions into Odd
Parts*, INTEGERS 26 (2026), Article A60, Theorem 3 (`integers-2026-A60-thm-3`). -/
public theorem_wanted overpartitionOdd_pentagonal_recurrence (n : ℕ) :
    ∑ k ∈ (Finset.Icc (-(n : ℤ)) n).filter (fun k : ℤ => k * (3 * k + 1) / 2 ≤ (n : ℤ)),
        (-1 : ℤ) ^ k.natAbs
          * (overpartitionOddPartsCount (n - (k * (3 * k + 1) / 2).toNat) : ℤ)
      = ∑ m ∈ Finset.Icc (-(n : ℤ)) n,
          if m * (3 * m + 1) / 2 = n then (-1 : ℤ) ^ ((m + 1) / 2).natAbs else 0

/-- **Triangular recurrence for overpartitions into odd parts.** Write $\mathrm{po}(m)$ for the
number of overpartitions of $m$ into odd parts. For every natural number $n$, the sum
$\sum_{k \ge 0,\ k(k+1)/2 \le n} (-1)^{\lceil k/2 \rceil} \, \mathrm{po}(n - k(k+1)/2)$ equals
$1$ if $n = m(m+1)/2$ for some natural number $m$, and equals $0$ otherwise.

Source: Deepthi G. and S. Chandankumar, *Linear Relations for Overpartitions into Odd
Parts*, INTEGERS 26 (2026), Article A60, Theorem 4 (`integers-2026-A60-thm-4`). -/
public theorem_wanted overpartitionOdd_triangular_recurrence (n : ℕ) :
    ∑ k ∈ (Finset.range (n + 1)).filter (fun k => k * (k + 1) / 2 ≤ n),
        (-1 : ℤ) ^ ((k + 1) / 2) * (overpartitionOddPartsCount (n - k * (k + 1) / 2) : ℤ)
      = if n ∈ (Finset.range (n + 1)).image (fun m => m * (m + 1) / 2) then 1 else 0

/-- **Square recurrence for overpartitions into odd parts.** Write $\mathrm{po}(m)$ for the
number of overpartitions of $m$ into odd parts. For every natural number $n$, the sum
$\mathrm{po}(n) + 2 \sum_{k \ge 1,\ 2k^2 \le n} (-1)^k \, \mathrm{po}(n - 2k^2)$ equals $1$ if
$n = 0$, equals $2$ if $n = m^2$ for some integer $m \ge 1$, and equals $0$ otherwise.

Source: Deepthi G. and S. Chandankumar, *Linear Relations for Overpartitions into Odd
Parts*, INTEGERS 26 (2026), Article A60, Theorem 5 (`integers-2026-A60-thm-5`). -/
public theorem_wanted overpartitionOdd_square_recurrence (n : ℕ) :
    (overpartitionOddPartsCount n : ℤ)
        + 2 * ∑ k ∈ (Finset.Icc 1 n).filter (fun k => 2 * k ^ 2 ≤ n),
          (-1 : ℤ) ^ k * (overpartitionOddPartsCount (n - 2 * k ^ 2) : ℤ)
      = if n = 0 then 1 else if n ∈ (Finset.Icc 1 n).image (fun m => m ^ 2) then 2 else 0

/-- **Overpartitions into odd parts from partitions and pentagonal numbers.** Let
$\mathrm{po}(m)$ be the number of overpartitions of $m$ into odd parts and $p(m)$ the number
of partitions of $m$. For every natural number $n$,
$\mathrm{po}(n) = \sum_k (-1)^{\lceil k/2 \rceil} p(n - k(3k+1)/2)$, the sum running over
the integers $k$ with $k(3k+1)/2 \le n$.

Source: Deepthi G. and S. Chandankumar, *Linear Relations for Overpartitions into Odd
Parts*, INTEGERS 26 (2026), Article A60, Theorem 7 (`integers-2026-A60-thm-7`). -/
public theorem_wanted overpartitionOdd_eq_sum_partition_pentagonal (n : ℕ) :
    (overpartitionOddPartsCount n : ℤ)
      = ∑ k ∈ (Finset.Icc (-(n : ℤ)) n).filter (fun k : ℤ => k * (3 * k + 1) / 2 ≤ (n : ℤ)),
          (-1 : ℤ) ^ ((k + 1) / 2).natAbs
            * (Fintype.card (Nat.Partition (n - (k * (3 * k + 1) / 2).toNat)) : ℤ)

/-- **Parity form of Euler's pentagonal recurrence.** Write $p(m)$ for the number of partitions
of $m$. For every positive integer $n$, the sum
$\sum_{k \in \mathbb{Z},\ k(3k+1)/2 \le n} p(n - k(3k+1)/2)$ is even.

Source: Deepthi G. and S. Chandankumar, *Linear Relations for Overpartitions into Odd
Parts*, INTEGERS 26 (2026), Article A60, Corollary 2 (`integers-2026-A60-cor-2`). -/
public theorem_wanted partition_pentagonal_sum_even (n : ℕ) (hn : 0 < n) :
    Even (∑ k ∈ (Finset.Icc (-(n : ℤ)) n).filter (fun k : ℤ => k * (3 * k + 1) / 2 ≤ (n : ℤ)),
      Fintype.card (Nat.Partition (n - (k * (3 * k + 1) / 2).toNat)))

/-- **Partitions whose even parts are distinct.** For a natural number $n$, $\mathrm{ped}(n)$ is
the number of partitions of $n$ in which every even part occurs exactly once; the odd parts are
unrestricted.

Its generating function is $\sum_{n \ge 0} \mathrm{ped}(n) q^n = (q^4; q^4)_\infty / (q; q)_\infty$.

Source: Deepthi G. and S. Chandankumar, *Linear Relations for Overpartitions into Odd
Parts*, INTEGERS 26 (2026), Article A60, Section 1 (definition of `ped(n)` before Theorem 1). -/
public def distinctEvenPartsCount (n : ℕ) : ℕ :=
  ((Finset.univ : Finset n.Partition).filter
    fun p => ∀ i ∈ p.parts, Even i → p.parts.count i = 1).card

/-- **Partitions whose odd parts are distinct.** For a natural number $n$, $\mathrm{pod}(n)$ is
the number of partitions of $n$ in which every odd part occurs exactly once; the even parts are
unrestricted.

Its generating function is
$\sum_{n \ge 0} \mathrm{pod}(n) q^n = (-q; q^2)_\infty / (q^2; q^2)_\infty$.

Source: Deepthi G. and S. Chandankumar, *Linear Relations for Overpartitions into Odd
Parts*, INTEGERS 26 (2026), Article A60, Section 3 (definition of `pod(n)` before Theorem 6). -/
public def distinctOddPartsCount (n : ℕ) : ℕ :=
  ((Finset.univ : Finset n.Partition).filter
    fun p => ∀ i ∈ p.parts, Odd i → p.parts.count i = 1).card

/-- **Partitions with no part congruent to 2 modulo 4.** For a natural number $n$, $P_2(n)$ is
the number of partitions of $n$ none of whose parts is congruent to $2$ modulo $4$.

Its generating function is $\sum_{n \ge 0} P_2(n) q^n = (q^2; q^4)_\infty / (q; q)_\infty$.

Source: Deepthi G. and S. Chandankumar, *Linear Relations for Overpartitions into Odd
Parts*, INTEGERS 26 (2026), Article A60, Section 3 (definition of `P_2(n)` before Theorem 11). -/
public def partsNotTwoModFourCount (n : ℕ) : ℕ :=
  (Nat.Partition.restricted n fun i => i % 4 ≠ 2).card

/-- **Bipartitions into distinct parts.** Let $\operatorname{pd}(m)$ be the number of partitions
of $m$ into distinct parts. For a natural number $n$, $q(n)$ is the number of ordered pairs of
partitions into distinct parts whose sizes add up to $n$, that is,
$q(n) = \sum_{k=0}^{n} \operatorname{pd}(k) \operatorname{pd}(n-k)$.

Its generating function is $\sum_{n \ge 0} q(n) x^n = (-x; x)_\infty^2$, where
$(a; x)_\infty = \prod_{i \ge 0} (1 - a x^i)$.

Source: Deepthi G. and S. Chandankumar, *Linear Relations for Overpartitions into Odd
Parts*, INTEGERS 26 (2026), Article A60, Section 3 (definition of `q(n)` before Theorem 12). -/
public def distinctPartsBipartitionCount (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1),
    (Nat.Partition.distincts k).card * (Nat.Partition.distincts (n - k)).card

/-- **Values at zero of the restricted partition counts.** The number $\operatorname{ped}(0)$ of
partitions of $0$ in which no even part is repeated, the number $\operatorname{pod}(0)$ of
partitions of $0$ in which no odd part is repeated, the number $P_2(0)$ of partitions of $0$ with
no part congruent to $2$ modulo $4$, and the number $q(0)$ of ordered pairs of partitions into
distinct parts with sizes adding up to $0$ are all equal to $1$, as only the empty partition (or
the pair of empty partitions) is counted.

Source: Deepthi G. and S. Chandankumar, *Linear Relations for Overpartitions into Odd
Parts*, INTEGERS 26 (2026), Article A60, Sections 1 and 3 (definitions of `ped`, `pod`,
`P_2`, `q`). -/
public theorem distinctEvenParts_distinctOddParts_partsNotTwoModFour_bipartition_zero :
    distinctEvenPartsCount 0 = 1 ∧ distinctOddPartsCount 0 = 1 ∧
      partsNotTwoModFourCount 0 = 1 ∧ distinctPartsBipartitionCount 0 = 1 := by
  decide

/-- **Merca's triangular recurrence for partitions with distinct even parts.** Let
$\operatorname{ped}(m)$ be the number of partitions of $m$ in which no even part is repeated. For
every $n \ge 0$, the sum $\sum_{j \ge 0} (-1)^{\lceil j/2 \rceil} \operatorname{ped}(n - j(j+1)/2)$
over the $j$ with $j(j+1)/2 \le n$ equals $1$ if $n = k(k+1)$ for some integer $k \ge 0$, and $0$
otherwise.

Source: Deepthi G. and S. Chandankumar, *Linear Relations for Overpartitions into Odd
Parts*, INTEGERS 26 (2026), Article A60, Theorem 1, quoting M. Merca (via da Silva and Sakai)
(`integers-2026-A60-thm-1`). -/
public theorem_wanted distinctEvenParts_triangular_recurrence (n : ℕ) :
    ∑ j ∈ (Finset.range (n + 1)).filter (fun j => j * (j + 1) / 2 ≤ n),
        (-1 : ℤ) ^ ((j + 1) / 2) * (distinctEvenPartsCount (n - j * (j + 1) / 2) : ℤ)
      = if n ∈ (Finset.range (n + 1)).image (fun k => k * (k + 1)) then 1 else 0

/-- **Merca's square recurrence for partitions with distinct even parts.** Let
$\operatorname{ped}(m)$ be the number of partitions of $m$ in which no even part is repeated. For
every $n \ge 0$, the sum $\sum_j (-1)^j \operatorname{ped}(n - 2j^2)$ over the integers $j$ with
$2j^2 \le n$ equals $1$ if $n = k(k+1)/2$ for some integer $k \ge 0$, and $0$ otherwise.

Source: Deepthi G. and S. Chandankumar, *Linear Relations for Overpartitions into Odd
Parts*, INTEGERS 26 (2026), Article A60, Theorem 2, quoting M. Merca (via da Silva and Sakai)
(`integers-2026-A60-thm-2`). -/
public theorem_wanted distinctEvenParts_square_recurrence (n : ℕ) :
    ∑ j ∈ (Finset.Icc (-(n : ℤ)) n).filter (fun j : ℤ => 2 * j ^ 2 ≤ (n : ℤ)),
        (-1 : ℤ) ^ j.natAbs * (distinctEvenPartsCount (n - (2 * j ^ 2).toNat) : ℤ)
      = if n ∈ (Finset.range (n + 1)).image (fun k => k * (k + 1) / 2) then 1 else 0

/-- **Overpartitions into odd parts from partitions with distinct odd parts.** Let
$\mathrm{po}(m)$ be the number of overpartitions of $m$ into odd parts and $\mathrm{pod}(m)$
the number of partitions of $m$ whose odd parts are distinct. For every natural number $n$,
$\mathrm{po}(n) = \sum_k \mathrm{pod}(n - k(k+1)/2)$, the sum running over the natural
numbers $k$ with $k(k+1)/2 \le n$.

Source: Deepthi G. and S. Chandankumar, *Linear Relations for Overpartitions into Odd
Parts*, INTEGERS 26 (2026), Article A60, Theorem 6 (`integers-2026-A60-thm-6`). -/
public theorem_wanted overpartitionOdd_eq_sum_distinctOddParts_triangular (n : ℕ) :
    overpartitionOddPartsCount n =
      ∑ k ∈ (Finset.range (n + 1)).filter (fun k => k * (k + 1) / 2 ≤ n),
        distinctOddPartsCount (n - k * (k + 1) / 2)

/-- **Evenness of a triangular sum of partition counts with distinct odd parts.** Let
$\operatorname{pod}(m)$ be the number of partitions of $m$ in which no odd part is repeated. For
every $n > 0$, the sum $\sum_{k \ge 0} \operatorname{pod}(n - k(k+1)/2)$ over the $k$ with
$k(k+1)/2 \le n$ is even.

Source: Deepthi G. and S. Chandankumar, *Linear Relations for Overpartitions into Odd
Parts*, INTEGERS 26 (2026), Article A60, Corollary 1 (`integers-2026-A60-cor-1`). -/
public theorem_wanted distinctOddParts_triangular_sum_even (n : ℕ) (hn : 0 < n) :
    Even (∑ k ∈ (Finset.range (n + 1)).filter (fun k => k * (k + 1) / 2 ≤ n),
      distinctOddPartsCount (n - k * (k + 1) / 2))

/-- **Overpartitions into odd parts from overpartitions and squares.** Let $\mathrm{po}(m)$
be the number of overpartitions of $m$ into odd parts and $\overline{p}(m)$ the number of
overpartitions of $m$. For every natural number $n$,
$\mathrm{po}(n) = \sum_k (-1)^k \, \overline{p}(n - 2k^2)$, the sum running over the
integers $k$ with $2k^2 \le n$.

With the partition function $p$ in place of $\overline{p}$ the identity fails at $n = 1$:
$\mathrm{po}(1) = 2$ but $p(1) = 1$.

Source: Deepthi G. and S. Chandankumar, *Linear Relations for Overpartitions into Odd
Parts*, INTEGERS 26 (2026), Article A60, Theorem 8 (`integers-2026-A60-thm-8`). -/
public theorem_wanted overpartitionOdd_eq_sum_overpartition_square (n : ℕ) :
    (overpartitionOddPartsCount n : ℤ) =
      ∑ k ∈ (Finset.Icc (-(n : ℤ)) n).filter (fun k : ℤ => 2 * k ^ 2 ≤ (n : ℤ)),
        (-1 : ℤ) ^ k.natAbs * (Nat.card (Nat.Overpartition (n - (2 * k ^ 2).toNat)) : ℤ)

/-- **Overpartitions of odd numbers into odd parts.** Let $\mathrm{po}(m)$ be the number of
overpartitions of $m$ into odd parts and $\overline{p}(m)$ the number of overpartitions of $m$.
For every natural number $n$,
$\mathrm{po}(2n+1) = 2 \sum_k \overline{p}(n - 2k(k+1))$, the sum running over the natural
numbers $k$ with $2k(k+1) \le n$.

With the partition function $p$ in place of $\overline{p}$ the identity fails at $n = 1$.

Source: Deepthi G. and S. Chandankumar, *Linear Relations for Overpartitions into Odd
Parts*, INTEGERS 26 (2026), Article A60, Theorem 9 (`integers-2026-A60-thm-9`). -/
public theorem_wanted overpartitionOdd_odd_eq_two_mul_sum_overpartition (n : ℕ) :
    overpartitionOddPartsCount (2 * n + 1) =
      2 * ∑ k ∈ (Finset.range (n + 1)).filter (fun k => 2 * k * (k + 1) ≤ n),
        Nat.card (Nat.Overpartition (n - 2 * k * (k + 1)))

/-- **Overpartitions of even numbers into odd parts.** Let $\mathrm{po}(m)$ be the number of
overpartitions of $m$ into odd parts and $\overline{p}(m)$ the number of overpartitions of $m$.
For every natural number $n$,
$\mathrm{po}(2n) = \overline{p}(n) + 2 \sum_k \overline{p}(n - 2k^2)$, the sum running over
the integers $k \ge 1$ with $2k^2 \le n$.

The sum cannot start at $k = 0$: at $n = 0$ that would give
$\overline{p}(0) + 2 \, \overline{p}(0) = 3$, whereas $\mathrm{po}(0) = 1$.

Source: Deepthi G. and S. Chandankumar, *Linear Relations for Overpartitions into Odd
Parts*, INTEGERS 26 (2026), Article A60, Theorem 10 (`integers-2026-A60-thm-10`). -/
public theorem_wanted overpartitionOdd_even_eq_sum_overpartition (n : ℕ) :
    overpartitionOddPartsCount (2 * n) =
      Nat.card (Nat.Overpartition n) +
        2 * ∑ k ∈ (Finset.Icc 1 n).filter (fun k => 2 * k ^ 2 ≤ n),
          Nat.card (Nat.Overpartition (n - 2 * k ^ 2))

/-- **Overpartitions into odd parts from partitions with no part congruent to 2 modulo 4.**
Let $\mathrm{po}(m)$ be the number of overpartitions of $m$ into odd parts and $P_2(m)$ the
number of partitions of $m$ with no part congruent to $2$ modulo $4$. For every natural
number $n$, $\mathrm{po}(n) = \sum_k P_2(n - k(k+1)/2)$, the sum running over the natural
numbers $k$ with $k(k+1)/2 \le n$.

The case $n = 0$ is included: there both sides equal $1$.

Source: Deepthi G. and S. Chandankumar, *Linear Relations for Overpartitions into Odd
Parts*, INTEGERS 26 (2026), Article A60, Theorem 11 (`integers-2026-A60-thm-11`). -/
public theorem_wanted overpartitionOdd_eq_sum_partsNotTwoModFour_triangular (n : ℕ) :
    overpartitionOddPartsCount n =
      ∑ k ∈ (Finset.range (n + 1)).filter (fun k => k * (k + 1) / 2 ≤ n),
        partsNotTwoModFourCount (n - k * (k + 1) / 2)

/-- **Parity of a triangular sum of partitions with no part congruent to 2 modulo 4.** Write
$P_2(m)$ for the number of partitions of $m$ with no part congruent to $2$ modulo $4$. For every
positive integer $n$, the sum $\sum_{k \ge 0,\ k(k+1)/2 \le n} P_2(n - k(k+1)/2)$ is even.

Source: Deepthi G. and S. Chandankumar, *Linear Relations for Overpartitions into Odd
Parts*, INTEGERS 26 (2026), Article A60, Corollary 3 (`integers-2026-A60-cor-3`). -/
public theorem_wanted partsNotTwoModFour_triangular_sum_even (n : ℕ) (hn : 0 < n) :
    Even (∑ k ∈ (Finset.range (n + 1)).filter (fun k => k * (k + 1) / 2 ≤ n),
      partsNotTwoModFourCount (n - k * (k + 1) / 2))

/-- **Bipartitions into distinct parts from the partition function.** Let $q(n)$ be the number of
ordered pairs of partitions into distinct parts whose sizes add up to $n$, and let $p(m)$ be the
number of partitions of $m$. For every $n \ge 0$, $q(n) = \sum_{k \ge 0} p(n - k(k+1)/2)$, where
the sum runs over the $k$ with $k(k+1)/2 \le n$.

The source states this for $n > 0$; it also holds at $n = 0$, where both sides equal $1$.

Source: Deepthi G. and S. Chandankumar, *Linear Relations for Overpartitions into Odd
Parts*, INTEGERS 26 (2026), Article A60, Theorem 12 (`integers-2026-A60-thm-12`). -/
public theorem_wanted distinctPartsBipartition_eq_sum_partition_triangular (n : ℕ) :
    distinctPartsBipartitionCount n =
      ∑ k ∈ (Finset.range (n + 1)).filter (fun k => k * (k + 1) / 2 ≤ n),
        Fintype.card (Nat.Partition (n - k * (k + 1) / 2))

/-- **Overpartitions into odd parts and partitions into distinct odd parts.** Let
$\mathrm{po}(m)$ be the number of overpartitions of $m$ into odd parts and $\mathrm{pdo}(m)$
the number of partitions of $m$ into distinct odd parts. For every natural number $n$, the
sum $\sum_k (-1)^k \, \mathrm{po}(n - k(3k+1)/2)$ over the integers $k$ with
$k(3k+1)/2 \le n$ equals the sum $\sum_k (-1)^k \, \mathrm{pdo}(n - k(3k+1))$ over the
integers $k$ with $k(3k+1) \le n$.

Source: Deepthi G. and S. Chandankumar, *Linear Relations for Overpartitions into Odd
Parts*, INTEGERS 26 (2026), Article A60, Theorem 13 (`integers-2026-A60-thm-13`). -/
public theorem_wanted overpartitionOdd_pentagonal_sum_eq_oddDistincts (n : ℕ) :
    ∑ k ∈ (Finset.Icc (-(n : ℤ)) n).filter (fun k : ℤ => k * (3 * k + 1) / 2 ≤ (n : ℤ)),
        (-1 : ℤ) ^ k.natAbs
          * (overpartitionOddPartsCount (n - (k * (3 * k + 1) / 2).toNat) : ℤ)
      = ∑ k ∈ (Finset.Icc (-(n : ℤ)) n).filter (fun k : ℤ => k * (3 * k + 1) ≤ (n : ℤ)),
          (-1 : ℤ) ^ k.natAbs
            * ((Nat.Partition.oddDistincts (n - (k * (3 * k + 1)).toNat)).card : ℤ)

/-- **Pentagonal recurrence for partitions into distinct odd parts.** Let $\operatorname{pdo}(m)$
be the number of partitions of $m$ into distinct odd parts. For every $n \ge 0$, the sum
$\sum_k (-1)^k \operatorname{pdo}(n - k(3k+1))$ over the integers $k$ with $k(3k+1) \le n$
equals $(-1)^{\lceil m/2 \rceil}$ if $n = m(3m+1)/2$ for some integer $m$, and $0$ otherwise.

Source: Deepthi G. and S. Chandankumar, *Linear Relations for Overpartitions into Odd
Parts*, INTEGERS 26 (2026), Article A60, Corollary 4 (`integers-2026-A60-cor-4`). -/
public theorem_wanted oddDistincts_pentagonal_recurrence (n : ℕ) :
    ∑ k ∈ (Finset.Icc (-(n : ℤ)) n).filter (fun k : ℤ => k * (3 * k + 1) ≤ (n : ℤ)),
        (-1 : ℤ) ^ k.natAbs
          * ((Nat.Partition.oddDistincts (n - (k * (3 * k + 1)).toNat)).card : ℤ)
      = ∑ m ∈ Finset.Icc (-(n : ℤ)) n,
          if m * (3 * m + 1) / 2 = n then (-1 : ℤ) ^ ((m + 1) / 2).natAbs else 0

/-- **Overpartitions into odd parts and partitions into distinct parts.** Write $\mathrm{po}(m)$
for the number of overpartitions of $m$ into odd parts and $\mathrm{pd}(m)$ for the number of
partitions of $m$ into distinct parts. For every natural number $n$,
$\sum_{k \ge 0,\ k(k+1)/2 \le n} (-1)^{\lceil k/2 \rceil} \, \mathrm{po}(n - k(k+1)/2) =
\sum_{k \in \mathbb{Z},\ k(3k+1) \le n} (-1)^k \, \mathrm{pd}(n - k(3k+1))$.

The sum on the left runs over $k \ge 0$ only. Taken over all integers $k$ it would double, since
$k$ and $-1 - k$ give the same term, and the identity would fail at $n = 0$.

Source: Deepthi G. and S. Chandankumar, *Linear Relations for Overpartitions into Odd
Parts*, INTEGERS 26 (2026), Article A60, Theorem 14 (`integers-2026-A60-thm-14`). -/
public theorem_wanted overpartitionOdd_triangular_sum_eq_distincts (n : ℕ) :
    ∑ k ∈ (Finset.range (n + 1)).filter (fun k => k * (k + 1) / 2 ≤ n),
        (-1 : ℤ) ^ ((k + 1) / 2) * (overpartitionOddPartsCount (n - k * (k + 1) / 2) : ℤ)
      = ∑ k ∈ (Finset.Icc (-(n : ℤ)) n).filter (fun k : ℤ => k * (3 * k + 1) ≤ (n : ℤ)),
          (-1 : ℤ) ^ k.natAbs
            * ((Nat.Partition.distincts (n - (k * (3 * k + 1)).toNat)).card : ℤ)

/-- **Pentagonal recurrence for partitions into distinct parts.** Let $\operatorname{pd}(m)$ be the
number of partitions of $m$ into distinct parts. For every $n \ge 0$, the sum
$\sum_k (-1)^k \operatorname{pd}(n - k(3k+1))$ over the integers $k$ with $k(3k+1) \le n$ equals
$1$ if $n = m(m+1)/2$ for some integer $m \ge 0$, and $0$ otherwise.

Source: Deepthi G. and S. Chandankumar, *Linear Relations for Overpartitions into Odd
Parts*, INTEGERS 26 (2026), Article A60, Corollary 5 (`integers-2026-A60-cor-5`). -/
public theorem_wanted distincts_pentagonal_recurrence (n : ℕ) :
    ∑ k ∈ (Finset.Icc (-(n : ℤ)) n).filter (fun k : ℤ => k * (3 * k + 1) ≤ (n : ℤ)),
        (-1 : ℤ) ^ k.natAbs
          * ((Nat.Partition.distincts (n - (k * (3 * k + 1)).toNat)).card : ℤ)
      = if n ∈ (Finset.range (n + 1)).image (fun m => m * (m + 1) / 2) then 1 else 0

end

end MetaMathlibExt
