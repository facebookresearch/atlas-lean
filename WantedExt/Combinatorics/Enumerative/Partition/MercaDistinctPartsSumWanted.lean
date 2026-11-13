/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Enumerative.Partition.Basic

/-!
# Merca's identities for sums of different parts (statements)

Statement-only targets from Cristina Ballantine, *Combinatorial Proofs of Merca's Identities
Involving the Sum of Different Parts Congruent to r Modulo m in All Partitions of n*,
INTEGERS 24 (2024), Article A15. `a_{r,m}(n)` is `sumDistinctPartsModEq m r n` and `s_m(n)` is
`sumDistinctPartsMultAtLeast m n`; `p(k)` is `Fintype.card (Nat.Partition k)`. The paper's
infinite sums (all terms vanish at negative arguments) become finite sums over the indices
whose shifted argument is nonnegative. `q_odd(k)` is `(Nat.Partition.oddDistincts k).card`,
`q(k/2)` (zero for odd `k`) is `(Nat.Partition.distincts (k / 2)).card` for even `k`, and
`p_{e-o}(k)` is `∑_{μ ⊢ k} (-1)^{ℓ(μ)}`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Sum of different parts congruent to $r$ modulo $m$.** For natural numbers $m$, $r$, $n$,
$a_{r,m}(n)$ is the sum, over all partitions $\mu$ of $n$, of the different parts $x$ of $\mu$
with $x \bmod m = r$; a part contributes $x$ once regardless of its multiplicity. It is used
with $0 \le r < m$, where $x \bmod m = r$ means $x \equiv r \pmod m$.

Source: Cristina Ballantine, *Combinatorial Proofs of Merca's Identities Involving the Sum of
Different Parts Congruent to r Modulo m in All Partitions of n*, INTEGERS 24 (2024),
Article A15, Section 1 (definition of `a_{r,m}(n)`). -/
public def sumDistinctPartsModEq (m r n : ℕ) : ℕ :=
  ∑ μ : n.Partition, ∑ x ∈ μ.parts.toFinset.filter (fun x => x % m = r), x

/-- **Sum of different parts appearing at least $m$ times.** For natural numbers $m$ and $n$,
$s_m(n)$ is the sum, over all partitions $\mu$ of $n$, of the different parts of $\mu$ that
appear at least $m$ times in $\mu$; such a part $j$ contributes $j$ once regardless of its
multiplicity.

Source: Cristina Ballantine, *Combinatorial Proofs of Merca's Identities Involving the Sum of
Different Parts Congruent to r Modulo m in All Partitions of n*, INTEGERS 24 (2024),
Article A15, Section 1 (definition of `s_m(n)`). -/
public def sumDistinctPartsMultAtLeast (m n : ℕ) : ℕ :=
  ∑ μ : n.Partition, ∑ x ∈ μ.parts.toFinset.filter (fun x => m ≤ μ.parts.count x), x

/-- **Small values of Merca's distinct-part sums.** For natural numbers $m$, $r$ and $n$, let
$a_{r,m}(n)$ be the sum, over all partitions of $n$, of the different parts $x$ of the partition
with $x \bmod m = r$, and let $s_m(n)$ be the sum, over all partitions of $n$, of the different
parts that occur at least $m$ times in the partition; each such part counts once per partition.
Then $a_{r,m}(0) = 0$ and $s_m(0) = 0$ for all $m$ and $r$, and moreover $a_{0,1}(1) = 1$,
$s_1(1) = 1$ and $s_2(1) = 0$.

The empty partition of $0$ has no parts, and $1$ has the single partition $1$.

Source: Cristina Ballantine, *Combinatorial Proofs of Merca's Identities Involving the Sum of
Different Parts Congruent to r Modulo m in All Partitions of n*, INTEGERS 24 (2024),
Article A15, Section 1 (definitions of `a_{r,m}(n)` and `s_m(n)`). -/
public theorem sumDistinctParts_small_values (m r : ℕ) :
    sumDistinctPartsModEq m r 0 = 0 ∧ sumDistinctPartsMultAtLeast m 0 = 0 ∧
      sumDistinctPartsModEq 1 0 1 = 1 ∧ sumDistinctPartsMultAtLeast 1 1 = 1 ∧
      sumDistinctPartsMultAtLeast 2 1 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [sumDistinctPartsModEq, sumDistinctPartsMultAtLeast, Finset.filter_singleton,
      Nat.Partition.partition_zero_parts, Nat.Partition.partition_one_parts]

/-- **Dyson's rank of a partition.** The rank of a partition $\mu$ of $n$ is the integer
$r(\mu) = \mu_1 - \ell(\mu)$, the largest part $\mu_1$ of $\mu$ minus its number of parts
$\ell(\mu)$, where the largest part of the empty partition is taken to be $0$. In particular the
empty partition has rank $0$.

Source: Cristina Ballantine, *Combinatorial Proofs of Merca's Identities Involving the Sum of
Different Parts Congruent to r Modulo m in All Partitions of n*, INTEGERS 24 (2024),
Article A15, Section 2 (definition of the rank before Theorem 8). -/
public def dysonRank {n : ℕ} (μ : n.Partition) : ℤ :=
  (μ.parts.sup : ℤ) - μ.parts.card

/-- **Rank of the partitions of $0$ and $1$.** The empty partition of $0$ and the partition $(1)$
of $1$ both have Dyson rank $0$.

Consequently the number of partitions of $k$ with nonnegative rank is $1$ for $k = 0$ and
$k = 1$, no partition of $1$ has positive rank, and no partition of $0$ has rank at most $-2$.

Source: Cristina Ballantine, *Combinatorial Proofs of Merca's Identities Involving the Sum of
Different Parts Congruent to r Modulo m in All Partitions of n*, INTEGERS 24 (2024),
Article A15, Section 2 (definition of the rank before Theorem 8). -/
public theorem dysonRank_small_values (μ : Nat.Partition 0) (ν : Nat.Partition 1) :
    dysonRank μ = 0 ∧ dysonRank ν = 0 := by
  refine ⟨?_, ?_⟩ <;>
    simp [dysonRank, Nat.Partition.partition_zero_parts, Nat.Partition.partition_one_parts]

/-- **Crank of a partition.** Let $\mu$ be a partition of $n$ and let $\omega(\mu)$ be the number
of parts of $\mu$ equal to $1$. The crank of $\mu$ (Andrews and Garvan) is the integer defined as
follows: if $\omega(\mu) = 0$, it is the largest part of $\mu$, where the largest part of the
empty partition is taken to be $0$; if $\omega(\mu) > 0$, it is the number of parts of $\mu$
larger than $\omega(\mu)$, counted with multiplicity, minus $\omega(\mu)$.

Source: Cristina Ballantine, *Combinatorial Proofs of Merca's Identities Involving the Sum of
Different Parts Congruent to r Modulo m in All Partitions of n*, INTEGERS 24 (2024),
Article A15, Section 2 (definition of the crank before Theorem 11). -/
public def partitionCrank {n : ℕ} (μ : n.Partition) : ℤ :=
  if μ.parts.count 1 = 0 then (μ.parts.sup : ℤ)
  else ((μ.parts.filter (fun x => μ.parts.count 1 < x)).card : ℤ) - μ.parts.count 1

/-- **Crank of the partitions of $0$ and $1$.** The empty partition of $0$ has crank $0$, and the
partition $(1)$ of $1$ has crank $0 - 1 = -1$.

Consequently the number of partitions of $0$ with nonnegative crank is $1$, and no partition of
$1$ has nonnegative crank.

Source: Cristina Ballantine, *Combinatorial Proofs of Merca's Identities Involving the Sum of
Different Parts Congruent to r Modulo m in All Partitions of n*, INTEGERS 24 (2024),
Article A15, Section 2 (definition of the crank before Theorem 11). -/
public theorem partitionCrank_small_values (μ : Nat.Partition 0) (ν : Nat.Partition 1) :
    partitionCrank μ = 0 ∧ partitionCrank ν = -1 := by
  refine ⟨?_, ?_⟩ <;>
    simp [partitionCrank, Nat.Partition.partition_zero_parts, Nat.Partition.partition_one_parts]

/-- **Merca's identity for different parts in a residue class.** Let $m$, $r$ and $n$ be natural
numbers with $r < m$, let $a_{r,m}(n)$ be the sum, over all partitions of $n$, of the different
parts congruent to $r$ modulo $m$, each counted once per partition whatever its multiplicity, and
let $p(k)$ be the number of partitions of $k$. Then
$$a_{r,m}(n) = \sum_{j \ge 0,\ mj + r \le n} (mj + r)\, p(n - mj - r).$$

Source: Cristina Ballantine, *Combinatorial Proofs of Merca's Identities Involving the Sum of
Different Parts Congruent to r Modulo m in All Partitions of n*, INTEGERS 24 (2024),
Article A15, Theorem 1 (i) (`integers-2024-A15-thm-1`). -/
public theorem_wanted sumDistinctPartsModEq_eq_sum_partition (m r n : ℕ) (hrm : r < m) :
    sumDistinctPartsModEq m r n =
      ∑ j ∈ (Finset.range (n + 1)).filter (fun j => m * j + r ≤ n),
        (m * j + r) * Fintype.card (Nat.Partition (n - (m * j + r)))

/-- **Merca's identity for $s_m(n)$.** Let $m \ge 1$ and $n$ be natural numbers, write $s_m(n)$
for the sum of the different parts that appear at least $m$ times in partitions of $n$, and
$p(k)$ for the number of partitions of $k$. Then $s_m(n) = \sum_{j \ge 0,\ mj \le n} j\, p(n - mj)$.

The paper's hypothesis $0 \le r < m$ forces $m \ge 1$; for $m = 0$ the right side diverges.

Source: Cristina Ballantine, *Combinatorial Proofs of Merca's Identities Involving the Sum of
Different Parts Congruent to r Modulo m in All Partitions of n*, INTEGERS 24 (2024),
Article A15, Theorem 1 (ii) (`integers-2024-A15-thm-1`). -/
public theorem_wanted sumDistinctPartsMultAtLeast_eq_sum_partition (m n : ℕ) (hm : 0 < m) :
    sumDistinctPartsMultAtLeast m n =
      ∑ j ∈ (Finset.range (n + 1)).filter (fun j => m * j ≤ n),
        j * Fintype.card (Nat.Partition (n - m * j))

/-- **Different parts in a residue class and even-minus-odd partition counts.** Let $m$, $r$ and
$n$ be natural numbers with $r < m$, and for $k \ge 0$ let $a_{r,m}(k)$ be the sum, over all
partitions of $k$, of the different parts congruent to $r$ modulo $m$, each counted once per
partition whatever its multiplicity. Let $p_{e-o}(k) = \sum_{\mu} (-1)^{\ell(\mu)}$, the sum over
the partitions $\mu$ of $k$ with $\ell(\mu)$ the number of parts of $\mu$; it is the number of
partitions of $k$ with an even number of parts minus the number with an odd number of parts. Then
$$a_{r,m}(n) + 2 \sum_{k \ge 1,\ k^2 \le n} (-1)^k a_{r,m}(n - k^2)
= \sum_{j \ge 0,\ mj + r \le n} (mj + r)\, p_{e-o}(n - mj - r).$$

Source: Cristina Ballantine, *Combinatorial Proofs of Merca's Identities Involving the Sum of
Different Parts Congruent to r Modulo m in All Partitions of n*, INTEGERS 24 (2024),
Article A15, Theorem 2 (`integers-2024-A15-thm-2`). -/
public theorem_wanted sumDistinctPartsModEq_square_eq_evenOdd (m r n : ℕ) (hrm : r < m) :
    (sumDistinctPartsModEq m r n : ℤ)
        + 2 * ∑ k ∈ (Finset.Icc 1 n).filter (fun k => k ^ 2 ≤ n),
          (-1 : ℤ) ^ k * (sumDistinctPartsModEq m r (n - k ^ 2) : ℤ)
      = ∑ j ∈ (Finset.range (n + 1)).filter (fun j => m * j + r ≤ n),
          ((m * j + r : ℕ) : ℤ) *
            ∑ μ : Nat.Partition (n - (m * j + r)), (-1 : ℤ) ^ μ.parts.card

/-- **Twice-square sum of $a_{r,m}$ and distinct odd parts.** Let $m, r, n$ be natural numbers
with $r < m$. Write $a_{r,m}(k)$ for the sum of the different parts congruent to $r$ modulo $m$
in all partitions of $k$, and $q_{\mathrm{odd}}(k)$ for the number of partitions of $k$ into
distinct odd parts. Then
$$
a_{r,m}(n) + 2 \sum_{k \ge 1,\ 2k^2 \le n} (-1)^k a_{r,m}(n - 2k^2)
= \sum_{j \ge 0,\ mj + r \le n} (mj + r)\, q_{\mathrm{odd}}(n - mj - r).
$$

Source: Cristina Ballantine, *Combinatorial Proofs of Merca's Identities Involving the Sum of
Different Parts Congruent to r Modulo m in All Partitions of n*, INTEGERS 24 (2024),
Article A15, Theorem 4 (`integers-2024-A15-thm-4`). -/
public theorem_wanted sumDistinctPartsModEq_twiceSquare_eq_oddDistinct (m r n : ℕ)
    (hrm : r < m) :
    (sumDistinctPartsModEq m r n : ℤ)
        + 2 * ∑ k ∈ (Finset.Icc 1 n).filter (fun k => 2 * k ^ 2 ≤ n),
          (-1 : ℤ) ^ k * (sumDistinctPartsModEq m r (n - 2 * k ^ 2) : ℤ)
      = ∑ j ∈ (Finset.range (n + 1)).filter (fun j => m * j + r ≤ n),
          ((m * j + r : ℕ) : ℤ) * ((Nat.Partition.oddDistincts (n - (m * j + r))).card : ℤ)

/-- **Signed triangular sum of $a_{r,m}$ and distinct partitions.** Let $m, r, n$ be natural
numbers with $r < m$. Write $a_{r,m}(k)$ for the sum of the different parts congruent to $r$
modulo $m$ in all partitions of $k$, $q(k)$ for the number of partitions of $k$ into distinct
parts, and $\tilde q(\ell)$ for $q(\ell/2)$ when $\ell$ is even and for $0$ when $\ell$ is odd.
Then
$$
\sum_{k \ge 0,\ k(k+1)/2 \le n} (-1)^{k(k+1)/2} a_{r,m}\bigl(n - k(k+1)/2\bigr)
= \sum_{j \ge 0,\ mj + r \le n} (mj + r)\, \tilde q(n - mj - r).
$$

Source: Cristina Ballantine, *Combinatorial Proofs of Merca's Identities Involving the Sum of
Different Parts Congruent to r Modulo m in All Partitions of n*, INTEGERS 24 (2024),
Article A15, Theorem 6 (`integers-2024-A15-thm-6`). -/
public theorem_wanted sumDistinctPartsModEq_triangular_eq_distinct_half (m r n : ℕ)
    (hrm : r < m) :
    ∑ k ∈ (Finset.range (n + 1)).filter (fun k => k * (k + 1) / 2 ≤ n),
        (-1 : ℤ) ^ (k * (k + 1) / 2) * (sumDistinctPartsModEq m r (n - k * (k + 1) / 2) : ℤ)
      = ∑ j ∈ (Finset.range (n + 1)).filter (fun j => m * j + r ≤ n),
          ((m * j + r : ℕ) : ℤ) *
            if Even (n - (m * j + r)) then
              ((Nat.Partition.distincts ((n - (m * j + r)) / 2)).card : ℤ)
            else 0

/-- **Signed triangular sum of $s_m$ and distinct partitions.** Let $m \ge 1$ and $n$ be natural
numbers. Write $s_m(k)$ for the sum of the different parts that appear at least $m$ times in
partitions of $k$, $q(k)$ for the number of partitions of $k$ into distinct parts, and
$\tilde q(\ell)$ for $q(\ell/2)$ when $\ell$ is even and for $0$ when $\ell$ is odd. Then
$$
\sum_{k \ge 0,\ k(k+1)/2 \le n} (-1)^{k(k+1)/2} s_m\bigl(n - k(k+1)/2\bigr)
= \sum_{j \ge 0,\ mj \le n} j\, \tilde q(n - mj).
$$

The paper says $m \ge 0$; for $m = 0$ the right side diverges.

Source: Cristina Ballantine, *Combinatorial Proofs of Merca's Identities Involving the Sum of
Different Parts Congruent to r Modulo m in All Partitions of n*, INTEGERS 24 (2024),
Article A15, Theorem 7 (`integers-2024-A15-thm-7`). -/
public theorem_wanted sumDistinctPartsMultAtLeast_triangular_eq_distinct_half (m n : ℕ)
    (hm : 0 < m) :
    ∑ k ∈ (Finset.range (n + 1)).filter (fun k => k * (k + 1) / 2 ≤ n),
        (-1 : ℤ) ^ (k * (k + 1) / 2) * (sumDistinctPartsMultAtLeast m (n - k * (k + 1) / 2) : ℤ)
      = ∑ j ∈ (Finset.range (n + 1)).filter (fun j => m * j ≤ n),
          (j : ℤ) *
            if Even (n - m * j) then ((Nat.Partition.distincts ((n - m * j) / 2)).card : ℤ)
            else 0

/-- **Different parts in a residue class and partitions of nonnegative rank.** Let $m$, $r$ and
$n$ be natural numbers with $r < m$, and for $k \ge 0$ let $a_{r,m}(k)$ be the sum, over all
partitions of $k$, of the different parts congruent to $r$ modulo $m$, each counted once per
partition whatever its multiplicity. Let $N(k)$ be the number of partitions of $k$ whose Dyson
rank (largest part minus number of parts) is nonnegative. Then
$$\sum_{j \ge 0,\ j(3j+1)/2 \le n} (-1)^j a_{r,m}(n - j(3j+1)/2)
= \sum_{j \ge 0,\ mj + r \le n} (mj + r)\, N(n - mj - r).$$

Source: Cristina Ballantine, *Combinatorial Proofs of Merca's Identities Involving the Sum of
Different Parts Congruent to r Modulo m in All Partitions of n*, INTEGERS 24 (2024),
Article A15, Theorem 8 (i) (`integers-2024-A15-thm-8`). -/
public theorem_wanted sumDistinctPartsModEq_pentagonal_eq_nonnegRank (m r n : ℕ)
    (hrm : r < m) :
    ∑ j ∈ (Finset.range (n + 1)).filter (fun j => j * (3 * j + 1) / 2 ≤ n),
        (-1 : ℤ) ^ j * (sumDistinctPartsModEq m r (n - j * (3 * j + 1) / 2) : ℤ)
      = ∑ j ∈ (Finset.range (n + 1)).filter (fun j => m * j + r ≤ n),
          ((m * j + r : ℕ) : ℤ) *
            ((Finset.univ.filter fun μ : Nat.Partition (n - (m * j + r)) =>
              0 ≤ dysonRank μ).card : ℤ)

/-- **Different parts in a residue class and partitions of positive rank.** Let $m$, $r$ and $n$
be natural numbers with $r < m$, and for $k \ge 0$ let $a_{r,m}(k)$ be the sum, over all
partitions of $k$, of the different parts congruent to $r$ modulo $m$, each counted once per
partition whatever its multiplicity. Let $R(k)$ be the number of partitions of $k$ whose Dyson
rank (largest part minus number of parts) is positive. Then
$$\sum_{j \ge 1,\ j(3j+1)/2 \le n} (-1)^{j+1} a_{r,m}(n - j(3j+1)/2)
= \sum_{j \ge 0,\ mj + r \le n} (mj + r)\, R(n - mj - r).$$

Source: Cristina Ballantine, *Combinatorial Proofs of Merca's Identities Involving the Sum of
Different Parts Congruent to r Modulo m in All Partitions of n*, INTEGERS 24 (2024),
Article A15, Theorem 8 (ii) (`integers-2024-A15-thm-8`). -/
public theorem_wanted sumDistinctPartsModEq_pentagonal_eq_posRank (m r n : ℕ) (hrm : r < m) :
    ∑ j ∈ (Finset.Icc 1 n).filter (fun j => j * (3 * j + 1) / 2 ≤ n),
        (-1 : ℤ) ^ (j + 1) * (sumDistinctPartsModEq m r (n - j * (3 * j + 1) / 2) : ℤ)
      = ∑ j ∈ (Finset.range (n + 1)).filter (fun j => m * j + r ≤ n),
          ((m * j + r : ℕ) : ℤ) *
            ((Finset.univ.filter fun μ : Nat.Partition (n - (m * j + r)) =>
              0 < dysonRank μ).card : ℤ)

/-- **Pentagonal sum of $s_m$ and nonnegative rank.** Let $m \ge 1$ and $n$ be natural numbers.
Write $s_m(k)$ for the sum of the different parts that appear at least $m$ times in partitions
of $k$, and $N(k)$ for the number of partitions of $k$ with nonnegative Dyson rank. Then
$$
\sum_{j \ge 0,\ j(3j+1)/2 \le n} (-1)^j s_m\bigl(n - j(3j+1)/2\bigr)
= \sum_{j \ge 0,\ mj \le n} j\, N(n - mj).
$$

The paper says $m \ge 0$; for $m = 0$ the right side diverges.

Source: Cristina Ballantine, *Combinatorial Proofs of Merca's Identities Involving the Sum of
Different Parts Congruent to r Modulo m in All Partitions of n*, INTEGERS 24 (2024),
Article A15, Theorem 9 (i) (`integers-2024-A15-thm-9`). -/
public theorem_wanted sumDistinctPartsMultAtLeast_pentagonal_eq_nonnegRank (m n : ℕ)
    (hm : 0 < m) :
    ∑ j ∈ (Finset.range (n + 1)).filter (fun j => j * (3 * j + 1) / 2 ≤ n),
        (-1 : ℤ) ^ j * (sumDistinctPartsMultAtLeast m (n - j * (3 * j + 1) / 2) : ℤ)
      = ∑ j ∈ (Finset.range (n + 1)).filter (fun j => m * j ≤ n),
          (j : ℤ) *
            ((Finset.univ.filter fun μ : Nat.Partition (n - m * j) => 0 ≤ dysonRank μ).card : ℤ)

/-- **Pentagonal sum of $s_m$ and positive rank.** Let $m \ge 1$ and $n$ be natural numbers.
Write $s_m(k)$ for the sum of the different parts that appear at least $m$ times in partitions
of $k$, and $R(k)$ for the number of partitions of $k$ with positive Dyson rank. Then
$$
\sum_{j \ge 1,\ j(3j+1)/2 \le n} (-1)^{j+1} s_m\bigl(n - j(3j+1)/2\bigr)
= \sum_{j \ge 0,\ mj \le n} j\, R(n - mj).
$$

The paper says $m \ge 0$; for $m = 0$ the right side diverges.

Source: Cristina Ballantine, *Combinatorial Proofs of Merca's Identities Involving the Sum of
Different Parts Congruent to r Modulo m in All Partitions of n*, INTEGERS 24 (2024),
Article A15, Theorem 9 (ii) (`integers-2024-A15-thm-9`). -/
public theorem_wanted sumDistinctPartsMultAtLeast_pentagonal_eq_posRank (m n : ℕ)
    (hm : 0 < m) :
    ∑ j ∈ (Finset.Icc 1 n).filter (fun j => j * (3 * j + 1) / 2 ≤ n),
        (-1 : ℤ) ^ (j + 1) * (sumDistinctPartsMultAtLeast m (n - j * (3 * j + 1) / 2) : ℤ)
      = ∑ j ∈ (Finset.range (n + 1)).filter (fun j => m * j ≤ n),
          (j : ℤ) *
            ((Finset.univ.filter fun μ : Nat.Partition (n - m * j) => 0 < dysonRank μ).card : ℤ)

/-- **Different parts in a residue class and Garden of Eden partitions.** Let $m$, $r$ and $n$ be
natural numbers with $r < m$, and for $k \ge 0$ let $a_{r,m}(k)$ be the sum, over all partitions
of $k$, of the different parts congruent to $r$ modulo $m$, each counted once per partition
whatever its multiplicity. Let $G(k)$ be the number of Garden of Eden partitions of $k$, that is,
partitions of $k$ whose Dyson rank (largest part minus number of parts) is at most $-2$. Then
$$\sum_{j \ge 1,\ 3j(j+1)/2 \le n} (-1)^{j+1} a_{r,m}(n - 3j(j+1)/2)
= \sum_{j \ge 0,\ mj + r \le n} (mj + r)\, G(n - mj - r).$$

The sum on the left starts at $j = 1$. Starting it at $j = 0$ makes the identity false: for
$m = 1$, $r = 0$ and $n = 1$ the left side becomes $-a_{0,1}(1) = -1$ while the right side is $0$.

Source: Cristina Ballantine, *Combinatorial Proofs of Merca's Identities Involving the Sum of
Different Parts Congruent to r Modulo m in All Partitions of n*, INTEGERS 24 (2024),
Article A15, Theorem 10 (i) (`integers-2024-A15-thm-10`). -/
public theorem_wanted sumDistinctPartsModEq_eq_gardenOfEden (m r n : ℕ) (hrm : r < m) :
    ∑ j ∈ (Finset.Icc 1 n).filter (fun j => 3 * (j * (j + 1)) / 2 ≤ n),
        (-1 : ℤ) ^ (j + 1) * (sumDistinctPartsModEq m r (n - 3 * (j * (j + 1)) / 2) : ℤ)
      = ∑ j ∈ (Finset.range (n + 1)).filter (fun j => m * j + r ≤ n),
          ((m * j + r : ℕ) : ℤ) *
            ((Finset.univ.filter fun μ : Nat.Partition (n - (m * j + r)) =>
              dysonRank μ ≤ -2).card : ℤ)

/-- **Garden of Eden identity for $s_m$.** Let $m \ge 1$ and $n$ be natural numbers. Write
$s_m(k)$ for the sum of the different parts that appear at least $m$ times in partitions of
$k$, and $G(k)$ for the number of Garden of Eden partitions of $k$, those whose Dyson rank is
at most $-2$ (so $G(0) = 0$). Then
$$
\sum_{j \ge 1,\ 3j(j+1)/2 \le n} (-1)^{j+1} s_m\bigl(n - 3j(j+1)/2\bigr)
= \sum_{j \ge 0,\ mj \le n} j\, G(n - mj).
$$

The paper says $m \ge 0$; for $m = 0$ the right side diverges.

Source: Cristina Ballantine, *Combinatorial Proofs of Merca's Identities Involving the Sum of
Different Parts Congruent to r Modulo m in All Partitions of n*, INTEGERS 24 (2024),
Article A15, Theorem 10 (ii) (`integers-2024-A15-thm-10`). -/
public theorem_wanted sumDistinctPartsMultAtLeast_eq_gardenOfEden (m n : ℕ) (hm : 0 < m) :
    ∑ j ∈ (Finset.Icc 1 n).filter (fun j => 3 * (j * (j + 1)) / 2 ≤ n),
        (-1 : ℤ) ^ (j + 1) * (sumDistinctPartsMultAtLeast m (n - 3 * (j * (j + 1)) / 2) : ℤ)
      = ∑ j ∈ (Finset.range (n + 1)).filter (fun j => m * j ≤ n),
          (j : ℤ) *
            ((Finset.univ.filter fun μ : Nat.Partition (n - m * j) =>
              dysonRank μ ≤ -2).card : ℤ)

/-- **Different parts in a residue class and partitions of nonnegative crank.** Let $m$, $r$ and
$n$ be natural numbers with $r < m$, and for $k \ge 0$ let $a_{r,m}(k)$ be the sum, over all
partitions of $k$, of the different parts congruent to $r$ modulo $m$, each counted once per
partition whatever its multiplicity. Let $C(k)$ be the number of partitions of $k$ whose crank is
nonnegative. Then
$$\sum_{j \ge 0,\ j(j+1)/2 \le n} (-1)^j a_{r,m}(n - j(j+1)/2)
= \sum_{j \ge 0,\ mj + r \le n} (mj + r)\, C(n - mj - r).$$

The companion identity of the source with the number $D(k)$ of partitions of $k$ with positive
crank is not stated: it fails for this crank, since $D(1) = 0$ while $p(1) - C(1) = 1$, where
$p(k)$ is the number of partitions of $k$ (for $m = 2$, $r = 1$, $n = 2$ its left side is $1$ and
its right side is $0$).

Source: Cristina Ballantine, *Combinatorial Proofs of Merca's Identities Involving the Sum of
Different Parts Congruent to r Modulo m in All Partitions of n*, INTEGERS 24 (2024),
Article A15, Theorem 11 (i) (`integers-2024-A15-thm-11`). -/
public theorem_wanted sumDistinctPartsModEq_triangular_eq_nonnegCrank (m r n : ℕ)
    (hrm : r < m) :
    ∑ j ∈ (Finset.range (n + 1)).filter (fun j => j * (j + 1) / 2 ≤ n),
        (-1 : ℤ) ^ j * (sumDistinctPartsModEq m r (n - j * (j + 1) / 2) : ℤ)
      = ∑ j ∈ (Finset.range (n + 1)).filter (fun j => m * j + r ≤ n),
          ((m * j + r : ℕ) : ℤ) *
            ((Finset.univ.filter fun μ : Nat.Partition (n - (m * j + r)) =>
              0 ≤ partitionCrank μ).card : ℤ)

/-- **Signed triangular sum of $s_m$ and nonnegative crank.** Let $m \ge 1$ and $n$ be natural
numbers. Write $s_m(k)$ for the sum of the different parts that appear at least $m$ times in
partitions of $k$, and $C(k)$ for the number of partitions of $k$ with nonnegative crank. Then
$$
\sum_{j \ge 0,\ j(j+1)/2 \le n} (-1)^j s_m\bigl(n - j(j+1)/2\bigr)
= \sum_{j \ge 0,\ mj \le n} j\, C(n - mj).
$$

The paper says $m \ge 0$; for $m = 0$ the right side diverges. Part (ii) (with $D(k)$, positive
crank) is omitted: it is false for this crank ($m = 1$, $n = 2$: left side $s_1(1) = 1$, right
side $D(1) + 2 D(0) = 0$).

Source: Cristina Ballantine, *Combinatorial Proofs of Merca's Identities Involving the Sum of
Different Parts Congruent to r Modulo m in All Partitions of n*, INTEGERS 24 (2024),
Article A15, Theorem 12 (i) (`integers-2024-A15-thm-12`). -/
public theorem_wanted sumDistinctPartsMultAtLeast_triangular_eq_nonnegCrank (m n : ℕ)
    (hm : 0 < m) :
    ∑ j ∈ (Finset.range (n + 1)).filter (fun j => j * (j + 1) / 2 ≤ n),
        (-1 : ℤ) ^ j * (sumDistinctPartsMultAtLeast m (n - j * (j + 1) / 2) : ℤ)
      = ∑ j ∈ (Finset.range (n + 1)).filter (fun j => m * j ≤ n),
          (j : ℤ) *
            ((Finset.univ.filter fun μ : Nat.Partition (n - m * j) =>
              0 ≤ partitionCrank μ).card : ℤ)

end

end MetaMathlibExt
