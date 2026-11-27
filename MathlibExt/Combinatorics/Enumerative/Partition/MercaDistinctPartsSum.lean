/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
import MathlibExt.Combinatorics.Enumerative.Partition.Counting

/-!
# Merca's sums of different parts

Merca's identities express two sums over the partitions of `n` in terms of partition numbers.
The first sums distinct parts in a residue class, and the second sums distinct parts occurring
at least `m` times. The module also gives the values of these sums, Dyson's rank and the
partition crank on small partitions.
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
public theorem sumDistinctPartsModEq_eq_sum_partition (m r n : ℕ) (hrm : r < m) :
    sumDistinctPartsModEq m r n =
      ∑ j ∈ (Finset.range (n + 1)).filter (fun j => m * j + r ≤ n),
        (m * j + r) * Fintype.card (Nat.Partition (n - (m * j + r))) := by
  let partSizes := (Finset.range (n + 1)).filter (fun x => x % m = r)
  calc
    sumDistinctPartsModEq m r n =
        ∑ x ∈ partSizes, ∑ _μ ∈ Finset.univ.filter (fun μ : n.Partition => x ∈ μ.parts), x := by
      apply Finset.sum_comm' (f := fun _ x => x)
      intro μ x
      simp only [partSizes, Finset.mem_univ, true_and, Finset.mem_filter, Multiset.mem_toFinset,
        Finset.mem_range, Nat.lt_succ_iff]
      exact ⟨fun ⟨hx, hr⟩ => ⟨hx, μ.le_of_mem_parts hx, hr⟩, fun ⟨hx, _, hr⟩ => ⟨hx, hr⟩⟩
    _ = ∑ x ∈ partSizes, x * Fintype.card (Nat.Partition (n - x)) := by
      refine Finset.sum_congr rfl fun x hx => ?_
      obtain rfl | hxpos := Nat.eq_zero_or_pos x
      · simp
      have hxn := Finset.mem_range_succ_iff.mp (Finset.mem_filter.mp hx).1
      rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm, ← Fintype.card_subtype,
        Fintype.card_congr (Nat.Partition.partitionWithPartEquiv hxpos hxn)]
    _ = _ := by
      symm
      apply Finset.sum_bij (fun j _ => m * j + r)
      · intro j hj
        exact Finset.mem_filter.mpr ⟨Finset.mem_range_succ_iff.mpr (Finset.mem_filter.mp hj).2,
          (Nat.mul_add_mod ..).trans (Nat.mod_eq_of_lt hrm)⟩
      · intro i _ j _ hij
        exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < m) (Nat.add_right_cancel hij)
      · intro x hx
        obtain ⟨hxn, hxr⟩ := Finset.mem_filter.mp hx
        have hrepr : m * (x / m) + r = x := hxr ▸ Nat.div_add_mod x m
        refine ⟨x / m, Finset.mem_filter.mpr ⟨?_, ?_⟩, hrepr⟩
        · exact Finset.mem_range.mpr ((Nat.div_le_self ..).trans_lt (Finset.mem_range.mp hxn))
        · exact hrepr.le.trans (Finset.mem_range_succ_iff.mp hxn)
      · intros
        rfl

open Finset

/-- **Merca's identity for $s_m(n)$.** Let $m \ge 1$ and $n$ be natural numbers, write $s_m(n)$
for the sum of the different parts that appear at least $m$ times in partitions of $n$, and
$p(k)$ for the number of partitions of $k$. Then $s_m(n) = \sum_{j \ge 0,\ mj \le n} j\, p(n - mj)$.

The paper's hypothesis $0 \le r < m$ forces $m \ge 1$; for $m = 0$ the condition $mj \le n$ would
no longer bound $j$ in the sum.

Source: Cristina Ballantine, *Combinatorial Proofs of Merca's Identities Involving the Sum of
Different Parts Congruent to r Modulo m in All Partitions of n*, INTEGERS 24 (2024),
Article A15, Theorem 1 (ii) (`integers-2024-A15-thm-1`). -/
public theorem sumDistinctPartsMultAtLeast_eq_sum_partition (m n : ℕ) (hm : 0 < m) :
    sumDistinctPartsMultAtLeast m n =
      ∑ j ∈ (Finset.range (n + 1)).filter (fun j => m * j ≤ n),
        j * Fintype.card (Nat.Partition (n - m * j)) := by
  let sizes := (range (n + 1)).filter (fun j => m * j ≤ n)
  have parts_eq (μ : n.Partition) :
      μ.parts.toFinset.filter (fun j => m ≤ μ.parts.count j) =
        sizes.filter (fun j => m ≤ μ.parts.count j) := by
    ext j
    simp only [sizes, mem_filter, Multiset.mem_toFinset, mem_range]
    constructor
    · rintro ⟨hj, hcount⟩
      refine ⟨⟨Nat.lt_succ_of_le (μ.le_of_mem_parts hj), ?_⟩, hcount⟩
      obtain ⟨rest, hrest⟩ := exists_add_of_le (Multiset.le_count_iff_replicate_le.mp hcount)
      rw [← μ.parts_sum, hrest, Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul]
      exact Nat.le_add_right _ _
    · exact fun ⟨_, hcount⟩ => ⟨Multiset.count_pos.mp (hm.trans_le hcount), hcount⟩
  calc
    sumDistinctPartsMultAtLeast m n =
        ∑ μ : n.Partition, ∑ j ∈ sizes, if m ≤ μ.parts.count j then j else 0 := by
      unfold sumDistinctPartsMultAtLeast
      exact sum_congr rfl fun μ _ => by rw [parts_eq, sum_filter]
    _ = ∑ j ∈ sizes, ∑ μ : n.Partition, if m ≤ μ.parts.count j then j else 0 := sum_comm
    _ = _ := by
      refine sum_congr rfl fun j hj => ?_
      obtain rfl | hjpos := Nat.eq_zero_or_pos j
      · simp
      · rw [← sum_filter, sum_const, smul_eq_mul,
          ← Fintype.card_subtype (fun μ : n.Partition => m ≤ μ.parts.count j),
          Nat.Partition.card_count_ge hjpos (mem_filter.mp hj).2, mul_comm]

end

end MetaMathlibExt
