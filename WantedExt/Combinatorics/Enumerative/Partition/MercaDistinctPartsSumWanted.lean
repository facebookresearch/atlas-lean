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

/-- `a_{r,m}(n)`: the sum of all different parts congruent to `r` modulo `m` in all
partitions of `n`; a part `x ≡ r (mod m)` of a partition contributes `x` once regardless of
its multiplicity. Used with `0 ≤ r < m`, where `x ≡ r (mod m)` is `x % m = r`.

Source: Cristina Ballantine, *Combinatorial Proofs of Merca's Identities Involving the Sum of
Different Parts Congruent to r Modulo m in All Partitions of n*, INTEGERS 24 (2024),
Article A15, Section 1 (definition of `a_{r,m}(n)`). -/
public def sumDistinctPartsModEq (m r n : ℕ) : ℕ :=
  ∑ μ : n.Partition, ∑ x ∈ μ.parts.toFinset.filter (fun x => x % m = r), x

/-- `s_m(n)`: the sum of the different parts that appear at least `m` times in partitions of
`n`; such a part `j` contributes `j` once regardless of its multiplicity.

Source: Cristina Ballantine, *Combinatorial Proofs of Merca's Identities Involving the Sum of
Different Parts Congruent to r Modulo m in All Partitions of n*, INTEGERS 24 (2024),
Article A15, Section 1 (definition of `s_m(n)`). -/
public def sumDistinctPartsMultAtLeast (m n : ℕ) : ℕ :=
  ∑ μ : n.Partition, ∑ x ∈ μ.parts.toFinset.filter (fun x => m ≤ μ.parts.count x), x

/-- Characteristic values: `a_{r,m}(0) = s_m(0) = 0` (the empty partition has no parts), and
for the single partition `1` of `1`: `a_{0,1}(1) = s_1(1) = 1`, `s_2(1) = 0`.

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

/-- Dyson's rank `r(μ) = μ₁ - ℓ(μ)` of a partition (largest part minus number of parts),
with largest part `0` for the empty partition, so the empty partition has rank `0`.

Source: Cristina Ballantine, *Combinatorial Proofs of Merca's Identities Involving the Sum of
Different Parts Congruent to r Modulo m in All Partitions of n*, INTEGERS 24 (2024),
Article A15, Section 2 (definition of the rank before Theorem 8). -/
public def dysonRank {n : ℕ} (μ : n.Partition) : ℤ :=
  (μ.parts.sup : ℤ) - μ.parts.card

/-- Characteristic values of the rank: the empty partition and the partition `1` of `1` both
have rank `0`, so `N(0) = N(1) = 1`, `R(1) = 0` and the Garden of Eden count `G(0) = 0`.

Source: Cristina Ballantine, *Combinatorial Proofs of Merca's Identities Involving the Sum of
Different Parts Congruent to r Modulo m in All Partitions of n*, INTEGERS 24 (2024),
Article A15, Section 2 (definition of the rank before Theorem 8). -/
public theorem dysonRank_small_values (μ : Nat.Partition 0) (ν : Nat.Partition 1) :
    dysonRank μ = 0 ∧ dysonRank ν = 0 := by
  refine ⟨?_, ?_⟩ <;>
    simp [dysonRank, Nat.Partition.partition_zero_parts, Nat.Partition.partition_one_parts]

/-- The crank of a partition (Andrews and Garvan): the largest part if `1` is not a part,
and otherwise the number of parts larger than the number `ω(μ)` of ones, minus `ω(μ)`.

Source: Cristina Ballantine, *Combinatorial Proofs of Merca's Identities Involving the Sum of
Different Parts Congruent to r Modulo m in All Partitions of n*, INTEGERS 24 (2024),
Article A15, Section 2 (definition of the crank before Theorem 11). -/
public def partitionCrank {n : ℕ} (μ : n.Partition) : ℤ :=
  if μ.parts.count 1 = 0 then (μ.parts.sup : ℤ)
  else ((μ.parts.filter (fun x => μ.parts.count 1 < x)).card : ℤ) - μ.parts.count 1

/-- Characteristic values of the crank: the empty partition has crank `0` and the partition
`1` of `1` has crank `0 - 1 = -1`, so `C(0) = 1` and `C(1) = 0`.

Source: Cristina Ballantine, *Combinatorial Proofs of Merca's Identities Involving the Sum of
Different Parts Congruent to r Modulo m in All Partitions of n*, INTEGERS 24 (2024),
Article A15, Section 2 (definition of the crank before Theorem 11). -/
public theorem partitionCrank_small_values (μ : Nat.Partition 0) (ν : Nat.Partition 1) :
    partitionCrank μ = 0 ∧ partitionCrank ν = -1 := by
  refine ⟨?_, ?_⟩ <;>
    simp [partitionCrank, Nat.Partition.partition_zero_parts, Nat.Partition.partition_one_parts]

/-- Merca's identity (i): for `0 ≤ r < m`, `a_{r,m}(n) = ∑_{j ≥ 0} (mj + r) p(n - mj - r)`.

Source: Cristina Ballantine, *Combinatorial Proofs of Merca's Identities Involving the Sum of
Different Parts Congruent to r Modulo m in All Partitions of n*, INTEGERS 24 (2024),
Article A15, Theorem 1 (i) (`integers-2024-A15-thm-1`). -/
public theorem_wanted sumDistinctPartsModEq_eq_sum_partition (m r n : ℕ) (hrm : r < m) :
    sumDistinctPartsModEq m r n =
      ∑ j ∈ (Finset.range (n + 1)).filter (fun j => m * j + r ≤ n),
        (m * j + r) * Fintype.card (Nat.Partition (n - (m * j + r)))

/-- Merca's identity (ii): for `m ≥ 1`, `s_m(n) = ∑_{j ≥ 0} j p(n - mj)`. The paper's
hypothesis `0 ≤ r < m` forces `m ≥ 1`; for `m = 0` the right side diverges.

Source: Cristina Ballantine, *Combinatorial Proofs of Merca's Identities Involving the Sum of
Different Parts Congruent to r Modulo m in All Partitions of n*, INTEGERS 24 (2024),
Article A15, Theorem 1 (ii) (`integers-2024-A15-thm-1`). -/
public theorem_wanted sumDistinctPartsMultAtLeast_eq_sum_partition (m n : ℕ) (hm : 0 < m) :
    sumDistinctPartsMultAtLeast m n =
      ∑ j ∈ (Finset.range (n + 1)).filter (fun j => m * j ≤ n),
        j * Fintype.card (Nat.Partition (n - m * j))

/-- For `0 ≤ r < m`, `a_{r,m}(n) + 2 ∑_{k ≥ 1} (-1)^k a_{r,m}(n - k²)
= ∑_{j ≥ 0} (mj + r) p_{e-o}(n - mj - r)`, where `p_{e-o}(k) = ∑_{μ ⊢ k} (-1)^{ℓ(μ)}` is the
number of partitions of `k` with an even number of parts minus the number with an odd number.

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

/-- For `0 ≤ r < m`, `a_{r,m}(n) + 2 ∑_{k ≥ 1} (-1)^k a_{r,m}(n - 2k²)
= ∑_{j ≥ 0} (mj + r) q_odd(n - mj - r)`, with `q_odd(k)` the number of partitions of `k` into
distinct odd parts.

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

/-- For `0 ≤ r < m`, `∑_{k ≥ 0} (-1)^{k(k+1)/2} a_{r,m}(n - k(k+1)/2)
= ∑_{j ≥ 0} (mj + r) q((n - mj - r)/2)`, with `q(x)` the number of partitions of `x` into
distinct parts and `q(x) = 0` when `x` is not an integer.

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

/-- For `m ≥ 1`, `∑_{k ≥ 0} (-1)^{k(k+1)/2} s_m(n - k(k+1)/2) = ∑_{j ≥ 0} j q((n - mj)/2)`,
with `q(x)` the number of partitions of `x` into distinct parts and `q(x) = 0` when `x` is not
an integer. The paper says `m ≥ 0`; for `m = 0` the right side diverges.

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

/-- For `0 ≤ r < m`, `∑_{j ≥ 0} (-1)^j a_{r,m}(n - j(3j+1)/2) = ∑_{j ≥ 0} (mj + r) N(n - mj - r)`,
with `N(k)` the number of partitions of `k` with nonnegative rank.

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

/-- For `0 ≤ r < m`, `∑_{j ≥ 1} (-1)^{j+1} a_{r,m}(n - j(3j+1)/2)
= ∑_{j ≥ 0} (mj + r) R(n - mj - r)`, with `R(k)` the number of partitions of `k` with positive
rank.

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

/-- For `m ≥ 1`, `∑_{j ≥ 0} (-1)^j s_m(n - j(3j+1)/2) = ∑_{j ≥ 0} j N(n - mj)`, with `N(k)` the
number of partitions of `k` with nonnegative rank. The paper says `m ≥ 0`; for `m = 0` the
right side diverges.

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

/-- For `m ≥ 1`, `∑_{j ≥ 1} (-1)^{j+1} s_m(n - j(3j+1)/2) = ∑_{j ≥ 0} j R(n - mj)`, with `R(k)`
the number of partitions of `k` with positive rank. The paper says `m ≥ 0`; for `m = 0` the
right side diverges.

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

/-- For `0 ≤ r < m`, `∑_{j ≥ 1} (-1)^{j+1} a_{r,m}(n - 3j(j+1)/2)
= ∑_{j ≥ 0} (mj + r) G(n - mj - r)`, with `G(k)` the number of Garden of Eden partitions of
`k`, i.e. partitions of rank at most `-2` (so `G(0) = 0`). The record prints the left sum from
`j = 0`; that reading is false (`m = 1`, `r = 0`, `n = 1`: left side `-a_{0,1}(1) = -1`, right
side `0`); the paper's proof reduces the identity to `G(n) = ∑_{j ≥ 1} (-1)^{j+1}
p(n - 3j(j+1)/2)` and part (ii) sums from `j = 1`, which is the reading stated here.

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

/-- For `m ≥ 1`, `∑_{j ≥ 1} (-1)^{j+1} s_m(n - 3j(j+1)/2) = ∑_{j ≥ 0} j G(n - mj)`, with `G(k)`
the number of Garden of Eden partitions of `k` (rank at most `-2`, so `G(0) = 0`). The paper
says `m ≥ 0`; for `m = 0` the right side diverges.

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

/-- For `0 ≤ r < m`, `∑_{j ≥ 0} (-1)^j a_{r,m}(n - j(j+1)/2) = ∑_{j ≥ 0} (mj + r) C(n - mj - r)`,
with `C(k)` the number of partitions of `k` with nonnegative crank. Part (ii) of the paper's
theorem (with `D(k)`, positive crank) is omitted: it is false for this crank because
`D(1) = 0` while `p(1) - C(1) = 1` (`m = 2`, `r = 1`, `n = 2`: left side `1`, right side `0`).

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

/-- For `m ≥ 1`, `∑_{j ≥ 0} (-1)^j s_m(n - j(j+1)/2) = ∑_{j ≥ 0} j C(n - mj)`, with `C(k)` the
number of partitions of `k` with nonnegative crank. The paper says `m ≥ 0`; for `m = 0` the
right side diverges. Part (ii) (with `D(k)`, positive crank) is omitted: it is false for this
crank (`m = 1`, `n = 2`: left side `s_1(1) = 1`, right side `D(1) + 2 D(0) = 0`).

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
