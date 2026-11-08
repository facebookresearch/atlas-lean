/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Weighted Schreier-type sets and the Fibonacci sequence

Statements from Hùng Việt Chu and Zachary Louis Vasseur, *Weighted Schreier-type Sets and the
Fibonacci Sequence*, The Fibonacci Quarterly 62 (2024), no. 4.

For `k ∈ ℕ` and a finite set `E` of positive integers, `ω_k(E)` counts the elements of `E`
other than `k`, and `a_{k,n}` counts the sets `E ⊆ {1, …, n}` that are empty or satisfy
`ω_k(E) < min E`. The condition `ω_k(E) < min E` is encoded as `ω_k(E) < m` for every `m ∈ E`,
which is vacuous for `E = ∅`. The definitions and the iterated partial sums of Section 3 are
taken from the arXiv version (arXiv:2405.19352v1), whose Section 3 numbering is shifted
against the journal labels used below: journal Proposition 3.1 is arXiv Proposition 3.2,
journal Lemmas 3.2-3.4 are arXiv Lemmas 3.3-3.5, and journal Proposition 3.5 is arXiv
Proposition 3.1.
-/

namespace MetaMathlibExt

@[expose] public section

/-- `a_{k,n}`, the number of sets `E ⊆ {1, …, n}` that are empty or satisfy
`ω_k(E) < min E`, where `ω_k(E)` is the number of elements of `E` different from `k`.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Weighted Schreier-type Sets and the
Fibonacci Sequence*, The Fibonacci Quarterly 62 (2024), no. 4, Section 1 (definition of
`A_{k,n}` and `a_{k,n}`). -/
public def weightedSchreierCount (k n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter fun E => ∀ m ∈ E, (E.filter (· ≠ k)).card < m).card

/-- `a_{1,1} = 2` (first entry of Table 1).

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Weighted Schreier-type Sets and the
Fibonacci Sequence*, The Fibonacci Quarterly 62 (2024), no. 4, Section 1, Table 1. -/
public theorem weightedSchreierCount_one_one : weightedSchreierCount 1 1 = 2 := by
  decide

/-- `a_{2,1} = 1` (Table 1).

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Weighted Schreier-type Sets and the
Fibonacci Sequence*, The Fibonacci Quarterly 62 (2024), no. 4, Section 1, Table 1. -/
public theorem weightedSchreierCount_two_one : weightedSchreierCount 2 1 = 1 := by
  decide

/-- `a_{3,3} = 4` (Table 1).

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Weighted Schreier-type Sets and the
Fibonacci Sequence*, The Fibonacci Quarterly 62 (2024), no. 4, Section 1, Table 1. -/
public theorem weightedSchreierCount_three_three : weightedSchreierCount 3 3 = 4 := by
  decide

/-- `a_{1,4} = 6` (Table 1).

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Weighted Schreier-type Sets and the
Fibonacci Sequence*, The Fibonacci Quarterly 62 (2024), no. 4, Section 1, Table 1. -/
public theorem weightedSchreierCount_one_four : weightedSchreierCount 1 4 = 6 := by
  decide

/-- The sequences `t^s_{k,n}` of Section 3: for a seed sequence `s = (b_n)` and a sequence
`(a_n)`, `t^s_{0,n} = a_n` and `t^s_{k+1,n} = b_k + ∑_{i<n} t^s_{k,i}`, i.e. the partial sum
operator `P_{b_k}` applied to `(t^s_{k,n})_n`.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Weighted Schreier-type Sets and the
Fibonacci Sequence*, The Fibonacci Quarterly 62 (2024), no. 4, Section 3 (partial sum
operator `P_b` and the sequences `t^s_{k,n}`). -/
public def seededPartialSums {M : Type*} [AddCommMonoid M] (s a : ℕ → M) : ℕ → ℕ → M
  | 0, n => a n
  | k + 1, n => s k + ∑ i ∈ Finset.range n, seededPartialSums s a k i

/-- `P^{(k)}((a_n)_{n ≥ 0})(m)`, the `k`-fold partial sum of `(a_n)`: the sequence
`t^s_{k,m}` for the zero seed sequence `s`.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Weighted Schreier-type Sets and the
Fibonacci Sequence*, The Fibonacci Quarterly 62 (2024), no. 4, Section 3 (definition of
`P^{(k)}`). -/
public def iteratedPartialSum {M : Type*} [AddCommMonoid M] (k : ℕ) (a : ℕ → M) (m : ℕ) : M :=
  seededPartialSums 0 a k m

/-- `t^s_{k+1,0} = b_k`: each partial-sum step starts at its seed.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Weighted Schreier-type Sets and the
Fibonacci Sequence*, The Fibonacci Quarterly 62 (2024), no. 4, Section 3 (partial sum
operator `P_b`). -/
public theorem seededPartialSums_succ_zero {M : Type*} [AddCommMonoid M] (s a : ℕ → M)
    (k : ℕ) : seededPartialSums s a (k + 1) 0 = s k := by
  simp [seededPartialSums]

/-- `P^{(1)}((a_n))(m) = ∑_{i<m} a_i`.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Weighted Schreier-type Sets and the
Fibonacci Sequence*, The Fibonacci Quarterly 62 (2024), no. 4, Section 3 (definition of
`P^{(k)}`). -/
public theorem iteratedPartialSum_one {M : Type*} [AddCommMonoid M] (a : ℕ → M) (m : ℕ) :
    iteratedPartialSum 1 a m = ∑ i ∈ Finset.range m, a i := by
  simp [iteratedPartialSum, seededPartialSums]

/-- `P^{(k+1)}((a_n))(m+1) = P^{(k+1)}((a_n))(m) + P^{(k)}((a_n))(m)`.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Weighted Schreier-type Sets and the
Fibonacci Sequence*, The Fibonacci Quarterly 62 (2024), no. 4, Section 3 (definition of
`P^{(k)}`; recurrence used in the proofs of Lemmas 3.3 and 3.4). -/
public theorem iteratedPartialSum_succ_succ {M : Type*} [AddCommMonoid M] (a : ℕ → M)
    (k m : ℕ) :
    iteratedPartialSum (k + 1) a (m + 1) =
      iteratedPartialSum (k + 1) a m + iteratedPartialSum k a m := by
  simp [iteratedPartialSum, seededPartialSums, Finset.sum_range_succ]

/-- For `n ≥ 1`, `a_{n,n} = 2 F_n`.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Weighted Schreier-type Sets and the
Fibonacci Sequence*, The Fibonacci Quarterly 62 (2024), no. 4, Theorem 1.1
(`fq-2024-chu08302024rev-thm-1.1`). -/
public theorem_wanted weightedSchreierCount_diag {n : ℕ} (hn : 1 ≤ n) :
    weightedSchreierCount n n = 2 * Nat.fib n

/-- First case of Theorem 1.2: `a_{1,1+ℓ} = F_{ℓ+2} + 1` for `ℓ ≥ 0`.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Weighted Schreier-type Sets and the
Fibonacci Sequence*, The Fibonacci Quarterly 62 (2024), no. 4, Theorem 1.2, case `k = 1`
(`fq-2024-chu08302024rev-thm-1.2`). -/
public theorem_wanted weightedSchreierCount_one (l : ℕ) :
    weightedSchreierCount 1 (1 + l) = Nat.fib (l + 2) + 1

/-- Second case of Theorem 1.2: for `k ≥ 2` and `ℓ ≥ 0`,
`a_{k,k+ℓ} = 2 ∑_{i=0}^{k-2} C(ℓ,i) F_{k-i} + 2 C(ℓ,k-1) + ∑_{j=1}^{ℓ} C(j, ℓ-j+k)`.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Weighted Schreier-type Sets and the
Fibonacci Sequence*, The Fibonacci Quarterly 62 (2024), no. 4, Theorem 1.2, case `k ≥ 2`,
`ℓ ≥ 0` (`fq-2024-chu08302024rev-thm-1.2`). -/
public theorem_wanted weightedSchreierCount_add {k : ℕ} (hk : 2 ≤ k) (l : ℕ) :
    weightedSchreierCount k (k + l) =
      2 * ∑ i ∈ Finset.range (k - 1), l.choose i * Nat.fib (k - i) + 2 * l.choose (k - 1) +
        ∑ j ∈ Finset.Icc 1 l, j.choose (l - j + k)

/-- Third case of Theorem 1.2, reindexed by `m = k + ℓ`: for `k ≥ 2` and `-k < ℓ < 0`,
i.e. `0 < m < k`, `a_{k,m} = F_{m+1}`.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Weighted Schreier-type Sets and the
Fibonacci Sequence*, The Fibonacci Quarterly 62 (2024), no. 4, Theorem 1.2, case `k ≥ 2`,
`-k < ℓ < 0` (`fq-2024-chu08302024rev-thm-1.2`). -/
public theorem_wanted weightedSchreierCount_of_pos_of_lt {k m : ℕ} (hk : 2 ≤ k) (hm : 0 < m)
    (hmk : m < k) : weightedSchreierCount k m = Nat.fib (m + 1)

/-- For `ℓ ≥ 0` and `k ≥ ℓ + 2`, `a_{k,k+ℓ} = 2 F_{k+ℓ}`.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Weighted Schreier-type Sets and the
Fibonacci Sequence*, The Fibonacci Quarterly 62 (2024), no. 4, Theorem 1.4
(`fq-2024-chu08302024rev-thm-1.4`). -/
public theorem_wanted weightedSchreierCount_add_of_le {k l : ℕ} (hkl : l + 2 ≤ k) :
    weightedSchreierCount k (k + l) = 2 * Nat.fib (k + l)

/-- For `k ≥ 1` and `n > max{k, 2}`, `a_{k,n} = a_{k,n-1} + a_{k-1,n-2}`. At `k = 1` the
term `a_{0,n-2}` is the same count with `ω_0(E) = |E|`.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Weighted Schreier-type Sets and the
Fibonacci Sequence*, The Fibonacci Quarterly 62 (2024), no. 4, Proposition 3.1
(`fq-2024-chu08302024rev-prop-3.1`). -/
public theorem_wanted weightedSchreierCount_recurrence {k n : ℕ} (hk : 1 ≤ k) (hkn : k < n)
    (h2n : 2 < n) :
    weightedSchreierCount k n =
      weightedSchreierCount k (n - 1) + weightedSchreierCount (k - 1) (n - 2)

/-- Comparison of seeded and unseeded iterated partial sums: for a seed sequence
`s = (b_n)`, `t^s_{k,n} - t^0_{k,n} = ∑_{i=0}^{k-1} C(n,i) b_{k-1-i}` for all `n ≥ 0`.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Weighted Schreier-type Sets and the
Fibonacci Sequence*, The Fibonacci Quarterly 62 (2024), no. 4, Lemma 3.2
(`fq-2024-chu08302024rev-lem-3.2`). -/
public theorem_wanted seededPartialSums_sub_zero {R : Type*} [CommRing R] (b a : ℕ → R)
    (k n : ℕ) :
    seededPartialSums b a k n - seededPartialSums 0 a k n =
      ∑ i ∈ Finset.range k, (n.choose i : R) * b (k - 1 - i)

/-- Shifting a sequence by `1` shifts its `k`-fold partial sums by binomial coefficients:
`P^{(k)}((a_n + 1))(m) - P^{(k)}((a_n))(m) = C(m,k)` for all `m ≥ 0`.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Weighted Schreier-type Sets and the
Fibonacci Sequence*, The Fibonacci Quarterly 62 (2024), no. 4, Lemma 3.3
(`fq-2024-chu08302024rev-lem-3.3`). -/
public theorem_wanted iteratedPartialSum_add_one_sub {R : Type*} [CommRing R] (a : ℕ → R)
    (k m : ℕ) :
    iteratedPartialSum k (fun n => a n + 1) m - iteratedPartialSum k a m = (m.choose k : R)

/-- For all `k, ℓ ≥ 0`,
`P^{(k)}((F_{n+2}))(ℓ) = P^{(k)}((F_n))(ℓ) + P^{(k)}((F_n))(ℓ+1)`.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Weighted Schreier-type Sets and the
Fibonacci Sequence*, The Fibonacci Quarterly 62 (2024), no. 4, Lemma 3.4
(`fq-2024-chu08302024rev-lem-3.4`). -/
public theorem_wanted iteratedPartialSum_fib_add_two (k l : ℕ) :
    iteratedPartialSum k (fun n => Nat.fib (n + 2)) l =
      iteratedPartialSum k Nat.fib l + iteratedPartialSum k Nat.fib (l + 1)

/-- For `k > n`, `a_{k,n} = F_{n+1}`. Stated for all `n < k`, including `n = 0`
(`a_{k,0} = 1 = F_1`), where the paper takes `n ∈ ℕ` positive.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Weighted Schreier-type Sets and the
Fibonacci Sequence*, The Fibonacci Quarterly 62 (2024), no. 4, Proposition 3.5
(`fq-2024-chu08302024rev-prop-3.5`). -/
public theorem_wanted weightedSchreierCount_of_lt {k n : ℕ} (hnk : n < k) :
    weightedSchreierCount k n = Nat.fib (n + 1)

end

end MetaMathlibExt
