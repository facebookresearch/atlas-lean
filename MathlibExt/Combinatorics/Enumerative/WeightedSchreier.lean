/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Weighted Schreier-type sets and the Fibonacci sequence

For weight zero at `1`, the admissible sets consist of the nonmaximal Schreier sets
and the singleton `{1}`. Grouping the nonmaximal sets by cardinality gives the
binomial sum for a Fibonacci number.

This file also defines the seeded and iterated partial sums used by Hùng Việt Chu and
Zachary Louis Vasseur in *Weighted Schreier-type Sets and the Fibonacci Sequence*.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Weighted Schreier-type sets.** For natural numbers $k$ and $n$, let $\omega_k(E)$ denote the
number of elements of a finite set $E$ that are different from $k$. The weighted Schreier count
$a_{k,n}$ is the number of subsets $E \subseteq \{1, \dots, n\}$ that are empty or satisfy
$\omega_k(E) < \min E$.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Weighted Schreier-type Sets and the
Fibonacci Sequence*, The Fibonacci Quarterly 62 (2024), no. 4, Section 1 (definition of
`A_{k,n}` and `a_{k,n}`). -/
public def weightedSchreierCount (k n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter fun E => ∀ m ∈ E, (E.filter (· ≠ k)).card < m).card

/-- **Weighted Schreier count $a_{1,1}$.** The weighted Schreier count $a_{1,1}$ equals $2$.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Weighted Schreier-type Sets and the
Fibonacci Sequence*, The Fibonacci Quarterly 62 (2024), no. 4, Section 1, Table 1. -/
public theorem weightedSchreierCount_one_one : weightedSchreierCount 1 1 = 2 := by
  decide

/-- **Weighted Schreier count $a_{2,1}$.** The weighted Schreier count $a_{2,1}$ equals $1$.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Weighted Schreier-type Sets and the
Fibonacci Sequence*, The Fibonacci Quarterly 62 (2024), no. 4, Section 1, Table 1. -/
public theorem weightedSchreierCount_two_one : weightedSchreierCount 2 1 = 1 := by
  decide

/-- **Weighted Schreier count $a_{3,3}$.** The weighted Schreier count $a_{3,3}$ equals $4$.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Weighted Schreier-type Sets and the
Fibonacci Sequence*, The Fibonacci Quarterly 62 (2024), no. 4, Section 1, Table 1. -/
public theorem weightedSchreierCount_three_three : weightedSchreierCount 3 3 = 4 := by
  decide

/-- **Weighted Schreier count $a_{1,4}$.** The weighted Schreier count $a_{1,4}$ equals $6$.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Weighted Schreier-type Sets and the
Fibonacci Sequence*, The Fibonacci Quarterly 62 (2024), no. 4, Section 1, Table 1. -/
public theorem weightedSchreierCount_one_four : weightedSchreierCount 1 4 = 6 := by
  decide

namespace weightedSchreierCount_one

open Finset

/-- The nonmaximal Schreier subsets of the interval, including the empty set. -/
private def nonmaximalSets (n : ℕ) : Finset (Finset ℕ) :=
  (Icc 1 n).powerset.filter fun E => ∀ m ∈ E, E.card < m

private theorem card_nonmaximalSets (n : ℕ) : (nonmaximalSets n).card = Nat.fib (n + 1) := by
  -- Index the sets of size r by the pair (n - r, r) in the Fibonacci binomial sum.
  let index (E : Finset ℕ) := (n - E.card, E.card)
  have hindex : Set.MapsTo index (nonmaximalSets n) (antidiagonal n) := by
    intro E hE
    have hsub := mem_powerset.mp (mem_filter.mp hE).1
    have hcard : E.card ≤ n := by simpa using card_le_card hsub
    exact mem_antidiagonal.mpr (Nat.sub_add_cancel hcard)
  rw [card_eq_sum_card_fiberwise hindex, Nat.fib_succ_eq_sum_choose]
  apply sum_congr rfl
  rintro ⟨a, r⟩ hp
  have har : a + r = n := mem_antidiagonal.mp hp
  -- Each such set consists of r elements chosen from the interval (r, n].
  have hfiber : ((nonmaximalSets n).filter fun E => index E = (a, r)) =
      (Ioc r n).powersetCard r := by
    ext E
    simp only [nonmaximalSets, mem_filter, mem_powerset, index, Prod.mk.injEq,
      mem_powersetCard, subset_iff, mem_Icc, mem_Ioc]
    grind
  rw [hfiber, card_powersetCard, Nat.card_Ioc, show n - r = a by omega]

end weightedSchreierCount_one

open Finset weightedSchreierCount_one in
/-- **Weighted Schreier counts for $k = 1$.** For every natural number $\ell$, the weighted
Schreier count satisfies $a_{1,1+\ell} = F_{\ell+2} + 1$, where $F_j$ is the $j$-th Fibonacci
number ($F_0 = 0$, $F_1 = 1$).

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Weighted Schreier-type Sets and the
Fibonacci Sequence*, The Fibonacci Quarterly 62 (2024), no. 4, Theorem 1.2, case `k = 1`
(`fq-2024-chu08302024rev-thm-1.2`). -/
public theorem weightedSchreierCount_one (l : ℕ) :
    weightedSchreierCount 1 (1 + l) = Nat.fib (l + 2) + 1 := by
  have hfamily : ((Icc 1 (1 + l)).powerset.filter fun E =>
      ∀ m ∈ E, (E.filter (· ≠ 1)).card < m) = insert {1} (nonmaximalSets (1 + l)) := by
    ext E
    simp only [nonmaximalSets, mem_insert, mem_filter, mem_powerset, filter_ne']
    constructor
    · rintro ⟨hsub, hlt⟩
      by_cases h : 1 ∈ E
      · have hempty : E.erase 1 = ∅ := card_eq_zero.mp (Nat.lt_one_iff.mp (hlt 1 h))
        exact Or.inl (by simpa [hempty] using (insert_erase h).symm)
      · exact Or.inr ⟨hsub, by simpa [h] using hlt⟩
    · rintro (rfl | ⟨hsub, hlt⟩)
      · simp
      · exact ⟨hsub, fun m hm => (card_le_card (erase_subset ..)).trans_lt (hlt m hm)⟩
  unfold weightedSchreierCount
  rw [hfamily, card_insert_of_notMem, card_nonmaximalSets, Nat.add_comm 1 l]
  simp [nonmaximalSets]

open Finset weightedSchreierCount_one in
/-- **Weighted Schreier counts for $n < k$.** For all natural numbers $n < k$, the weighted
Schreier count satisfies $a_{k,n} = F_{n+1}$, where $F_j$ is the $j$-th Fibonacci number
($F_0 = 0$, $F_1 = 1$).

This includes $n = 0$, where $a_{k,0} = 1 = F_1$; the source takes $n$ positive.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Weighted Schreier-type Sets and the
Fibonacci Sequence*, The Fibonacci Quarterly 62 (2024), no. 4, Proposition 3.5
(`fq-2024-chu08302024rev-prop-3.5`). -/
public theorem weightedSchreierCount_of_lt {k n : ℕ} (hnk : n < k) :
    weightedSchreierCount k n = Nat.fib (n + 1) := by
  rw [weightedSchreierCount, ← card_nonmaximalSets n, nonmaximalSets]
  apply congrArg Finset.card
  apply filter_congr
  intro E hE
  have hk : k ∉ E := fun h => hnk.not_ge (mem_Icc.mp (mem_powerset.mp hE h)).2
  simp [filter_ne', hk]

set_option linter.unusedVariables false in
/-- **Weighted Schreier counts for $0 < m < k$.** For natural numbers $k \ge 2$ and $m$ with
$0 < m < k$, the weighted Schreier count satisfies $a_{k,m} = F_{m+1}$, where $F_j$ is the
$j$-th Fibonacci number ($F_0 = 0$, $F_1 = 1$).

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Weighted Schreier-type Sets and the
Fibonacci Sequence*, The Fibonacci Quarterly 62 (2024), no. 4, Theorem 1.2, case `k ≥ 2`,
`-k < ℓ < 0` (`fq-2024-chu08302024rev-thm-1.2`). -/
public theorem weightedSchreierCount_of_pos_of_lt {k m : ℕ} (hk : 2 ≤ k) (hm : 0 < m)
    (hmk : m < k) : weightedSchreierCount k m = Nat.fib (m + 1) :=
  weightedSchreierCount_of_lt hmk

/-- **Seeded partial sums.** Let $M$ be an additive commutative monoid, and let
$s = (s_n)_{n \ge 0}$ (the seed sequence) and $a = (a_n)_{n \ge 0}$ be sequences in $M$. The
seeded partial sums $t^s_{k,n}$, for $k, n \ge 0$, are defined by recursion on $k$:
$t^s_{0,n} = a_n$ and $t^s_{k+1,n} = s_k + \sum_{i<n} t^s_{k,i}$.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Weighted Schreier-type Sets and the
Fibonacci Sequence*, The Fibonacci Quarterly 62 (2024), no. 4, Section 3 (partial sum
operator `P_b` and the sequences `t^s_{k,n}`). -/
public def seededPartialSums {M : Type*} [AddCommMonoid M] (s a : ℕ → M) : ℕ → ℕ → M
  | 0, n => a n
  | k + 1, n => s k + ∑ i ∈ Finset.range n, seededPartialSums s a k i

/-- **Iterated partial sums.** Let $M$ be an additive commutative monoid and let
$a = (a_n)_{n \ge 0}$ be a sequence in $M$. For $k, m \ge 0$, the $k$-fold iterated partial sum
$P^{(k)}(a)(m)$ is the seeded partial sum $t^s_{k,m}$ of $a$ for the zero seed sequence $s = 0$.
Thus $P^{(0)}(a)(m) = a_m$ and $P^{(k+1)}(a)(m) = \sum_{i<m} P^{(k)}(a)(i)$.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Weighted Schreier-type Sets and the
Fibonacci Sequence*, The Fibonacci Quarterly 62 (2024), no. 4, Section 3 (definition of
`P^{(k)}`). -/
public def iteratedPartialSum {M : Type*} [AddCommMonoid M] (k : ℕ) (a : ℕ → M) (m : ℕ) : M :=
  seededPartialSums 0 a k m

/-- **Seeded partial sums start at the seed.** Let $M$ be an additive commutative monoid, let
$s = (s_n)_{n \ge 0}$ and $a = (a_n)_{n \ge 0}$ be sequences in $M$, and write $t^s_{k,n}$ for
the seeded partial sums of $a$ with seed sequence $s$. Then $t^s_{k+1,0} = s_k$ for every
$k \ge 0$.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Weighted Schreier-type Sets and the
Fibonacci Sequence*, The Fibonacci Quarterly 62 (2024), no. 4, Section 3 (partial sum
operator `P_b`). -/
public theorem seededPartialSums_succ_zero {M : Type*} [AddCommMonoid M] (s a : ℕ → M)
    (k : ℕ) : seededPartialSums s a (k + 1) 0 = s k := by
  simp [seededPartialSums]

/-- **Effect of the seed on seeded partial sums.** Let $R$ be a commutative ring, let
$a = (a_n)_{n \ge 0}$ and $b = (b_n)_{n \ge 0}$ be sequences in $R$, and write $t^b_{k,n}$ for
the seeded partial sums of $a$ with seed sequence $b$ and $t^0_{k,n}$ for those with the zero
seed sequence. Then for all $k, n \ge 0$,
$t^b_{k,n} - t^0_{k,n} = \sum_{i<k} \binom{n}{i} b_{k-1-i}$, where the binomial coefficients
are read as elements of $R$.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Weighted Schreier-type Sets and the
Fibonacci Sequence*, The Fibonacci Quarterly 62 (2024), no. 4, Lemma 3.2
(`fq-2024-chu08302024rev-lem-3.2`). -/
public theorem seededPartialSums_sub_zero {R : Type*} [CommRing R] (b a : ℕ → R)
    (k n : ℕ) :
    seededPartialSums b a k n - seededPartialSums 0 a k n =
      ∑ i ∈ Finset.range k, (n.choose i : R) * b (k - 1 - i) := by
  induction k generalizing n with
  | zero => simp [seededPartialSums]
  | succ k ih =>
    induction n with
    | zero => simp [seededPartialSums_succ_zero, Finset.sum_range_succ']
    | succ n hn =>
      have step (s : ℕ → R) : seededPartialSums s a (k + 1) (n + 1) =
          seededPartialSums s a (k + 1) n + seededPartialSums s a k n := by
        simp [seededPartialSums, Finset.sum_range_succ, add_assoc]
      rw [step, step, add_sub_add_comm, hn, ih]
      simp only [Finset.sum_range_succ' _ k, Nat.add_sub_cancel, Nat.sub_zero,
        Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.choose_succ_succ', Nat.cast_add,
        add_mul, Finset.sum_add_distrib, Nat.sub_sub, Nat.add_comm 1]
      ac_rfl

/-- **The first iterated partial sum.** Let $M$ be an additive commutative monoid and let
$(a_n)_{n \ge 0}$ be a sequence in $M$. For every $m \ge 0$, the $1$-fold iterated partial sum
of $(a_n)$ at $m$ is the ordinary partial sum: $P^{(1)}((a_n)_{n \ge 0})(m) = \sum_{i<m} a_i$.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Weighted Schreier-type Sets and the
Fibonacci Sequence*, The Fibonacci Quarterly 62 (2024), no. 4, Section 3 (definition of
`P^{(k)}`). -/
public theorem iteratedPartialSum_one {M : Type*} [AddCommMonoid M] (a : ℕ → M) (m : ℕ) :
    iteratedPartialSum 1 a m = ∑ i ∈ Finset.range m, a i := by
  simp [iteratedPartialSum, seededPartialSums]

/-- **Recurrence for iterated partial sums.** Let $M$ be an additive commutative monoid, let
$a = (a_n)_{n \ge 0}$ be a sequence in $M$, and write $P^{(k)}(a)(m)$ for its $k$-fold iterated
partial sum at $m$. Then for all $k, m \ge 0$,
$P^{(k+1)}(a)(m+1) = P^{(k+1)}(a)(m) + P^{(k)}(a)(m)$.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Weighted Schreier-type Sets and the
Fibonacci Sequence*, The Fibonacci Quarterly 62 (2024), no. 4, Section 3 (definition of
`P^{(k)}`; recurrence used in the proofs of Lemmas 3.3 and 3.4). -/
public theorem iteratedPartialSum_succ_succ {M : Type*} [AddCommMonoid M] (a : ℕ → M)
    (k m : ℕ) :
    iteratedPartialSum (k + 1) a (m + 1) =
      iteratedPartialSum (k + 1) a m + iteratedPartialSum k a m := by
  simp [iteratedPartialSum, seededPartialSums, Finset.sum_range_succ]

/-- **Adding one to a sequence shifts its iterated partial sums by a binomial coefficient.**
Let $R$ be a commutative ring, let $(a_n)_{n \ge 0}$ be a sequence in $R$, and let $k, m \ge 0$.
Writing $P^{(k)}(x)(m)$ for the $k$-fold iterated partial sum of a sequence $x$ at $m$, we have
$P^{(k)}((a_n + 1)_{n \ge 0})(m) - P^{(k)}((a_n)_{n \ge 0})(m) = \binom{m}{k}$, where
$\binom{m}{k}$ is read as an element of $R$.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Weighted Schreier-type Sets and the
Fibonacci Sequence*, The Fibonacci Quarterly 62 (2024), no. 4, Lemma 3.3
(`fq-2024-chu08302024rev-lem-3.3`). -/
public theorem iteratedPartialSum_add_one_sub {R : Type*} [CommRing R] (a : ℕ → R)
    (k m : ℕ) :
    iteratedPartialSum k (fun n => a n + 1) m - iteratedPartialSum k a m = (m.choose k : R) := by
  induction k generalizing m with
  | zero => simp [iteratedPartialSum, seededPartialSums]
  | succ k ih =>
    induction m with
    | zero => simp [iteratedPartialSum, seededPartialSums]
    | succ m ihm =>
      rw [iteratedPartialSum_succ_succ, iteratedPartialSum_succ_succ, add_sub_add_comm,
        ihm, ih m, Nat.choose_succ_succ, Nat.cast_add]
      exact add_comm _ _

/-- **Iterated partial sums of shifted Fibonacci numbers.** Let $F_n$ denote the Fibonacci
numbers, with $F_0 = 0$ and $F_1 = 1$, and write $P^{(k)}(x)(m)$ for the $k$-fold iterated
partial sum of a sequence $x$ of natural numbers at $m$. Then for all $k, \ell \ge 0$,
$P^{(k)}((F_{n+2})_{n \ge 0})(\ell) = P^{(k)}((F_n)_{n \ge 0})(\ell) +
P^{(k)}((F_n)_{n \ge 0})(\ell + 1)$.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Weighted Schreier-type Sets and the
Fibonacci Sequence*, The Fibonacci Quarterly 62 (2024), no. 4, Lemma 3.4
(`fq-2024-chu08302024rev-lem-3.4`). -/
public theorem iteratedPartialSum_fib_add_two (k l : ℕ) :
    iteratedPartialSum k (fun n => Nat.fib (n + 2)) l =
      iteratedPartialSum k Nat.fib l + iteratedPartialSum k Nat.fib (l + 1) := by
  unfold iteratedPartialSum
  induction k generalizing l with
  | zero => exact Nat.fib_add_two
  | succ k ih =>
    have hzero : seededPartialSums 0 Nat.fib k 0 = 0 := by
      cases k <;> simp [seededPartialSums]
    simp only [seededPartialSums, Pi.zero_apply, zero_add, ih, Finset.sum_add_distrib]
    rw [Finset.sum_range_succ' (seededPartialSums 0 Nat.fib k) l, hzero, Nat.add_zero]

end

end MetaMathlibExt
