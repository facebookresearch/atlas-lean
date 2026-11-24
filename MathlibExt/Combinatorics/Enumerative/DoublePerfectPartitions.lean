/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.Multiset.Powerset
public import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.Ring.Multiset

/-!
# Perfect and double-perfect partitions

A double-perfect partition of order `r` has two distinct subpartitions at each interior sum
and one at each end. The theorem `isDoublePerfectOfOrder_add_replicate` shows that inserting
copies of the total minus `r` preserves this pattern. This module also defines the perfect
partitions associated to ordered factorizations and counts those factorizations.
The theorem `exists_partition_unique_subsums_but_one_iff` classifies the possible counts
when a single interior sum is allowed to have more than one subpartition.
The theorem `typeADoublePerfect_forms` gives the two ordered-factorization shapes of
Type-A double-perfect partitions.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Number of subpartitions with a given sum.** For a multiset $\lambda$ of natural numbers and
$m \in \mathbb{N}$, the number of partitions of $m$ contained in $\lambda$ is the number of
distinct sub-multisets of $\lambda$ whose elements sum to $m$.

Sub-multisets are counted as multisets, not by the positions of their parts: the paper's example
counts $(1)$ once in $(1^5, 2)$.

Source: Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025),
Article A109, Section 1 (Definitions 1, 3 and the example `(1^5, 2) ⊢ 7` after Definition 3). -/
def subpartitionCount (l : Multiset ℕ) (m : ℕ) : ℕ :=
  (l.powerset.toFinset.filter fun s => s.sum = m).card

/-- **Perfect partition.** Let $n$ be a natural number. A multiset $\lambda$ of natural numbers
is a perfect partition of $n$ when its elements are positive, they sum to $n$, and for every
integer $m$ with $1 \le m \le n$ exactly one partition of $m$ is contained in $\lambda$, that is,
exactly one sub-multiset of $\lambda$ has sum $m$ (equal sub-multisets are counted once).

Source: Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025),
Article A109, Definition 1. -/
def IsPerfectPartition (n : ℕ) (l : Multiset ℕ) : Prop :=
  (∀ a ∈ l, 0 < a) ∧ l.sum = n ∧ ∀ m ∈ Finset.Icc 1 n, subpartitionCount l m = 1

/-- **Double-perfect partitions of higher order.** A double-perfect partition of $N$ of order $r$
is a finite multiset $\lambda$ of positive integers with sum $N$ such that, for every integer $m$
with $1 \le m \le N$, the number of distinct sub-multisets of $\lambda$ with sum $m$ is $2$ if
$r + 1 \le m \le N - r - 1$ and $1$ otherwise. Their set is denoted $U_r(N)$; order $1$ gives the
double-perfect partitions.

Source: Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025),
Article A109, Definition 4 and display (11). -/
def IsDoublePerfectOfOrder (r N : ℕ) (l : Multiset ℕ) : Prop :=
  (∀ a ∈ l, 0 < a) ∧ l.sum = N ∧
    ∀ m ∈ Finset.Icc 1 N,
      subpartitionCount l m = if r + 1 ≤ m ∧ m + r + 1 ≤ N then 2 else 1

/-- **Type-A double-perfect partition.** Let $r$ and $N$ be natural numbers. A multiset
$\lambda$ of natural numbers is a Type-A double-perfect partition of $N$ of order $r$ when
$\lambda$ is a double-perfect partition of $N$ of order $r$ and there is a perfect partition
$\beta$ of $N - r - 1$ (read as $0$ when $N \le r$) such that $\lambda$ is $\beta$ with $r + 1$
parts equal to $1$ added, or $\beta$ with one part equal to $r + 1$ added. The set of these
partitions is denoted $D_r(N)$.

Source: Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025),
Article A109, Section 3 (definition of `D_r(N)` after display (12)). -/
def IsTypeADoublePerfect (r N : ℕ) (l : Multiset ℕ) : Prop :=
  IsDoublePerfectOfOrder r N l ∧ ∃ β, IsPerfectPartition (N - r - 1) β ∧
    (l = β + Multiset.replicate (r + 1) 1 ∨ l = β + {r + 1})

/-- **MacMahon's partition of an ordered factorization.** To a finite sequence
$(a_1, \dots, a_k)$ of natural numbers, read as the ordered factorization $a_1 a_2 \cdots a_k$,
attach the multiset of parts
$(1^{a_1-1}, a_1^{a_2-1}, (a_1a_2)^{a_3-1}, \dots, (a_1\cdots a_{k-1})^{a_k-1})$, where $x^e$
denotes $e$ parts equal to $x$ and an exponent $a_i - 1$ is read as $0$ when $a_i = 0$. In
particular the empty sequence gives the empty multiset.

For factors $a_i \ge 2$ this is MacMahon's bijection (1): for each $n \ge 0$, it maps the ordered
factorizations of $n + 1$ into such factors onto the perfect partitions of $n$.

Source: Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025),
Article A109, display (1). -/
def perfectPartitionOfFactorization : List ℕ → Multiset ℕ
  | [] => 0
  | a :: as => Multiset.replicate (a - 1) 1 + (perfectPartitionOfFactorization as).map (a * ·)

/-- **MacMahon's partition of the factorization 2 · 3.** MacMahon's bijection sends the ordered
factorization $6 = 2 \cdot 3$ to the partition $(1, 2^2) = (1, 2, 2)$ of $5$.

Source: Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025),
Article A109, Table 1. -/
theorem perfectPartitionOfFactorization_two_three :
    perfectPartitionOfFactorization [2, 3] = {1, 2, 2} := by
  decide

/-- **The partition of a factorization sums to the product minus one.** Let $k \ge 0$ and let
$a_1, \dots, a_k \ge 1$ be integers. The parts of the partition
$(1^{a_1-1}, a_1^{a_2-1}, (a_1a_2)^{a_3-1}, \dots, (a_1\cdots a_{k-1})^{a_k-1})$ that MacMahon's
bijection attaches to the ordered factorization $a_1 a_2 \cdots a_k$, where $x^e$ denotes $e$
parts equal to $x$, sum to $a_1 a_2 \cdots a_k - 1$.

Source: Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025),
Article A109, display (1) (perfect partitions of `n` correspond to factorizations of `n + 1`). -/
theorem perfectPartitionOfFactorization_sum_add_one (a : List ℕ) (ha : ∀ x ∈ a, 1 ≤ x) :
    (perfectPartitionOfFactorization a).sum + 1 = a.prod := by
  induction a with
  | nil => simp [perfectPartitionOfFactorization]
  | cons x xs ih =>
    have hx := ha x (by simp)
    have h := ih fun y hy => ha y (by simp [hy])
    obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
    simp only [perfectPartitionOfFactorization, Multiset.sum_add, Multiset.sum_replicate,
      Nat.nsmul_eq_mul, mul_one, List.prod_cons, Nat.add_sub_cancel]
    rw [Multiset.sum_map_mul_left, Multiset.map_id', ← h, Nat.mul_add, Nat.mul_one]
    generalize (y + 1) * (perfectPartitionOfFactorization xs).sum = t
    omega

/-- **Truncated recursion for ordered factorizations.** For natural numbers $k$ and $n$, define
$f_k(n)$ by recursion on $k$: $f_0(n) = 0$, $f_{k+1}(1) = 1$, and for $n \ne 1$, $f_{k+1}(n)$ is
the sum of $f_k(d)$ over the proper divisors $d$ of $n$, that is, the divisors $d$ of $n$ with
$1 \le d < n$ (there are none when $n = 0$).

Source: Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025),
Article A109, Section 1 (definition of `f(n)`; summing over the first factor `n / d` of an
ordered factorization gives the recursion). -/
def orderedFactorizationCountAux : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, n => if n = 1 then 1 else ∑ d ∈ n.properDivisors, orderedFactorizationCountAux k d

/-- **Number of ordered factorizations.** For $n \ge 2$, $f(n)$ is the number of ordered
factorizations $n = a_1 a_2 \cdots a_k$ of $n$ into factors $a_i > 1$ (OEIS A074206); moreover
$f(0) = 0$ and $f(1) = 1$.

Source: Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025),
Article A109, Section 1 (`f(n) := Σ_k f(n, k)`, `f(0) = 0`, `f(1) = 1`). -/
def orderedFactorizationCount (n : ℕ) : ℕ :=
  orderedFactorizationCountAux n n

/-- **The truncated ordered-factorization recursion stabilizes.** Let $f_k(n)$ be the truncated
recursion with $f_0(n) = 0$, $f_{k+1}(1) = 1$, and $f_{k+1}(n)$ the sum of $f_k(d)$ over the
proper divisors $d$ of $n$ when $n \ne 1$. For all natural numbers $n$ and $k$ with $n \le k$,
$f_k(n) = f(n)$, where $f(n)$ is the number of ordered factorizations of $n$ into factors
greater than $1$.

Source: Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025),
Article A109, Section 1 (definition of `f(n)`). -/
theorem orderedFactorizationCountAux_eq (n : ℕ) :
    ∀ k, n ≤ k → orderedFactorizationCountAux k n = orderedFactorizationCount n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro k hk
    unfold orderedFactorizationCount
    rcases n with _ | n
    · cases k <;> simp [orderedFactorizationCountAux]
    · obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      simp only [orderedFactorizationCountAux]
      split_ifs
      · rfl
      · refine Finset.sum_congr rfl fun d hd => ?_
        have hdn := Nat.mem_properDivisors.mp hd
        rw [ih d hdn.2 k (by omega), ih d hdn.2 n (by omega)]

/-- **Recursion for the number of ordered factorizations.** For every integer $n \ge 2$, the
number $f(n)$ of ordered factorizations of $n$ into factors greater than $1$ satisfies
$f(n) = \sum_{d \mid n,\ d < n} f(d)$, the sum running over the proper divisors $d$ of $n$.

The recursion comes from splitting off the first factor of an ordered factorization.

Source: Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025),
Article A109, Section 1 (definition of `f(n)`). -/
theorem orderedFactorizationCount_eq_sum {n : ℕ} (hn : 2 ≤ n) :
    orderedFactorizationCount n = ∑ d ∈ n.properDivisors, orderedFactorizationCount d := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [orderedFactorizationCount, orderedFactorizationCountAux]
  split_ifs with h
  · omega
  refine Finset.sum_congr rfl fun d hd => ?_
  have := Nat.mem_properDivisors.mp hd
  exact orderedFactorizationCountAux_eq d m (by omega)

/-- **Small values of the ordered factorization count.** The number $f(n)$ of ordered
factorizations of $n$ into factors greater than $1$ takes the values $f(0) = 0$, $f(1) = 1$,
$f(6) = 3$ and $f(12) = 8$.

Source: Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025),
Article A109, Section 1 (the eight ordered factorizations of `12`, Table 1 for `6`). -/
theorem orderedFactorizationCount_small :
    orderedFactorizationCount 0 = 0 ∧ orderedFactorizationCount 1 = 1 ∧
      orderedFactorizationCount 6 = 3 ∧ orderedFactorizationCount 12 = 8 := by
  decide

/-- **A perfect partition of seven.** The partition $(1^3, 4)$ of $7$, with three parts equal
to $1$ and one part equal to $4$, is a perfect partition of $7$.

Source: Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025),
Article A109, example after Definition 1. -/
theorem isPerfectPartition_seven : IsPerfectPartition 7 {1, 1, 1, 4} := by
  unfold IsPerfectPartition subpartitionCount
  decide

/-- **A Type-A double-perfect partition of seven.** The partition $(1^5, 2)$ of $7$, with five
parts equal to $1$ and one part equal to $2$, is a Type-A double-perfect partition of $7$ of
order $1$.

It arises from the perfect partition $(1^5)$ of $5$ by adding the part $2$.

Source: Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025),
Article A109, example after Definition 3 and Table 3. -/
theorem isTypeADoublePerfect_one_seven : IsTypeADoublePerfect 1 7 {1, 1, 1, 1, 1, 2} := by
  refine ⟨?_, {1, 1, 1, 1, 1}, ?_, Or.inr ?_⟩
  · unfold IsDoublePerfectOfOrder subpartitionCount
    decide +kernel
  · unfold IsPerfectPartition subpartitionCount
    decide
  · decide

private def subpartitions (l : Multiset ℕ) (k : ℕ) : Finset (Multiset ℕ) :=
  l.powerset.toFinset.filter fun s => s.sum = k

private theorem mem_subpartitions {l s : Multiset ℕ} {k : ℕ} :
    s ∈ subpartitions l k ↔ s ≤ l ∧ s.sum = k := by
  simp [subpartitions]

namespace exists_partition_unique_subsums_but_one_iff

-- Removing a one or inserting a one maps the two classes into neighboring sums.
private theorem card_le_neighbors {l : Multiset ℕ} (h₁ : 1 ∈ l) (m : ℕ) :
    (subpartitions l m).card ≤
      (subpartitions l (m - 1)).card + (subpartitions l (m + 1)).card := by
  rw [← Finset.card_filter_add_card_filter_not (s := subpartitions l m) (fun s => 1 ∈ s)]
  apply Nat.add_le_add
  · apply Finset.card_le_card_of_injOn (fun s => s.erase 1)
    · intro s hs
      obtain ⟨hs, hmem⟩ := Finset.mem_filter.mp hs
      obtain ⟨hs, hsum⟩ := mem_subpartitions.mp hs
      refine mem_subpartitions.mpr ⟨(Multiset.erase_le _ _).trans hs, ?_⟩
      change (s.erase 1).sum = m - 1
      rw [← Multiset.cons_erase hmem, Multiset.sum_cons] at hsum
      omega
    · intro s hs t ht h
      simpa only [Multiset.cons_erase (Finset.mem_filter.mp hs).2,
        Multiset.cons_erase (Finset.mem_filter.mp ht).2] using congrArg (Multiset.cons 1) h
  · apply Finset.card_le_card_of_injOn (Multiset.cons 1)
    · intro s hs
      obtain ⟨hs, hmem⟩ := Finset.mem_filter.mp hs
      obtain ⟨hs, hsum⟩ := mem_subpartitions.mp hs
      exact mem_subpartitions.mpr ⟨(Multiset.cons_le_of_notMem hmem).mpr ⟨h₁, hs⟩,
        by simp [hsum, Nat.add_comm]⟩
    · exact fun _ _ _ _ h => (Multiset.cons_inj_right 1).mp h

end exists_partition_unique_subsums_but_one_iff

/-- **Partitions with unique subsums except one.** The partitions of $m$ contained in a
partition $\lambda$ are the distinct sub-multisets of the parts of $\lambda$ with sum $m$. Let
$v \ge 1$. There are a natural number $n$ and a partition $\lambda$ of $n$ that contains exactly
$v$ partitions of some $m$ with $v \le m \le n - v$ and exactly one partition of every positive
integer $m' < n$ other than $m$ if and only if $v = 1$ or $v = 2$.

The hypothesis $v \ge 1$ is needed: for $v = 0$ the partition $(2)$ of $2$ qualifies with
$m = 1$, since it contains no partition of $1$.

Source: Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025),
Article A109, Lemma 1 (`integers-2025-A109-lem-1`). -/
theorem exists_partition_unique_subsums_but_one_iff (v : ℕ) (hv : 1 ≤ v) :
    (∃ n : ℕ, ∃ p : n.Partition,
      let c : ℕ → ℕ := fun m => (p.parts.powerset.toFinset.filter fun s => s.sum = m).card
      ∃ m, v ≤ m ∧ m ≤ n - v ∧ c m = v ∧ ∀ m', 0 < m' → m' < n → m' ≠ m → c m' = 1) ↔
      v = 1 ∨ v = 2 := by
  constructor
  · rintro ⟨n, p, m, hvm, hmn, hm, hother⟩
    by_contra! h
    have hv₃ : 3 ≤ v := by omega
    change (subpartitions p.parts m).card = v at hm
    change ∀ k, 0 < k → k < n → k ≠ m → (subpartitions p.parts k).card = 1 at hother
    -- A subpartition of sum one supplies a part equal to one.
    have hc := hother 1 (by decide) (by omega) (by omega)
    obtain ⟨s, hs⟩ := Finset.card_pos.mp (by omega : 0 < (subpartitions p.parts 1).card)
    obtain ⟨hs, hsum⟩ := mem_subpartitions.mp hs
    have hne : s ≠ 0 := by rintro rfl; simp at hsum
    obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hne
    have hap := Multiset.mem_of_le hs ha
    have hpos := p.parts_pos hap
    have hle := Multiset.le_sum_of_mem ha
    have ha₁ : a = 1 := by omega
    have hbound := exists_partition_unique_subsums_but_one_iff.card_le_neighbors (ha₁ ▸ hap) m
    rw [hm, hother (m - 1) (by omega) (by omega) (by omega),
      hother (m + 1) (by omega) (by omega) (by omega)] at hbound
    omega
  · rintro (rfl | rfl)
    · refine ⟨2, Nat.Partition.ofSums 2 {1, 1} (by decide), 1, by decide, by decide, by decide, ?_⟩
      intro k hk hkn hne
      omega
    · refine ⟨4, Nat.Partition.ofSums 4 {1, 1, 2} (by decide), 2, by decide, by decide,
        by decide, ?_⟩
      intro k hk hkn hne
      have : k = 1 ∨ k = 3 := by omega
      rcases this with rfl | rfl <;> decide

private theorem sum_le_of_le {s l : Multiset ℕ} (h : s ≤ l) : s.sum ≤ l.sum := by
  obtain ⟨t, rfl⟩ := Multiset.le_iff_exists_add.mp h
  simp

-- Extend the defining counts to zero and to sums beyond the total.
private theorem count_at {r n : ℕ} {l : Multiset ℕ} (h : IsDoublePerfectOfOrder r n l) (k : ℕ) :
    subpartitionCount l k =
      if k ≤ n then (if r + 1 ≤ k ∧ k + r + 1 ≤ n then 2 else 1) else 0 := by
  by_cases hkn : k ≤ n
  · rw [ite_eq_left hkn]
    obtain rfl | hk := Nat.eq_zero_or_pos k
    · rw [ite_eq_right (by omega)]
      change (subpartitions l 0).card = 1
      apply Finset.card_eq_one.mpr
      refine ⟨0, Finset.ext fun s => ?_⟩
      rw [mem_subpartitions, Finset.mem_singleton]
      constructor
      · rintro ⟨hs, hsum⟩
        by_contra hne
        obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hne
        have hpos := h.1 a (Multiset.mem_of_le hs ha)
        have hle := Multiset.single_le_sum (fun _ _ => Nat.zero_le _) a ha
        omega
      · rintro rfl
        simp
    · exact h.2.2 k (Finset.mem_Icc.mpr ⟨hk, hkn⟩)
  · rw [ite_eq_right hkn]
    change (subpartitions l k).card = 0
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro s hs
    obtain ⟨hs, hsum⟩ := mem_subpartitions.mp hs
    exact hkn (hsum ▸ h.2.1 ▸ sum_le_of_le hs)

-- A part of size n - r would leave only r for all the other parts combined.
private theorem new_part_notMem {r n : ℕ} {l : Multiset ℕ} (hn : 2 * (r + 1) ≤ n)
    (hl : IsDoublePerfectOfOrder r n l) : n - r ∉ l := by
  have hc : 0 < (subpartitions l (r + 1)).card := by
    change 0 < subpartitionCount l (r + 1)
    rw [count_at hl]
    split_ifs <;> omega
  obtain ⟨s, hs⟩ := Finset.card_pos.mp hc
  obtain ⟨hs, hsum⟩ := mem_subpartitions.mp hs
  intro hd
  obtain ⟨t, ht⟩ := Multiset.exists_cons_of_mem hd
  have hsmall : n - r ∉ s := by
    intro h
    have hle := Multiset.single_le_sum (fun _ _ => Nat.zero_le _) _ h
    omega
  rw [ht, Multiset.le_cons_of_notMem hsmall] at hs
  have hle := sum_le_of_le hs
  have htotal := hl.2.1
  rw [ht, Multiset.sum_cons] at htotal
  omega

private theorem le_add_replicate_iff {s l : Multiset ℕ} {d : ℕ} (hd : d ∉ s) (m : ℕ) :
    s ≤ l + Multiset.replicate m d ↔ s ≤ l := by
  induction m with
  | zero => simp
  | succ m ih => simpa only [Multiset.replicate_succ, Multiset.add_cons,
      Multiset.le_cons_of_notMem hd] using ih

-- Separate subpartitions using no new part from those where one copy can be removed.
private theorem count_add_replicate_succ {l : Multiset ℕ} {d : ℕ} (hd : d ∉ l) (m k : ℕ) :
    subpartitionCount (l + Multiset.replicate (m + 1) d) k =
      subpartitionCount l k +
        if d ≤ k then subpartitionCount (l + Multiset.replicate m d) (k - d) else 0 := by
  let t := l + Multiset.replicate m d
  let shifted := t.powerset.toFinset.filter fun s => d + s.sum = k
  let ins : Multiset ℕ ↪ Multiset ℕ :=
    ⟨Multiset.cons d, fun _ _ => (Multiset.cons_inj_right d).mp⟩
  have hshift {s : Multiset ℕ} : s ∈ shifted ↔ s ≤ t ∧ d + s.sum = k := by
    simp [shifted]
  have hunion : subpartitions (d ::ₘ t) k = subpartitions l k ∪ shifted.map ins := by
    ext s
    simp only [mem_subpartitions, Finset.mem_union, Finset.mem_map, hshift]
    constructor
    · rintro ⟨hs, hsum⟩
      by_cases hds : d ∈ s
      · obtain ⟨u, rfl⟩ := Multiset.exists_cons_of_mem hds
        exact Or.inr ⟨u, ⟨(Multiset.cons_le_cons_iff _).mp hs, by simpa using hsum⟩, rfl⟩
      · exact Or.inl ⟨(le_add_replicate_iff hds m).mp ((Multiset.le_cons_of_notMem hds).mp hs),
          hsum⟩
    · rintro (⟨hs, hsum⟩ | ⟨u, ⟨hu, hsum⟩, rfl⟩)
      · exact ⟨(hs.trans (Multiset.le_add_right _ _)).trans (Multiset.le_cons_self _ _), hsum⟩
      · exact ⟨Multiset.cons_le_cons d hu, (Multiset.sum_cons _ _).trans hsum⟩
  have hdisj : Disjoint (subpartitions l k) (shifted.map ins) := by
    apply Finset.disjoint_left.mpr
    intro s hs h
    obtain ⟨u, _, rfl⟩ := Finset.mem_map.mp h
    exact hd (Multiset.mem_of_le (mem_subpartitions.mp hs).1 (Multiset.mem_cons_self d u))
  rw [Multiset.replicate_succ, Multiset.add_cons]
  change (subpartitions (d ::ₘ t) k).card = _
  rw [hunion, Finset.card_union_of_disjoint hdisj, Finset.card_map]
  congr 1
  by_cases hdk : d ≤ k
  · rw [ite_eq_left hdk]
    change shifted.card = (subpartitions t (k - d)).card
    congr 1
    ext s
    rw [hshift, mem_subpartitions]
    exact and_congr_right fun _ => by omega
  · rw [ite_eq_right hdk, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro s hs
    have := (hshift.mp hs).2
    omega

/-- **Inserting copies of a part into a double-perfect partition.** Let $r \ge 1$,
$n \ge 2(r+1)$, and let $\lambda$ be a double-perfect partition of $n$ of order $r$. For every
$m \ge 0$, adding $m$ parts equal to $n - r$ to $\lambda$ gives a double-perfect partition of
$n + m(n - r)$ of order $r$.

The hypothesis $n \ge 2(r+1)$ is needed: for $r = 1$, $(1^2)$ is a double-perfect partition of $2$
of order $1$, but adding $m = 2$ parts equal to $1$ gives $(1^4)$, which is not double-perfect of
order $1$.

Source: Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025),
Article A109, Theorem 4 (`integers-2025-A109-thm-4`). -/
theorem isDoublePerfectOfOrder_add_replicate (r n : ℕ) (hr : 1 ≤ r)
    (hn : 2 * (r + 1) ≤ n) (l : Multiset ℕ) (hl : IsDoublePerfectOfOrder r n l) (m : ℕ) :
    IsDoublePerfectOfOrder r (n + m * (n - r)) (l + Multiset.replicate m (n - r)) := by
  set d := n - r with hd_eq
  have hd : 0 < d := by omega
  have hnew : d ∉ l := new_part_notMem hn hl
  induction m with
  | zero => simpa using hl
  | succ m ih =>
    refine ⟨?_, ?_, ?_⟩
    · intro a ha
      rcases Multiset.mem_add.mp ha with ha | ha
      · exact hl.1 a ha
      · exact Multiset.eq_of_mem_replicate ha ▸ hd
    · rw [Multiset.sum_add, hl.2.1, Multiset.sum_replicate, Nat.nsmul_eq_mul]
    · intro k hk
      obtain ⟨hk₁, hk₂⟩ := Finset.mem_Icc.mp hk
      rw [count_add_replicate_succ hnew, count_at hl, count_at ih]
      rw [Nat.succ_mul] at hk₂ ⊢
      -- Both counts contribute on [d, n], where k and k - d each have one representation.
      have htotal : d + r = n := by omega
      split_ifs <;> omega

namespace typeADoublePerfect_forms

-- A prefix of total b - 1 represents every residue modulo b. Copies of b
-- extend this interval by successive blocks of length b.
private theorem cover_blocks {p : Multiset ℕ} {b : ℕ} (hb : 0 < b)
    (cover : ∀ k < b, ∃ s ≤ p, s.sum = k) (c : ℕ) :
    ∀ k < b * (c + 1), ∃ s ≤ p + Multiset.replicate c b, s.sum = k := by
  intro k hk
  obtain ⟨s, hs, hsum⟩ := cover (k % b) (Nat.mod_lt k hb)
  have hdiv : k / b ≤ c := by
    have := (Nat.div_lt_iff_lt_mul hb).2 (Nat.mul_comm b (c + 1) ▸ hk)
    omega
  refine ⟨s + Multiset.replicate (k / b) b, add_le_add hs (Multiset.replicate_mono b hdiv), ?_⟩
  simpa [hsum, Nat.mul_comm] using Nat.mod_add_div k b

-- A subpartition that does not fit in the prefix uses a part from the tail.
private theorem meets_tail {s p t : Multiset ℕ} (hs : s ≤ p + t) (hp : ¬ s ≤ p) :
    ∃ x ∈ s, x ∈ t := by
  by_contra! avoid
  apply hp
  apply Multiset.le_iff_count.mpr
  intro x
  by_cases hx : x ∈ s
  · simpa [Multiset.count_eq_zero_of_notMem (avoid x hx)] using Multiset.le_iff_count.mp hs x
  · simp [Multiset.count_eq_zero_of_notMem hx]

-- Unique sums force the next part of a perfect partition to be the first
-- integer beyond the covered interval. Its multiplicity determines the next radix.
private theorem factor_tail {n : ℕ} {β : Multiset ℕ} (hβ : IsPerfectPartition n β)
    (p t : Multiset ℕ) (b : ℕ) (hsplit : p + t = β) (hb : p.sum + 1 = b)
    (cover : ∀ k < b, ∃ s ≤ p, s.sum = k) (sep : ∀ x ∈ t, x ∉ p) :
    ∃ as : List ℕ, (∀ a ∈ as, 2 ≤ a) ∧
      t = (perfectPartitionOfFactorization as).map (b * ·) := by
  by_cases ht : t = 0
  · exact ⟨[], by simp, by simp [ht, perfectPartitionOfFactorization]⟩
  have hpβ : p ≤ β := hsplit ▸ Multiset.le_add_right _ _
  have htβ : t ≤ β := hsplit ▸ Multiset.le_add_left _ _
  have lower (x : ℕ) (hx : x ∈ t) : b ≤ x := by
    by_contra! h
    obtain ⟨s, hs, hsum⟩ := cover x h
    have hxβ := Multiset.mem_of_le htβ hx
    have hxn := Multiset.le_sum_of_mem hxβ
    have hc : (subpartitions β x).card = 1 :=
      hβ.2.2 x (Finset.mem_Icc.mpr ⟨hβ.1 x hxβ, hβ.2.1 ▸ hxn⟩)
    have he := Finset.card_le_one.mp hc.le s (mem_subpartitions.mpr ⟨hs.trans hpβ, hsum⟩)
      {x} (mem_subpartitions.mpr ⟨Multiset.singleton_le.mpr hxβ, by simp⟩)
    exact sep x hx (Multiset.singleton_le.mp (he ▸ hs))
  obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero ht
  have hxn := Multiset.le_sum_of_mem (Multiset.mem_of_le htβ hx)
  have hbn : b ≤ n := (lower x hx).trans (hβ.2.1 ▸ hxn)
  have hc : (subpartitions β b).card = 1 := hβ.2.2 b (Finset.mem_Icc.mpr ⟨by omega, hbn⟩)
  obtain ⟨s, hs⟩ := Finset.card_pos.mp (by omega : 0 < (subpartitions β b).card)
  obtain ⟨hs, hsum⟩ := mem_subpartitions.mp hs
  obtain ⟨y, hys, hyt⟩ := meets_tail (hsplit ▸ hs) (fun hp => by
    have := sum_le_of_le hp
    omega)
  have hy : y = b := le_antisymm (hsum ▸ Multiset.le_sum_of_mem hys) (lower y hyt)
  have hbt : b ∈ t := hy ▸ hyt
  let c := t.count b
  let rest := t.filter (· ≠ b)
  have ht' : Multiset.replicate c b + rest = t := by
    simpa only [Multiset.filter_eq'] using t.filter_add_not (· = b)
  have hcpos : 0 < c := Multiset.count_pos.mpr hbt
  have hcard := congrArg Multiset.card ht'
  simp only [Multiset.card_add, Multiset.card_replicate] at hcard
  have hlt : rest.card < t.card := by omega
  have hrec := factor_tail hβ (p + Multiset.replicate c b) rest (b * (c + 1))
    (by rwa [add_assoc, ht']) (by simp [Nat.mul_add, Nat.mul_comm, ← hb]; omega)
    (cover_blocks (by omega) cover c) (by
      intro y hy hymem
      obtain ⟨hyt, hne⟩ := Multiset.mem_filter.mp hy
      rcases Multiset.mem_add.mp hymem with hyp | hyr
      · exact sep y hyt hyp
      · exact hne (Multiset.eq_of_mem_replicate hyr))
  obtain ⟨as, has, he⟩ := hrec
  refine ⟨(c + 1) :: as, List.forall_mem_cons.mpr ⟨by omega, has⟩, ?_⟩
  rw [← ht', he]
  simp [perfectPartitionOfFactorization, Multiset.map_map, Nat.mul_assoc]
termination_by t.card
decreasing_by exact hlt

private theorem first_interior_card {r N : ℕ} {l : Multiset ℕ} (hN : 2 * (r + 1) ≤ N)
    (hl : IsDoublePerfectOfOrder r N l) : (subpartitions l (r + 1)).card = 2 := by
  change subpartitionCount l (r + 1) = 2
  rw [count_at hl]
  split_ifs <;> omega

-- The first sum with two representations is r + 1. With extra ones this
-- must be the least part larger than one.
private theorem head_of_extra_ones {r N a : ℕ} {t l : Multiset ℕ} (ha : 2 ≤ a)
    (hN : 2 * (r + 1) ≤ N) (hl : IsDoublePerfectOfOrder r N l)
    (lower : ∀ x ∈ t, a ≤ x) (first : t ≠ 0 → a ∈ t)
    (he : l = Multiset.replicate (a - 1 + (r + 1)) 1 + t) : a = r + 1 := by
  have hc := first_interior_card hN hl
  obtain ⟨s, hmem, hne⟩ := Finset.exists_mem_ne (by omega :
    1 < (subpartitions l (r + 1)).card) (Multiset.replicate (r + 1) 1)
  obtain ⟨hs, hsum⟩ := mem_subpartitions.mp hmem
  obtain ⟨x, hxs, hxt⟩ := meets_tail (he ▸ hs) (by
    intro hp
    obtain ⟨k, _, rfl⟩ := Multiset.le_replicate_iff.mp hp
    have hk : k = r + 1 := by simpa using hsum
    exact hne (hk ▸ rfl))
  have hx := Multiset.le_sum_of_mem hxs
  have hax := lower x hxt
  by_contra hne'
  have ha₁ : a ≤ r := by omega
  have hc₁ : (subpartitions l a).card = 1 := by
    change subpartitionCount l a = 1
    rw [count_at hl]
    split_ifs <;> omega
  have ha_mem : a ∈ t := first (by rintro rfl; simp at hxt)
  have hsingle : {a} ∈ subpartitions l a := mem_subpartitions.mpr
    ⟨Multiset.singleton_le.mpr (he ▸ Multiset.mem_add.mpr (Or.inr ha_mem)), by simp⟩
  have hones : Multiset.replicate a 1 ∈ subpartitions l a := by
    refine mem_subpartitions.mpr ⟨?_, by simp⟩
    rw [he]
    exact (Multiset.replicate_mono 1 (by omega)).trans (Multiset.le_add_right _ _)
  have heq := Finset.card_le_one.mp hc₁.le _ hones _ hsingle
  have := congrArg Multiset.card heq
  simp at this
  omega

-- If there are only r ones and all other parts are at least r + 1, the
-- singleton is the only possible representation of r + 1.
private theorem head_of_extra_part {r N a : ℕ} {t l : Multiset ℕ}
    (hN : 2 * (r + 1) ≤ N) (hl : IsDoublePerfectOfOrder r N l)
    (lower : ∀ x ∈ t, a ≤ x)
    (he : l = Multiset.replicate (a - 1) 1 + t + {r + 1}) : a ≠ r + 1 := by
  intro heq
  have hc : (subpartitions l a).card = 2 := heq ▸ first_interior_card hN hl
  obtain ⟨s, hmem, hne⟩ := Finset.exists_mem_ne (by omega : 1 < (subpartitions l a).card)
    ({a} : Multiset ℕ)
  obtain ⟨hs, hsum⟩ := mem_subpartitions.mp hmem
  rw [add_assoc] at he
  obtain ⟨x, hxs, hxt⟩ := meets_tail (he ▸ hs) (by
    intro hp
    have := sum_le_of_le hp
    simp at this
    omega)
  have hx : a ≤ x := by
    rcases Multiset.mem_add.mp hxt with hx | hx
    · exact lower x hx
    · exact (heq.trans (Multiset.mem_singleton.mp hx).symm).le
  have := Multiset.le_sum_of_mem hxs
  obtain rfl : x = a := by omega
  obtain ⟨u, rfl⟩ := Multiset.exists_cons_of_mem hxs
  rw [Multiset.sum_cons] at hsum
  by_cases hu : u = 0
  · simp [hu] at hne
  obtain ⟨y, hy⟩ := Multiset.exists_mem_of_ne_zero hu
  have := hl.1 y (Multiset.mem_of_le hs (Multiset.mem_cons_of_mem hy))
  have := Multiset.le_sum_of_mem hy
  omega

end typeADoublePerfect_forms

/-- **Shapes of Type-A double-perfect partitions.** Let $r \ge 1$ and $N \ge 2(r+1)$. For a
finite sequence $(a_1, \dots, a_k)$ write
$P(a_1, \dots, a_k) = (1^{a_1-1}, a_1^{a_2-1}, \dots, (a_1\cdots a_{k-1})^{a_k-1})$ for the
partition that MacMahon's bijection attaches to the ordered factorization $a_1 \cdots a_k$,
where $x^e$ denotes $e$ parts equal to $x$, and let $\cup$ join parts with multiplicity. Every
Type-A double-perfect partition $\lambda$ of $N$ of order $r$ has one of two shapes. Either
there are $k \ge 1$ and integers $a_2, \dots, a_k \ge 2$ with $(r+1) a_2 \cdots a_k = N - r$ and
$\lambda = (1^{r+1}) \cup P(r+1, a_2, \dots, a_k) =
(1^{2r+1}, (r+1)^{a_2-1}, ((r+1)a_2)^{a_3-1}, \dots)$; or there are $k \ge 0$ and integers
$a_1, \dots, a_k \ge 2$ with $a_1 \cdots a_k = N - r$, with $a_1 \ne r + 1$ if $k \ge 1$, and
$\lambda = P(a_1, \dots, a_k) \cup (r+1)$.

Source: Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025),
Article A109, Corollary 2 with displays (14)-(17) (`integers-2025-A109-cor-2`). -/
theorem typeADoublePerfect_forms (r N : ℕ) (hr : 1 ≤ r) (hN : 2 * (r + 1) ≤ N)
    (l : Multiset ℕ) (hl : IsTypeADoublePerfect r N l) :
    (∃ as : List ℕ, (∀ a ∈ as, 2 ≤ a) ∧ (r + 1) * as.prod = N - r ∧
      l = Multiset.replicate (r + 1) 1 + perfectPartitionOfFactorization ((r + 1) :: as)) ∨
    (∃ as : List ℕ, (∀ a ∈ as, 2 ≤ a) ∧ as.prod = N - r ∧ as.head? ≠ some (r + 1) ∧
      l = perfectPartitionOfFactorization as + {r + 1}) := by
  obtain ⟨hd, β, hβ, hshape⟩ := hl
  obtain ⟨as, has, hfac⟩ := typeADoublePerfect_forms.factor_tail hβ 0 β 1 (by simp) (by simp)
    (by intro k hk; exact ⟨0, le_rfl, by simp; omega⟩) (by simp)
  simp only [Nat.one_mul, Multiset.map_id'] at hfac
  have hprod := perfectPartitionOfFactorization_sum_add_one as fun x hx =>
    (has x hx).trans' (by decide)
  rw [← hfac, hβ.2.1] at hprod
  have htotal : as.prod = N - r := by omega
  cases as with
  | nil => simp at htotal; omega
  | cons a as =>
    obtain ⟨ha, has⟩ := List.forall_mem_cons.mp has
    let t := (perfectPartitionOfFactorization as).map (a * ·)
    have hparts : β = Multiset.replicate (a - 1) 1 + t := hfac
    have lower (x : ℕ) (hx : x ∈ t) : a ≤ x := by
      obtain ⟨y, _, hxy⟩ := Multiset.mem_map.mp hx
      exact Nat.le_of_dvd (hβ.1 x (hparts ▸ Multiset.mem_add.mpr (Or.inr hx))) ⟨y, hxy.symm⟩
    rcases hshape with he | he
    · have first : t ≠ 0 → a ∈ t := by
        cases as with
        | nil => simp [t, perfectPartitionOfFactorization]
        | cons b bs =>
          intro _
          have hb := has b (by simp)
          apply Multiset.mem_map.mpr
          refine ⟨1, Multiset.mem_add.mpr (.inl (Multiset.mem_replicate.mpr ⟨?_, rfl⟩)), by simp⟩
          omega
      have he' : l = Multiset.replicate (a - 1 + (r + 1)) 1 + t := by
        rw [he, hparts, Multiset.replicate_add (a - 1) (r + 1)]
        ac_rfl
      have heq := typeADoublePerfect_forms.head_of_extra_ones ha hN hd lower first he'
      exact Or.inl ⟨as, has, by simpa only [List.prod_cons, heq] using htotal,
        by rw [he, hfac, heq, add_comm]⟩
    · have hne := typeADoublePerfect_forms.head_of_extra_part hN hd lower
        (he.trans (by rw [hparts]))
      exact Or.inr ⟨a :: as, List.forall_mem_cons.mpr ⟨ha, has⟩, htotal, by simpa using hne,
        by rw [he, hfac]⟩

end

end MetaMathlibExt
