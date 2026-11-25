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


namespace isTypeADoublePerfect_iff

private theorem perfect_count {n : ℕ} {β : Multiset ℕ} (hβ : IsPerfectPartition n β)
    (m : ℕ) : subpartitionCount β m = if m ≤ n then 1 else 0 := by
  -- Reuse the endpoint count with an empty interval of doubled counts.
  have h : IsDoublePerfectOfOrder n n β := ⟨hβ.1, hβ.2.1, fun k hk => by
    have hkN := (Finset.mem_Icc.mp hk).2
    rw [ite_eq_right (by omega)]
    exact hβ.2.2 k hk⟩
  rw [count_at h]
  split_ifs <;> omega

private theorem le_of_count_le {s β : Multiset ℕ} {d q : ℕ}
    (hs : s ≤ β + Multiset.replicate q d) (hc : s.count d ≤ β.count d) : s ≤ β := by
  refine Multiset.le_iff_count.mpr fun a => ?_
  by_cases ha : d = a
  · simpa only [← ha] using hc
  · simpa only [Multiset.count_add, Multiset.count_replicate, ite_eq_right ha, Nat.add_zero] using
      Multiset.le_iff_count.mp hs a

private theorem subpartitions_mono {s t : Multiset ℕ} (hst : s ≤ t) (m : ℕ) :
    subpartitions s m ⊆ subpartitions t m := by
  intro u hu
  obtain ⟨hu, hsum⟩ := mem_subpartitions.mp hu
  exact mem_subpartitions.mpr ⟨hu.trans hst, hsum⟩

-- The low multiplicities are the old subpartitions. Removing the full new block
-- from a high multiplicity leaves another old subpartition.
private theorem count_add_block (β : Multiset ℕ) (d m : ℕ) :
    let b := Multiset.replicate (β.count d + 1) d
    subpartitionCount (β + b) m =
      subpartitionCount β m + if b.sum ≤ m then subpartitionCount β (m - b.sum) else 0 := by
  intro b
  let shift : Multiset ℕ ↪ Multiset ℕ :=
    ⟨fun s => s + b, fun _ _ h => add_right_cancel h⟩
  let shifted := β.powerset.toFinset.filter fun s => s.sum + b.sum = m
  have hshift {s : Multiset ℕ} : s ∈ shifted ↔ s ≤ β ∧ s.sum + b.sum = m := by
    simp [shifted]
  have hunion : subpartitions (β + b) m = subpartitions β m ∪ shifted.map shift := by
    ext s
    simp only [mem_subpartitions, Finset.mem_union, Finset.mem_map, hshift]
    constructor
    · rintro ⟨hs, hsum⟩
      by_cases h : β.count d + 1 ≤ s.count d
      · obtain ⟨u, hu⟩ := Multiset.le_iff_exists_add.mp
          (Multiset.le_count_iff_replicate_le.mp h)
        rw [add_comm b u] at hu
        subst s
        exact Or.inr ⟨u, ⟨le_of_add_le_add_right hs, by simpa using hsum⟩, rfl⟩
      · exact Or.inl ⟨le_of_count_le hs (by omega), hsum⟩
    · rintro (⟨hs, hsum⟩ | ⟨u, ⟨hu, hsum⟩, rfl⟩)
      · exact ⟨hs.trans (Multiset.le_add_right _ _), hsum⟩
      · change u + b ≤ β + b ∧ (u + b).sum = m
        exact ⟨add_le_add_left hu b, (Multiset.sum_add _ _).trans hsum⟩
  have hdisj : Disjoint (subpartitions β m) (shifted.map shift) := by
    refine Finset.disjoint_left.mpr fun s hs ht => ?_
    obtain ⟨u, _, rfl⟩ := Finset.mem_map.mp ht
    have h := Multiset.le_iff_count.mp (mem_subpartitions.mp hs).1 d
    change (u + b).count d ≤ β.count d at h
    simp only [b, Multiset.count_add, Multiset.count_replicate_self] at h
    omega
  change (subpartitions (β + b) m).card = _
  rw [hunion, Finset.card_union_of_disjoint hdisj, Finset.card_map]
  congr 1
  by_cases hm : b.sum ≤ m
  · rw [ite_eq_left hm]
    change shifted.card = (subpartitions β (m - b.sum)).card
    congr 1
    ext s
    rw [hshift, mem_subpartitions]
    exact and_congr_right fun _ => by omega
  · rw [ite_eq_right hm, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro s hs
    have := (hshift.mp hs).2
    omega

private theorem double_perfect_add_block {r N d : ℕ} {β : Multiset ℕ}
    (hN : 2 * (r + 1) ≤ N) (hβ : IsPerfectPartition (N - r - 1) β) (hd : 0 < d)
    (hsize : (Multiset.replicate (β.count d + 1) d).sum = r + 1) :
    IsDoublePerfectOfOrder r N (β + Multiset.replicate (β.count d + 1) d) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    rcases Multiset.mem_add.mp ha with ha | ha
    · exact hβ.1 a ha
    · exact Multiset.eq_of_mem_replicate ha ▸ hd
  · rw [Multiset.sum_add, hβ.2.1, hsize]
    omega
  · intro m hm
    have hmN := (Finset.mem_Icc.mp hm).2
    rw [count_add_block, hsize, perfect_count hβ, perfect_count hβ]
    split_ifs <;> omega

private theorem replicate_ones_sum (q : ℕ) : (Multiset.replicate q (1 : ℕ)).sum = q := by
  simp [Multiset.sum_replicate]

private theorem count_mul_le_sum (s : Multiset ℕ) (d : ℕ) : s.count d * d ≤ s.sum := by
  simpa only [Multiset.sum_replicate, Nat.nsmul_eq_mul] using
    sum_le_of_le (Multiset.le_count_iff_replicate_le.mp (le_refl (s.count d)))

private theorem subpartitions_ne_at_first_doubled_sum {r N : ℕ} {β l : Multiset ℕ}
    (hN : 2 * (r + 1) ≤ N) (hβ : IsPerfectPartition (N - r - 1) β)
    (hl : IsDoublePerfectOfOrder r N l) : subpartitions l (r + 1) ≠ subpartitions β (r + 1) := by
  intro heq
  have hc : subpartitionCount l (r + 1) = subpartitionCount β (r + 1) :=
    congrArg Finset.card heq
  rw [count_at hl, perfect_count hβ, ite_eq_left (by omega), ite_eq_left (by omega),
    ite_eq_left (by omega)] at hc
  contradiction

private theorem count_ones_of_add_ones {r N : ℕ} {β : Multiset ℕ}
    (hN : 2 * (r + 1) ≤ N) (hβ : IsPerfectPartition (N - r - 1) β)
    (hl : IsDoublePerfectOfOrder r N (β + Multiset.replicate (r + 1) 1)) :
    β.count 1 = r := by
  have hle : β ≤ β + Multiset.replicate (r + 1) 1 := Multiset.le_add_right _ _
  by_contra hne
  rcases lt_or_gt_of_ne hne with hsmall | hlarge
  · -- A new all-ones subpartition would duplicate a sum below the doubled interval.
    let k := β.count 1 + 1
    have hcounts : (subpartitions β k).card = 1 := by
      change subpartitionCount β k = 1
      rw [perfect_count hβ, ite_eq_left (by dsimp [k]; omega)]
    have hcountl : (subpartitions (β + Multiset.replicate (r + 1) 1) k).card = 1 := by
      change subpartitionCount (β + Multiset.replicate (r + 1) 1) k = 1
      rw [count_at hl, ite_eq_left (by dsimp [k]; omega), ite_eq_right (by dsimp [k]; omega)]
    have hstrict : subpartitions β k ⊂ subpartitions (β + Multiset.replicate (r + 1) 1) k := by
      refine (Finset.ssubset_iff_of_subset (subpartitions_mono hle k)).mpr
        ⟨Multiset.replicate k 1, ?_, ?_⟩
      · exact mem_subpartitions.mpr
          ⟨(Multiset.replicate_le_replicate 1 |>.mpr (by dsimp [k]; omega)).trans
            (Multiset.le_add_left _ _), replicate_ones_sum k⟩
      · intro hs
        have := Multiset.le_count_iff_replicate_le.mpr (mem_subpartitions.mp hs).1
        dsimp [k] at this
        omega
    have := Finset.card_lt_card hstrict
    omega
  · -- Every subpartition at the first doubled sum already fits in the old partition.
    apply subpartitions_ne_at_first_doubled_sum hN hβ hl
    refine Finset.Subset.antisymm ?_ (subpartitions_mono hle _)
    intro s hs
    obtain ⟨hs, hsum⟩ := mem_subpartitions.mp hs
    have hc : s.count 1 ≤ s.sum := by simpa using count_mul_le_sum s 1
    exact mem_subpartitions.mpr ⟨le_of_count_le hs (by omega), hsum⟩

private theorem not_mem_of_add_singleton {r N : ℕ} {β : Multiset ℕ}
    (hd : 0 < r + 1) (hN : 2 * (r + 1) ≤ N) (hβ : IsPerfectPartition (N - r - 1) β)
    (hl : IsDoublePerfectOfOrder r N (β + {r + 1})) : r + 1 ∉ β := by
  intro hmem
  apply subpartitions_ne_at_first_doubled_sum hN hβ hl
  refine Finset.Subset.antisymm ?_ (subpartitions_mono (Multiset.le_add_right _ _) _)
  intro s hs
  obtain ⟨hs, hsum⟩ := mem_subpartitions.mp hs
  have hc : s.count (r + 1) ≤ 1 := by
    apply Nat.le_of_mul_le_mul_right _ hd
    simpa only [Nat.one_mul, hsum] using count_mul_le_sum s (r + 1)
  rw [← Multiset.replicate_one] at hs
  exact mem_subpartitions.mpr
    ⟨le_of_count_le hs (hc.trans (Multiset.count_pos.mpr hmem)), hsum⟩

-- If there are exactly r ones, the first sum they cannot represent needs a part r + 1.
private theorem mem_succ_of_count_ones {r n : ℕ} {β : Multiset ℕ} (hn : r + 1 ≤ n)
    (hβ : IsPerfectPartition n β) (hc : β.count 1 = r) : r + 1 ∈ β := by
  have hsmall {a : ℕ} (ha : a ∈ β) (har : a ≤ r) : a = 1 := by
    have hcount : (subpartitions β a).card ≤ 1 := by
      change subpartitionCount β a ≤ 1
      rw [perfect_count hβ, ite_eq_left (by omega)]
    have h₁ : ({a} : Multiset ℕ) ∈ subpartitions β a :=
      mem_subpartitions.mpr ⟨Multiset.singleton_le.mpr ha, Multiset.sum_singleton a⟩
    have h₂ : Multiset.replicate a 1 ∈ subpartitions β a :=
      mem_subpartitions.mpr
        ⟨Multiset.le_count_iff_replicate_le.mp (by omega), replicate_ones_sum a⟩
    have heq := Finset.card_le_one.mp hcount _ h₁ _ h₂
    have hmem : a ∈ Multiset.replicate a 1 := heq ▸ Multiset.mem_singleton_self a
    exact Multiset.eq_of_mem_replicate hmem
  have hcount : 0 < (subpartitions β (r + 1)).card := by
    change 0 < subpartitionCount β (r + 1)
    rw [perfect_count hβ, ite_eq_left hn]
    exact Nat.zero_lt_one
  obtain ⟨s, hs⟩ := Finset.card_pos.mp hcount
  obtain ⟨hs, hsum⟩ := mem_subpartitions.mp hs
  have hnotall : ¬ ∀ a ∈ s, a = 1 := by
    intro hall
    have hrep := Multiset.eq_replicate_of_mem hall
    rw [hrep, replicate_ones_sum] at hsum
    have hle := Multiset.le_iff_count.mp hs 1
    rw [hrep, Multiset.count_replicate_self, hsum, hc] at hle
    omega
  push Not at hnotall
  obtain ⟨a, ha, hne⟩ := hnotall
  have hab := Multiset.mem_of_le hs ha
  have hlt : r < a := lt_of_not_ge (fun har => hne (hsmall hab har))
  have hle := Multiset.le_sum_of_mem ha
  exact (show a = r + 1 by omega) ▸ hab

end isTypeADoublePerfect_iff

/-- **Characterization of Type-A double-perfect partitions.** Let $r \ge 1$ and $N \ge 2(r+1)$
be integers. A multiset $\lambda$ of natural numbers is a Type-A double-perfect partition of $N$
of order $r$ if and only if there is a perfect partition $\beta$ of $N - r - 1$ such that either
$1$ occurs exactly $r$ times in $\beta$ and $\lambda$ is $\beta$ with $r + 1$ parts equal to $1$
added, or $1$ does not occur exactly $r$ times in $\beta$, $r + 1$ is not a part of $\beta$, and
$\lambda$ is $\beta$ with one part equal to $r + 1$ added.

The condition that $r + 1$ is not a part of $\beta$ in the second case is needed, and the printed
statement of Theorem 2 omits it: for $r = 3$ and $N = 11$, $\beta = (1, 2, 4)$ is a perfect
partition of $7$ with one part $1$, but $(1, 2, 4^2)$ is not double-perfect of order $3$, since
it contains only one partition of $4$. The paper uses this condition in the proof of Theorem 3,
part (ia), and it matches the set $W(2)$ of Proposition 2.

Source: Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025),
Article A109, Theorem 2, display (13) (`integers-2025-A109-thm-2`). -/
theorem isTypeADoublePerfect_iff (r N : ℕ) (hr : 1 ≤ r) (hN : 2 * (r + 1) ≤ N)
    (l : Multiset ℕ) :
    IsTypeADoublePerfect r N l ↔ ∃ β, IsPerfectPartition (N - r - 1) β ∧
      ((β.count 1 = r ∧ l = β + Multiset.replicate (r + 1) 1) ∨
        (β.count 1 ≠ r ∧ r + 1 ∉ β ∧ l = β + {r + 1})) := by
  constructor
  · rintro ⟨hl, β, hβ, rfl | rfl⟩
    · exact ⟨β, hβ, Or.inl ⟨isTypeADoublePerfect_iff.count_ones_of_add_ones hN hβ hl, rfl⟩⟩
    · have hpos := Nat.zero_lt_of_lt (Nat.lt_succ_of_le hr)
      have hnot := isTypeADoublePerfect_iff.not_mem_of_add_singleton hpos hN hβ hl
      have hne : β.count 1 ≠ r := fun hc =>
        hnot (isTypeADoublePerfect_iff.mem_succ_of_count_ones (by omega) hβ hc)
      exact ⟨β, hβ, Or.inr ⟨hne, hnot, rfl⟩⟩
  · rintro ⟨β, hβ, ⟨hc, rfl⟩ | ⟨_, hnot, rfl⟩⟩
    · refine ⟨?_, β, hβ, Or.inl rfl⟩
      have h := isTypeADoublePerfect_iff.double_perfect_add_block hN hβ
        (d := 1) Nat.zero_lt_one (by rw [isTypeADoublePerfect_iff.replicate_ones_sum, hc])
      simpa only [hc] using h
    · refine ⟨?_, β, hβ, Or.inr rfl⟩
      have hc := Multiset.count_eq_zero_of_notMem hnot
      have h := isTypeADoublePerfect_iff.double_perfect_add_block hN hβ
        (d := r + 1) (by omega) (by simp [hc])
      simpa only [hc, Nat.zero_add, Multiset.replicate_one] using h

end

end MetaMathlibExt
