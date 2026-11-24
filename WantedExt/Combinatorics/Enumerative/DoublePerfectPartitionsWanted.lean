/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.NumberTheory.Divisors

namespace MetaMathlibExt

@[expose] public section

/-- **Partitions with unique subsums except one.** The partitions of $m$ contained in a
partition $\lambda$ are the distinct sub-multisets of the parts of $\lambda$ with sum $m$. Let
$v \ge 1$. There are a natural number $n$ and a partition $\lambda$ of $n$ that contains exactly
$v$ partitions of some $m$ with $v \le m \le n - v$ and exactly one partition of every positive
integer $m' < n$ other than $m$ if and only if $v = 1$ or $v = 2$.

The hypothesis $v \ge 1$ is needed: for $v = 0$ the partition $(2)$ of $2$ qualifies with
$m = 1$, since it contains no partition of $1$.

Source: Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025),
Article A109, Lemma 1 (`integers-2025-A109-lem-1`). -/
public theorem_wanted exists_partition_unique_subsums_but_one_iff (v : ℕ) (hv : 1 ≤ v) :
    (∃ n : ℕ, ∃ p : n.Partition,
      let c : ℕ → ℕ := fun m => (p.parts.powerset.toFinset.filter fun s => s.sum = m).card
      ∃ m, v ≤ m ∧ m ≤ n - v ∧ c m = v ∧ ∀ m', 0 < m' → m' < n → m' ≠ m → c m' = 1) ↔
      v = 1 ∨ v = 2

/-! ### Perfect and double-perfect partitions of order `r` -/

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
      smul_eq_mul, mul_one, List.prod_cons, Nat.add_sub_cancel]
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

/-- **Lee's form of double-perfect partitions.** Let $N \ge 4$ and let $\lambda$ be a
double-perfect partition of $N$ of order $1$. Then there are integers $q_1 \ge 2$ and
$q_2 \ge 1$, with $q_2 = 1$ unless $q_1 = 3$, an integer $k \ge 2$ and integers
$q_3, \dots, q_k \ge 1$ such that, with $B = q_1 + 2q_2 - 1$,
$\lambda = (1^{q_1}, 2^{q_2}, B^{q_3}, (B(q_3+1))^{q_4}, \dots,
(B(q_3+1) \cdots (q_{k-1}+1))^{q_k})$ (for $k = 2$ the only parts are $1$ and $2$). That is, the
parts other than $1^{q_1}$ and $2^{q_2}$ are $B$ times the parts of the perfect partition
$(1^{q_3}, (q_3+1)^{q_4}, \dots, ((q_3+1) \cdots (q_{k-1}+1))^{q_k})$ attached to the ordered
factorization $(q_3+1)(q_4+1) \cdots (q_k+1)$.

The hypothesis $N \ge 4$ is needed: $(1^3)$ is a double-perfect partition of $3$ of order $1$
but has no part $2$.

Source: Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025),
Article A109, Proposition 1 (Lee), display (3) (`integers-2025-A109-prop-1`). -/
public theorem_wanted doublePerfect_form (N : ℕ) (hN : 4 ≤ N) (l : Multiset ℕ)
    (hl : IsDoublePerfectOfOrder 1 N l) :
    ∃ q₁ q₂ : ℕ, ∃ qs : List ℕ, 2 ≤ q₁ ∧ 1 ≤ q₂ ∧ (∀ q ∈ qs, 1 ≤ q) ∧ (q₁ ≠ 3 → q₂ = 1) ∧
      l = Multiset.replicate q₁ 1 + Multiset.replicate q₂ 2 +
        (perfectPartitionOfFactorization (qs.map (· + 1))).map ((q₁ + 2 * q₂ - 1) * ·)

/-- **Lee's count of double-perfect partitions.** Let $f(m)$ be the number of ordered
factorizations of $m$ into factors greater than $1$, with $f(0) = 0$ and $f(1) = 1$. For every
$n \ge 4$, the number $d(n)$ of double-perfect partitions of $n$ of order $1$ is $f(n-1)$ unless
$n \equiv 1 \pmod 4$, in which case $d(n) = f(n-1) - f((n-1)/4)$.

The hypothesis $n \ge 4$ is needed: for $n = 3$ both perfect partitions $(1^3)$ and $(1, 2)$ are
double-perfect of order $1$ while $f(2) = 1$, and for $n = 1$ the partition $(1)$ is
double-perfect of order $1$ while $f(0) = 0$.

Source: Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025),
Article A109, Theorem 1 (Lee), display (4) (`integers-2025-A109-thm-1`). -/
public theorem_wanted doublePerfect_ncard (n : ℕ) (hn : 4 ≤ n) :
    ({l | IsDoublePerfectOfOrder 1 n l}.ncard : ℤ) =
      if n % 4 = 1 then
        (orderedFactorizationCount (n - 1) : ℤ) - orderedFactorizationCount ((n - 1) / 4)
      else orderedFactorizationCount (n - 1)

/-- **Double-perfect partitions from perfect partitions.** Let $N > 3$. A multiset $\lambda$ of
natural numbers is a double-perfect partition of $N$ of order $1$ if and only if there is a
perfect partition $\beta$ of $N - 2$ such that either $1$ occurs exactly once in $\beta$ and
$\lambda$ is $\beta$ with two more parts equal to $1$, or $2$ is not a part of $\beta$ and
$\lambda$ is $\beta$ with one more part equal to $2$.

Source: Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025),
Article A109, Proposition 2 (`integers-2025-A109-prop-2`). -/
public theorem_wanted isDoublePerfect_one_iff (N : ℕ) (hN : 3 < N) (l : Multiset ℕ) :
    IsDoublePerfectOfOrder 1 N l ↔ ∃ β, IsPerfectPartition (N - 2) β ∧
      ((β.count 1 = 1 ∧ l = β + {1, 1}) ∨ (2 ∉ β ∧ l = β + {2}))

/-- **Lee's two forms of double-perfect partitions.** For an integer $B$, an integer $k \ge 2$ and
integers $q_3, \dots, q_k \ge 1$, write $T_B(q_3, \dots, q_k)$ for the parts
$B^{q_3}, (B(q_3+1))^{q_4}, \dots, (B(q_3+1) \cdots (q_{k-1}+1))^{q_k}$ (no parts when $k = 2$).
Let $N \ge 4$ and let $\lambda$ be a double-perfect partition of $N$ of order $1$. Then either
$\lambda = (1^3, 2^{q_2}, T_{2(q_2+1)}(q_3, \dots, q_k))$ for some $q_2 > 1$, some $k \ge 2$ and
some $q_3, \dots, q_k \ge 1$, or $\lambda = (1^{q_1}, 2, T_{q_1+1}(q_3, \dots, q_k))$ for some
$q_1 \ge 2$, some $k \ge 2$ and some $q_3, \dots, q_k \ge 1$.

The hypothesis $N \ge 4$ is needed, as for Lee's form of double-perfect partitions: $(1^3)$ is a
double-perfect partition of $3$ of order $1$ of neither form.

Source: Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025),
Article A109, Corollary 1 with displays (5), (6) (`integers-2025-A109-cor-1`). -/
public theorem_wanted doublePerfect_lee_forms (N : ℕ) (hN : 4 ≤ N) (l : Multiset ℕ)
    (hl : IsDoublePerfectOfOrder 1 N l) :
    (∃ q₂ : ℕ, ∃ qs : List ℕ, 1 < q₂ ∧ (∀ q ∈ qs, 1 ≤ q) ∧
      l = Multiset.replicate 3 1 + Multiset.replicate q₂ 2 +
        (perfectPartitionOfFactorization (qs.map (· + 1))).map ((2 * (q₂ + 1)) * ·)) ∨
    (∃ q₁ : ℕ, ∃ qs : List ℕ, 2 ≤ q₁ ∧ (∀ q ∈ qs, 1 ≤ q) ∧
      l = Multiset.replicate q₁ 1 + {2} +
        (perfectPartitionOfFactorization (qs.map (· + 1))).map ((q₁ + 1) * ·))

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
public theorem_wanted isTypeADoublePerfect_iff (r N : ℕ) (hr : 1 ≤ r) (hN : 2 * (r + 1) ≤ N)
    (l : Multiset ℕ) :
    IsTypeADoublePerfect r N l ↔ ∃ β, IsPerfectPartition (N - r - 1) β ∧
      ((β.count 1 = r ∧ l = β + Multiset.replicate (r + 1) 1) ∨
        (β.count 1 ≠ r ∧ r + 1 ∉ β ∧ l = β + {r + 1}))

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
public theorem_wanted typeADoublePerfect_forms (r N : ℕ) (hr : 1 ≤ r) (hN : 2 * (r + 1) ≤ N)
    (l : Multiset ℕ) (hl : IsTypeADoublePerfect r N l) :
    (∃ as : List ℕ, (∀ a ∈ as, 2 ≤ a) ∧ (r + 1) * as.prod = N - r ∧
      l = Multiset.replicate (r + 1) 1 + perfectPartitionOfFactorization ((r + 1) :: as)) ∨
    (∃ as : List ℕ, (∀ a ∈ as, 2 ≤ a) ∧ as.prod = N - r ∧ as.head? ≠ some (r + 1) ∧
      l = perfectPartitionOfFactorization as + {r + 1})

/-- **Number of Type-A double-perfect partitions.** Let $f(n)$ be the number of ordered
factorizations of $n$ into factors greater than $1$. Let $r \ge 1$ and $N \ge 2(r+1)$, that is,
$1 \le r \le \lfloor (N-2)/2 \rfloor$, and put $M = 2(r+1)$. The number $d_r(N)$ of Type-A
double-perfect partitions of $N$ of order $r$ is
$f(N-r) - f((N-r)/M) - (f(r+1) - 1) f((N-r)/(r+1))$ if $N \equiv r \pmod M$,
$f(N-r) - (f(r+1) - 1) f((N-r)/(r+1))$ if $N \equiv -1 \pmod M$, and $f(N-r)$ otherwise.

Source: Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025),
Article A109, Theorem 3, display (18) (`integers-2025-A109-thm-3`). -/
public theorem_wanted typeADoublePerfect_ncard (r N : ℕ) (hr : 1 ≤ r) (hN : 2 * (r + 1) ≤ N) :
    ({l | IsTypeADoublePerfect r N l}.ncard : ℤ) =
      if N % (2 * (r + 1)) = r then
        (orderedFactorizationCount (N - r) : ℤ) -
          orderedFactorizationCount ((N - r) / (2 * (r + 1))) -
          ((orderedFactorizationCount (r + 1) : ℤ) - 1) *
            orderedFactorizationCount ((N - r) / (r + 1))
      else if N % (2 * (r + 1)) = 2 * (r + 1) - 1 then
        (orderedFactorizationCount (N - r) : ℤ) -
          ((orderedFactorizationCount (r + 1) : ℤ) - 1) *
            orderedFactorizationCount ((N - r) / (r + 1))
      else orderedFactorizationCount (N - r)

/-- **Adding equal parts to a Type-A double-perfect partition.** Let $r \ge 1$ and
$n \ge 2(r+1)$ be integers, and let $\lambda$ be a Type-A double-perfect partition of $n$ of
order $r$. Then for every natural number $m$, the partition obtained from $\lambda$ by adding $m$
parts equal to $n - r$ is a Type-A double-perfect partition of $n + m(n - r)$ of order $r$.

The bound $n \ge 2(r+1)$ is needed: for $r = 1$ and $n = 2$, the partition $(1^2)$, obtained
from the empty perfect partition of $0$ by adding two parts $1$, is Type-A double-perfect of
order $1$, but adding $m = 2$ parts equal to $1$ gives $(1^4)$, which is not double-perfect of
order $1$ because it contains only one partition of $2$.

Source: Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025),
Article A109, Proposition 3 (`integers-2025-A109-prop-3`). -/
public theorem_wanted isTypeADoublePerfect_add_replicate (r n : ℕ) (hr : 1 ≤ r)
    (hn : 2 * (r + 1) ≤ n) (l : Multiset ℕ) (hl : IsTypeADoublePerfect r n l) (m : ℕ) :
    IsTypeADoublePerfect r (n + m * (n - r)) (l + Multiset.replicate m (n - r))

/-- **Inserting copies of a part into a double-perfect partition.** Let $r \ge 1$,
$n \ge 2(r+1)$, and let $\lambda$ be a double-perfect partition of $n$ of order $r$. For every
$m \ge 0$, adding $m$ parts equal to $n - r$ to $\lambda$ gives a double-perfect partition of
$n + m(n - r)$ of order $r$.

The hypothesis $n \ge 2(r+1)$ is needed: for $r = 1$, $(1^2)$ is a double-perfect partition of $2$
of order $1$, but adding $m = 2$ parts equal to $1$ gives $(1^4)$, which is not double-perfect of
order $1$.

Source: Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025),
Article A109, Theorem 4 (`integers-2025-A109-thm-4`). -/
public theorem_wanted isDoublePerfectOfOrder_add_replicate (r n : ℕ) (hr : 1 ≤ r)
    (hn : 2 * (r + 1) ≤ n) (l : Multiset ℕ) (hl : IsDoublePerfectOfOrder r n l) (m : ℕ) :
    IsDoublePerfectOfOrder r (n + m * (n - r)) (l + Multiset.replicate m (n - r))

/-- **Adding a copy of the largest part to a double-perfect partition.** Let $r \ge 1$,
$n \ge 2(r+1)$, and let $\lambda$ be a double-perfect partition of $n$ of order $r$ whose largest
part $\ell$ is not $r + 1$. Then $\lambda$ with one more part $\ell$ is a double-perfect partition
of $n + \ell$ of order $r$. The condition $\ell \ne r + 1$ cannot be dropped: $(1^2, 3^4, 6)$ is
a Type-A double-perfect partition of $20$ of order $5$, but $(1^2, 3^4, 6^2)$ is not a
double-perfect partition of $26$ of order $5$.

The hypothesis $n \ge 2(r+1)$ is needed: for $r = 1$, $(1^3)$ is a double-perfect partition of
$3$ of order $1$, but $(1^4)$ is not a double-perfect partition of $4$ of order $1$.

Source: Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025),
Article A109, Corollary 3 (`integers-2025-A109-cor-3`). -/
public theorem_wanted isDoublePerfectOfOrder_add_largest :
    (∀ (r n : ℕ), 1 ≤ r → 2 * (r + 1) ≤ n → ∀ l : Multiset ℕ, IsDoublePerfectOfOrder r n l →
      l.sup ≠ r + 1 → IsDoublePerfectOfOrder r (n + l.sup) (l + {l.sup})) ∧
    IsTypeADoublePerfect 5 20 {1, 1, 3, 3, 3, 3, 6} ∧
    ¬ IsDoublePerfectOfOrder 5 26 {1, 1, 3, 3, 3, 3, 6, 6}

/-- **Halved perfect partitions are double-perfect but not of Type A.** For integers
$a_1, \dots, a_k \ge 2$ write $P(a_1, \dots, a_k)$ for the perfect partition
$(1^{a_1-1}, a_1^{a_2-1}, (a_1a_2)^{a_3-1}, \dots, (a_1 \cdots a_{k-1})^{a_k-1})$. Let $N$ and
$r \ge 1$ be natural numbers, let $a_1, \dots, a_k \ge 2$ and $1 < j < k$ with
$a_1 \cdots a_j = 2(r+1)$, $a_1 \cdots a_k = 2(N - r)$, $a_j > 2$ and $a_{j+1} > 2$. Let
$\lambda$ consist of the parts of $P(a_1, \dots, a_j)$ together with $r + 1$ times each part of
$P(a_{j+1}, \dots, a_k)$, that is,
$\lambda = (1^{a_1-1}, a_1^{a_2-1}, \dots, (a_1 \cdots a_{j-1})^{a_j-1},
(a_1 \cdots a_j/2)^{a_{j+1}-1}, \dots, (a_1 \cdots a_{k-1}/2)^{a_k-1})$. Then $\lambda$ is a
double-perfect partition of $N$ of order $r$ and is not a Type-A double-perfect partition of $N$
of order $r$.

Source: Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025),
Article A109, Theorem 5 with conditions (23)-(25) and display (26)
(`integers-2025-A109-thm-5`). -/
public theorem_wanted halvedPerfect_isDoublePerfect_not_typeA (r N : ℕ) (hr : 1 ≤ r)
    (b c : List ℕ) (hb : ∀ a ∈ b, 2 ≤ a) (hc : ∀ a ∈ c, 2 ≤ a) (hblen : 2 ≤ b.length)
    (hc0 : c ≠ []) (hbprod : b.prod = 2 * (r + 1)) (hprod : (b ++ c).prod = 2 * (N - r))
    (hbj : ∀ x ∈ b.getLast?, 2 < x) (hcj : ∀ x ∈ c.head?, 2 < x) :
    IsDoublePerfectOfOrder r N
        (perfectPartitionOfFactorization b +
          (perfectPartitionOfFactorization c).map ((r + 1) * ·)) ∧
      ¬ IsTypeADoublePerfect r N
        (perfectPartitionOfFactorization b +
          (perfectPartitionOfFactorization c).map ((r + 1) * ·))

/-- **Number of Type-B double-perfect partitions.** Let $f(n)$ be the number of ordered
factorizations of $n$ into factors greater than $1$. Let $r \ge 1$ and $N \ge 3r + 4$, that is,
$1 \le r \le \lfloor (N-4)/3 \rfloor$, and put $M = 2(r+1)$ and $c = f(M) - 1 - f(r+1)$. The
number $e_r(N)$ of Type-B double-perfect partitions of $N$ of order $r$, that is, of
double-perfect partitions of $N$ of order $r$ that are not of Type A, is
$c\,(f((N-r)/(r+1)) - f((N-r)/M))$ if $N \equiv r \pmod M$, $c\, f((N-r)/(r+1))$ if
$N \equiv -1 \pmod M$, and $0$ otherwise.

Source: Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025),
Article A109, Theorem 6, display (27) (`integers-2025-A109-thm-6`). -/
public theorem_wanted typeBDoublePerfect_ncard (r N : ℕ) (hr : 1 ≤ r) (hN : 3 * r + 4 ≤ N) :
    ({l | IsDoublePerfectOfOrder r N l ∧ ¬ IsTypeADoublePerfect r N l}.ncard : ℤ) =
      if N % (2 * (r + 1)) = r then
        ((orderedFactorizationCount (2 * (r + 1)) : ℤ) - 1 - orderedFactorizationCount (r + 1)) *
          ((orderedFactorizationCount ((N - r) / (r + 1)) : ℤ) -
            orderedFactorizationCount ((N - r) / (2 * (r + 1))))
      else if N % (2 * (r + 1)) = 2 * (r + 1) - 1 then
        ((orderedFactorizationCount (2 * (r + 1)) : ℤ) - 1 - orderedFactorizationCount (r + 1)) *
          orderedFactorizationCount ((N - r) / (r + 1))
      else 0

/-- **Number of double-perfect partitions of higher order.** Let $f(m)$ be the number of ordered
factorizations of $m$ into factors greater than $1$. Let $r \ge 1$ and $N \ge 2(r+1)$
(equivalently $1 \le r \le \lfloor (N-2)/2 \rfloor$), put $M = 2(r+1)$, and let $u_r(N)$ be the
number of double-perfect partitions of $N$ of order $r$. Then $u_r(N)$ equals
$f(N-r) + (f(M) - 2f(r+1)) f((N-r)/(r+1)) - (f(M) - f(r+1)) f((N-r)/M)$ if $N \equiv r \pmod M$,
$f(N-r) + (f(M) - 2f(r+1)) f((N-r)/(r+1))$ if $N \equiv -1 \pmod M$, and $f(N-r)$ otherwise.

Source: Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025),
Article A109, Theorem 7, display (28) (`integers-2025-A109-thm-7`). -/
public theorem_wanted doublePerfectOfOrder_ncard (r N : ℕ) (hr : 1 ≤ r)
    (hN : 2 * (r + 1) ≤ N) :
    ({l | IsDoublePerfectOfOrder r N l}.ncard : ℤ) =
      if N % (2 * (r + 1)) = r then
        (orderedFactorizationCount (N - r) : ℤ) +
          ((orderedFactorizationCount (2 * (r + 1)) : ℤ) - 2 * orderedFactorizationCount (r + 1)) *
            orderedFactorizationCount ((N - r) / (r + 1)) -
          ((orderedFactorizationCount (2 * (r + 1)) : ℤ) - orderedFactorizationCount (r + 1)) *
            orderedFactorizationCount ((N - r) / (2 * (r + 1)))
      else if N % (2 * (r + 1)) = 2 * (r + 1) - 1 then
        (orderedFactorizationCount (N - r) : ℤ) +
          ((orderedFactorizationCount (2 * (r + 1)) : ℤ) - 2 * orderedFactorizationCount (r + 1)) *
            orderedFactorizationCount ((N - r) / (r + 1))
      else orderedFactorizationCount (N - r)

end

end MetaMathlibExt
