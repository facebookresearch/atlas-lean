/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Set.Card

/-!
# Diagonal sequences of integer partitions

Statements from Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer
Partitions*, INTEGERS 25 (2025), Article A60 (arXiv:2412.06856).

For a partition `α = (α₁ ≥ α₂ ≥ ⋯ ≥ α_t)` the diagonal sequence is `δ(α) = (d_k)_{k ≥ 1}` with
`d_k = |{i | 1 ≤ i ≤ k, α_i + i - 1 ≥ k}|`, the number of cells of the Young diagram on the
`k`-th upper-right to lower-left diagonal. Partitions are `Nat.Partition n`; a diagonal sequence
is a function `ℕ → ℕ` with the paper's indexing `d_1, d_2, …` and the value `0` at index `0`.
`[d]` is the set of partitions with diagonal sequence `d`. The definitions follow the arXiv
version of the paper (Definition (1.1), Proposition 2.3, Section 4).
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Diagonal sequence of a partition.** Let $\alpha$ be a partition with parts
$\alpha_1 \ge \alpha_2 \ge \dots \ge \alpha_t$, and set $\alpha_i = 0$ for $i > t$. Its diagonal
sequence $\delta(\alpha) = (d_k)_{k \ge 0}$ has $d_0 = 0$ and, for $k \ge 1$, $d_k$ equal to the
number of indices $i$ with $1 \le i \le k$ and $\alpha_i + i - 1 \ge k$, that is, the number of
cells of the Young diagram on its $k$-th diagonal from upper right to lower left. Equivalently,
$d_k$ is the number of $i$ with $1 \le i \le k$ such that at least $i$ parts of $\alpha$ are at
least $k + 1 - i$; the definition uses this form, with the parts given as a finite multiset of
natural numbers.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Section 1, Definition of the diagonal sequence (1.1). -/
def diagonalSequence (s : Multiset ℕ) (k : ℕ) : ℕ :=
  ((Finset.Icc 1 k).filter fun i => i ≤ s.countP (k + 1 - i ≤ ·)).card

/-- **Diagonal sequence of $(7, 7, 4, 1, 1, 1)$.** The diagonal sequence of the partition
$(7, 7, 4, 1, 1, 1)$ takes the values $0, 1, 2, 3, 4, 4, 4, 2, 1, 0$ at the indices
$0, 1, \dots, 9$. This is the paper's running example.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Section 1 (example after the definition); characteristic check
of `diagonalSequence`. -/
theorem diagonalSequence_seven_seven_four_one_one_one :
    (List.range 10).map (diagonalSequence {7, 7, 4, 1, 1, 1}) = [0, 1, 2, 3, 4, 4, 4, 2, 1, 0] := by
  decide +kernel

/-- **Sequence of a finite list.** A finite list $(d_1, \dots, d_\ell)$ of natural numbers
determines the sequence of natural numbers whose value at index $k$ is $d_k$ for
$1 \le k \le \ell$, and $0$ for $k = 0$ and for $k > \ell$. This is the indexing of diagonal
sequences, which take the value $0$ at index $0$.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Section 1 (trailing zeroes of `δ(α)` are omitted). -/
def diagonalOfList (l : List ℕ) (k : ℕ) : ℕ :=
  (0 :: l).getD k 0

/-- **The list sequence of $(1, 2, 1)$.** The sequence given by the list $(1, 2, 1)$ takes the
values $0, 1, 2, 1, 0, 0$ at the indices $0, 1, 2, 3, 4, 5$.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Section 1; characteristic check of `diagonalOfList`. -/
theorem diagonalOfList_one_two_one :
    (List.range 6).map (diagonalOfList [1, 2, 1]) = [0, 1, 2, 1, 0, 0] := by
  decide

/-- **Normal form of a diagonal sequence.** For a natural number $q$ and a sequence
$s = (s_k)$ of natural numbers, the normal form is the list
$(1, 2, \dots, q - 1, q, q^{(s_q)}, (q-1)^{(s_{q-1})}, \dots, 1^{(s_1)})$, where $v^{(m)}$
denotes $m$ copies of $v$: the numbers $1, \dots, q$ followed by $s_v$ copies of $v$ for
$v = q, q - 1, \dots, 1$.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Corollary 1, display (2.1). -/
def diagonalNormalForm (q : ℕ) (s : ℕ → ℕ) : List ℕ :=
  List.range' 1 q ++ (List.range q).reverse.flatMap fun j => List.replicate (s (j + 1)) (j + 1)

/-- **Diagonal normal form for $q = 4$ and $s = (1, 1, 0, 2)$.** For $q = 4$ and $s_1 = 1$,
$s_2 = 1$, $s_3 = 0$, $s_4 = 2$, the diagonal normal form
$(1, 2, 3, 4, 4^{(s_4)}, 3^{(s_3)}, 2^{(s_2)}, 1^{(s_1)})$, where $v^{(m)}$ denotes $m$ copies
of $v$, is $(1, 2, 3, 4, 4, 4, 2, 1)$.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Section 2 (example after Corollary 4); characteristic check of
`diagonalNormalForm`. -/
theorem diagonalNormalForm_four_example :
    diagonalNormalForm 4 (fun k => [0, 1, 1, 0, 2].getD k 0) = [1, 2, 3, 4, 4, 4, 2, 1] := by
  decide

/-- **Maximal partition of a diagonal normal form.** For a natural number $q$ and a sequence
$s = (s_k)$ of natural numbers, $\bar\alpha = (\bar\alpha_1, \dots, \bar\alpha_q)$ is the list of
the $q$ numbers $\bar\alpha_i = q - i + 1 + \sum_{k=i}^{q} s_k$, $1 \le i \le q$, in this order.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Proposition 1. -/
def diagonalMaxPartition (q : ℕ) (s : ℕ → ℕ) : List ℕ :=
  (List.range q).map fun j => q - j + ∑ k ∈ Finset.Icc (j + 1) q, s k

/-- **Maximal partition for $q = 4$ and $s = (1, 1, 0, 2)$.** For $q = 4$ and $s_1 = 1$,
$s_2 = 1$, $s_3 = 0$, $s_4 = 2$, the maximal partition $\bar\alpha$, with parts
$\bar\alpha_i = q - i + 1 + \sum_{k=i}^{q} s_k$ for $1 \le i \le q$, is $(8, 6, 4, 3)$.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Section 2 (example after Corollary 4); characteristic check of
`diagonalMaxPartition`. -/
theorem diagonalMaxPartition_four_example :
    diagonalMaxPartition 4 (fun k => [0, 1, 1, 0, 2].getD k 0) = [8, 6, 4, 3] := by
  decide

/-- **Minimal partition of a diagonal normal form.** For a natural number $q$ and a sequence
$s = (s_k)$ of natural numbers, $\underline\alpha$ is the list
$(q^{(s_q + 1)}, (q-1)^{(s_{q-1} + 1)}, \dots, 1^{(s_1 + 1)})$, where $v^{(m)}$ denotes $m$
copies of $v$: first $s_q + 1$ copies of $q$, then $s_{q-1} + 1$ copies of $q - 1$, and so on
down to $s_1 + 1$ copies of $1$.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Proposition 2. -/
def diagonalMinPartition (q : ℕ) (s : ℕ → ℕ) : List ℕ :=
  (List.range q).reverse.flatMap fun j => List.replicate (s (j + 1) + 1) (j + 1)

/-- **Minimal partition for $q = 4$ and $s = (1, 1, 0, 2)$.** For $q = 4$ and $s_1 = 1$,
$s_2 = 1$, $s_3 = 0$, $s_4 = 2$, the minimal partition
$\underline\alpha = (4^{(s_4 + 1)}, 3^{(s_3 + 1)}, 2^{(s_2 + 1)}, 1^{(s_1 + 1)})$, where
$v^{(m)}$ denotes $m$ copies of $v$, is $(4, 4, 4, 3, 2, 2, 1, 1)$.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Section 2 (example after Corollary 4); characteristic check of
`diagonalMinPartition`. -/
theorem diagonalMinPartition_four_example :
    diagonalMinPartition 4 (fun k => [0, 1, 1, 0, 2].getD k 0) = [4, 4, 4, 3, 2, 2, 1, 1] := by
  decide

/-- **Conjugate of a multiset of parts.** For a finite multiset $\alpha$ of natural numbers with
largest element $m$ (and $m = 0$ if $\alpha$ is empty), the conjugate $\alpha^*$ is the multiset
of the $m$ numbers $c_0, c_1, \dots, c_{m-1}$, where $c_j$ is the number of elements of $\alpha$
greater than $j$, counted with multiplicity. When $\alpha$ is the multiset of parts of a
partition, these are the parts of the conjugate partition.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Section 1 (conjugate partition `α*`). -/
def conjugateParts (s : Multiset ℕ) : Multiset ℕ :=
  (Multiset.range s.sup).map fun j => s.countP (j < ·)

/-- **The conjugate of $(3, 1)$ is $(2, 1, 1)$.** The conjugate of the partition with parts
$\{3, 1\}$ is the partition with parts $\{2, 1, 1\}$.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Section 1; characteristic check of `conjugateParts`. -/
theorem conjugateParts_three_one : conjugateParts {3, 1} = {2, 1, 1} := by
  decide

/-- **Diagonal class of a partition.** For a partition $p$ of $n$, its diagonal class
$\delta^{-1}(\delta(p))$ is the finite set of all partitions $\beta$ of $n$ whose diagonal
sequence $\delta(\beta)$ equals the diagonal sequence $\delta(p)$ of $p$.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Section 1 (definition of `[d]`). -/
noncomputable def diagonalClass {n : ℕ} (p : Nat.Partition n) : Finset (Nat.Partition n) :=
  open Classical in Finset.univ.filter fun β => diagonalSequence β.parts = diagonalSequence p.parts

/-- **Every partition lies in its diagonal class.** For every partition $p$ of $n$, $p$ belongs
to the diagonal class of $p$, the set of partitions of $n$ whose diagonal sequence equals that
of $p$.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Section 1 (definition of `[d]`); characteristic check of
`diagonalClass`. -/
theorem mem_diagonalClass_self {n : ℕ} (p : Nat.Partition n) : p ∈ diagonalClass p := by
  simp [diagonalClass]

/-- **Partitions with a prescribed diagonal sequence.** For a natural number $n$ and a sequence
$d = (d_k)_{k \ge 0}$ of natural numbers, $[d]$ is the finite set of partitions $\beta$ of $n$
whose diagonal sequence $\delta(\beta)$ equals $d$.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Section 1 (definition of `[d]` for `d ∈ Δ(n)`). -/
noncomputable def diagonalClassOf (n : ℕ) (d : ℕ → ℕ) : Finset (Nat.Partition n) :=
  open Classical in Finset.univ.filter fun β => diagonalSequence β.parts = d

/-- **A partition lies in the class of its diagonal sequence.** Every partition $\beta$ of $n$
belongs to the set of partitions of $n$ whose diagonal sequence equals that of $\beta$.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Section 1 (definition of `[d]`); characteristic check of
`diagonalClassOf`. -/
theorem mem_diagonalClassOf_diagonalSequence {n : ℕ} (β : Nat.Partition n) :
    β ∈ diagonalClassOf n (diagonalSequence β.parts) := by
  simp [diagonalClassOf]

/-- **Majorization of part lists.** For finite lists $a = (a_1, \dots, a_s)$ and
$b = (b_1, \dots, b_t)$ of natural numbers, $a$ majorizes $b$, written $a \succ b$, when
$b_1 + \dots + b_k \le a_1 + \dots + a_k$ for every natural number $k \le \min\{s, t\}$.

No ordering of the lists is required; the source applies majorization to the parts of partitions
listed in decreasing order.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Section 3 (definition of majorization). -/
def PartitionMajorizes (a b : List ℕ) : Prop :=
  ∀ k ≤ min a.length b.length, (b.take k).sum ≤ (a.take k).sum

/-- **Majorization of $(2, 2)$ by $(3, 1)$.** The partition $(3, 1)$ majorizes the partition
$(2, 2)$: $3 \ge 2$ and $3 + 1 \ge 2 + 2$.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Section 3; characteristic check of `PartitionMajorizes`. -/
theorem partitionMajorizes_three_one_two_two : PartitionMajorizes [3, 1] [2, 2] := by
  unfold PartitionMajorizes
  decide

/-- **Number of $k$-vn-arrangements.** Let $k$ be a natural number and $M$ a finite multiset of
integers. A $k$-vn-arrangement of $M$ is a finite sequence $(v_1, \dots, v_b)$ of integers whose
multiset of entries is $M$ and with $v_{i+1} - v_i \le k$ for all $1 \le i < b$. This is the
number of distinct such sequences; sequences are compared entry by entry, so exchanging two
equal entries gives the same arrangement. For $k = 1$ these are the vn-arrangements.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Section 4 (definitions of vn-arrangement and
k-vn-arrangement). -/
noncomputable def vnArrangementCount (k : ℕ) (M : Multiset ℤ) : ℕ :=
  Set.ncard {l : List ℤ | (l : Multiset ℤ) = M ∧ l.IsChain fun a b => b - a ≤ (k : ℤ)}

/-- **A singleton multiset has one $k$-vn-arrangement.** For every natural number $k$ and every
integer $a$, the one-element multiset $\{a\}$ has exactly one $k$-vn-arrangement.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Section 4; characteristic check of `vnArrangementCount`. -/
theorem vnArrangementCount_singleton (k : ℕ) (a : ℤ) : vnArrangementCount k {a} = 1 := by
  have h : {l : List ℤ | (l : Multiset ℤ) = {a} ∧ l.IsChain fun a b => b - a ≤ (k : ℤ)} =
      {[a]} := by
    ext l
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Multiset.coe_eq_singleton]
    constructor
    · exact fun h => h.1
    · rintro rfl
      exact ⟨rfl, List.isChain_singleton _⟩
  rw [vnArrangementCount, h, Set.ncard_singleton]

/-- **Increments of the diagonal sequence.** Let $\alpha$ be a partition of $n$ with diagonal
sequence $(d_k)_{k \ge 0}$, where $d_0 = 0$, and let $k \ge 0$. Then $d_{k+1} \le d_k + 1$, with
equality if and only if $d_j = j$ for every $j$ with $1 \le j \le k + 1$. Moreover, if
$d_{k+1} \le d_k$, then $d_{k+2} \le d_{k+1}$.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Lemma 1. -/
public theorem_wanted diagonalSequence_succ_le_and_antitone {n : ℕ} (p : Nat.Partition n)
    (k : ℕ) :
    (diagonalSequence p.parts (k + 1) ≤ diagonalSequence p.parts k + 1 ∧
      (diagonalSequence p.parts (k + 1) = diagonalSequence p.parts k + 1 ↔
        ∀ j ∈ Finset.Icc 1 (k + 1), diagonalSequence p.parts j = j)) ∧
    (diagonalSequence p.parts (k + 1) ≤ diagonalSequence p.parts k →
      diagonalSequence p.parts (k + 2) ≤ diagonalSequence p.parts (k + 1))

/-- **Existence and uniqueness of the diagonal normal form.** Write $v^{(m)}$ for $m$ copies of
$v$. For every partition $\alpha$ of $n \ge 1$ there are an integer $q > 0$ and natural numbers
$s_1, \dots, s_q$ such that the diagonal sequence of $\alpha$, indexed from $0$, is
$(0, 1, 2, \dots, q, q^{(s_q)}, (q-1)^{(s_{q-1})}, \dots, 1^{(s_1)}, 0, 0, \dots)$ and
$q(q+1)/2 + \sum_{k=1}^{q} k s_k = n$. Moreover $q$ and $s_1, \dots, s_q$ are unique: if
$q' > 0$ and $s'_1, \dots, s'_{q'}$ give the same diagonal sequence, then $q' = q$ and
$s'_k = s_k$ for $1 \le k \le q$.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Corollary 1. -/
public theorem_wanted exists_unique_diagonalNormalForm {n : ℕ} (hn : 0 < n)
    (p : Nat.Partition n) :
    ∃ q, 0 < q ∧ ∃ s : ℕ → ℕ,
      diagonalSequence p.parts = diagonalOfList (diagonalNormalForm q s) ∧
      q * (q + 1) / 2 + ∑ k ∈ Finset.Icc 1 q, k * s k = n ∧
      ∀ q' (s' : ℕ → ℕ), 0 < q' →
        diagonalSequence p.parts = diagonalOfList (diagonalNormalForm q' s') →
        q' = q ∧ ∀ k ∈ Finset.Icc 1 q, s' k = s k

/-- **The maximal partition has the prescribed diagonal normal form.** Let $q > 0$ and let
$s_1, \dots, s_q$ be natural numbers with $q(q+1)/2 + \sum_{k=1}^{q} k s_k = n$, and let
$\bar\alpha = (\bar\alpha_1, \dots, \bar\alpha_q)$ with
$\bar\alpha_i = q - i + 1 + \sum_{k=i}^{q} s_k$. Then the entries of $\bar\alpha$ are positive,
sum to $n$ and are strictly decreasing; the diagonal sequence of $\bar\alpha$ is
$(1, 2, \dots, q, q^{(s_q)}, (q-1)^{(s_{q-1})}, \dots, 1^{(s_1)})$ followed by zeros, where
$v^{(m)}$ denotes $m$ copies of $v$; $s_i = \bar\alpha_i - \bar\alpha_{i+1} - 1$ for
$1 \le i < q$; and $s_q = \bar\alpha_q - 1$.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Proposition 1. -/
public theorem_wanted diagonalMaxPartition_spec (n q : ℕ) (hq : 0 < q) (s : ℕ → ℕ)
    (hn : q * (q + 1) / 2 + ∑ k ∈ Finset.Icc 1 q, k * s k = n) :
    ((diagonalMaxPartition q s).sum = n ∧ ∀ x ∈ diagonalMaxPartition q s, 0 < x) ∧
    (diagonalMaxPartition q s).SortedGT ∧
    diagonalSequence ↑(diagonalMaxPartition q s) = diagonalOfList (diagonalNormalForm q s) ∧
    (∀ i ∈ Finset.Ico 1 q, s i =
      (diagonalMaxPartition q s).getD (i - 1) 0 - (diagonalMaxPartition q s).getD i 0 - 1) ∧
    s q = (diagonalMaxPartition q s).getD (q - 1) 0 - 1

/-- **Counting diagonal sequences.** For every natural number $n$, including $n = 0$, the number
of distinct diagonal sequences of partitions of $n$ equals the number of partitions of $n$ into
distinct parts, and the number of partitions of $n$ into distinct parts equals the number of
partitions of $n$ into odd parts.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Corollary 2. -/
public theorem_wanted ncard_diagonalSequences_eq_card_distincts (n : ℕ) :
    (Set.range fun p : Nat.Partition n => diagonalSequence p.parts).ncard =
        (Nat.Partition.distincts n).card ∧
      (Nat.Partition.distincts n).card = (Nat.Partition.odds n).card

/-- **Conjugate of a partition with prescribed gaps between its parts.** Let $q \ge 0$ and let
$s_1, \dots, s_q$ be natural numbers. The conjugate of the partition $\bar\alpha$ with parts
$\bar\alpha_i = q - i + 1 + \sum_{k=i}^{q} s_k$ for $1 \le i \le q$ is the partition
$\underline{\alpha} = (q^{(s_q + 1)}, (q-1)^{(s_{q-1} + 1)}, \dots, 1^{(s_1 + 1)})$, where
$v^{(r)}$ means $r$ copies of $v$; the parts are compared as multisets.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Proposition 2. -/
public theorem_wanted conjugateParts_diagonalMaxPartition (q : ℕ) (s : ℕ → ℕ) :
    conjugateParts ↑(diagonalMaxPartition q s) = ↑(diagonalMinPartition q s)

/-- **Equal diagonal sequences of the maximal and minimal partitions.** Let $q \ge 0$ and
$s_1, \dots, s_q \ge 0$ be natural numbers, write $v^{(m)}$ for $m$ copies of $v$, and let
$\bar\alpha$ and $\underline\alpha$ be the partitions with parts
$\bar\alpha_i = q - i + 1 + s_i + s_{i+1} + \dots + s_q$ for $1 \le i \le q$ and
$\underline\alpha = (q^{(s_q + 1)}, (q-1)^{(s_{q-1} + 1)}, \dots, 1^{(s_1 + 1)})$. Then
$\bar\alpha$ and $\underline\alpha$ have the same diagonal sequence; this diagonal sequence,
indexed from $0$, is $(0, 1, 2, \dots, q, q^{(s_q)}, \dots, 1^{(s_1)}, 0, 0, \dots)$; and the
multiset of its nonzero entries $1, 2, \dots, q, q^{(s_q)}, \dots, 1^{(s_1)}$ equals the multiset
of parts of $\underline\alpha$.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Corollary 3. -/
public theorem_wanted diagonalSequence_max_eq_min_and_multiset (q : ℕ) (s : ℕ → ℕ) :
    diagonalSequence ↑(diagonalMaxPartition q s) =
        diagonalSequence ↑(diagonalMinPartition q s) ∧
      diagonalSequence ↑(diagonalMinPartition q s) = diagonalOfList (diagonalNormalForm q s) ∧
      (↑(diagonalNormalForm q s) : Multiset ℕ) = ↑(diagonalMinPartition q s)

/-- **Repeated parts and large gaps in a diagonal class.** Let $q \ge 0$ and
$s_1, \dots, s_q \ge 0$ be natural numbers, write $v^{(m)}$ for $m$ copies of $v$, and let
$\bar\alpha$ and $\underline\alpha$ be the partitions with parts
$\bar\alpha_i = q - i + 1 + s_i + s_{i+1} + \dots + s_q$ for $1 \le i \le q$ and
$\underline\alpha = (q^{(s_q + 1)}, (q-1)^{(s_{q-1} + 1)}, \dots, 1^{(s_1 + 1)})$. Let $\alpha$
be a partition of $n$ with parts $\alpha_1 \ge \dots \ge \alpha_t$, set $\alpha_{t+1} = 0$, and
suppose that the diagonal sequence of $\alpha$, indexed from $0$, is
$(0, 1, 2, \dots, q, q^{(s_q)}, \dots, 1^{(s_1)}, 0, 0, \dots)$. If $\alpha \ne \bar\alpha$, then
$\alpha_i = \alpha_{i+1}$ for some $i$ with $1 \le i < t$. If $\alpha \ne \underline\alpha$, then
$\alpha_i - \alpha_{i+1} \ge 2$ for some $i$ with $1 \le i \le t$.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Corollary 4. -/
public theorem_wanted exists_eq_succ_of_ne_diagonalMaxPartition {n : ℕ} (p : Nat.Partition n)
    (q : ℕ) (s : ℕ → ℕ)
    (hd : diagonalSequence p.parts = diagonalOfList (diagonalNormalForm q s)) :
    (p.parts.sort (· ≥ ·) ≠ diagonalMaxPartition q s →
      ∃ i, i + 1 < p.parts.card ∧
        (p.parts.sort (· ≥ ·)).getD i 0 = (p.parts.sort (· ≥ ·)).getD (i + 1) 0) ∧
    (p.parts.sort (· ≥ ·) ≠ diagonalMinPartition q s →
      ∃ i, i < p.parts.card ∧
        (p.parts.sort (· ≥ ·)).getD (i + 1) 0 + 1 < (p.parts.sort (· ≥ ·)).getD i 0)

/-- **The largest part of a partition with given diagonal sequence.** Let $\alpha$ be a partition
of $n$, let $q$ and $s_1, s_2, \dots$ be natural numbers, and suppose the diagonal sequence of
$\alpha$ is $(1, 2, \dots, q, q^{(s_q)}, (q-1)^{(s_{q-1})}, \dots, 1^{(s_1)})$ followed by zeros,
where $v^{(m)}$ denotes $m$ copies of $v$. Then the largest part of $\alpha$ (taken to be $0$ if
$\alpha$ has no parts) lies in the set
$A_1 = \{q + \sum_{i=j}^{q} s_i : 1 \le j \le q + 1\}$, that is,
$A_1 = \{q, q + s_q, q + s_q + s_{q-1}, \dots, q + s_q + \dots + s_1\}$.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Proposition 3. -/
public theorem_wanted sup_parts_mem_diagonalFirstPartSet {n : ℕ} (p : Nat.Partition n) (q : ℕ)
    (s : ℕ → ℕ) (hd : diagonalSequence p.parts = diagonalOfList (diagonalNormalForm q s)) :
    p.parts.sup ∈ (Finset.Icc 1 (q + 1)).image fun j => q + ∑ i ∈ Finset.Icc j q, s i

/-- **Sums of squared parts and the diagonal sequence.** Let $\alpha$ be a partition of $n$ with
diagonal sequence $(d_k)_{k \ge 1}$ and conjugate partition $\alpha^*$, and write $s(\gamma)$ for
the sum of the squares of the parts of a partition $\gamma$. Then
$s(\alpha) + s(\alpha^*) = 2 \sum_{k=1}^{2n} k \, d_k$. Consequently every partition $\beta$ of
$n$ with the same diagonal sequence as $\alpha$ satisfies
$s(\beta) + s(\beta^*) = s(\alpha) + s(\alpha^*)$.

The paper sums only up to the last diagonal $t + \alpha_1 - 1$, where $t$ is the number of parts
and $\alpha_1$ the largest part; summing to $2n$ adds only zero terms.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Proposition 4. -/
public theorem_wanted sum_sq_add_sum_sq_conjugate_eq {n : ℕ} (p : Nat.Partition n) :
    (p.parts.map (· ^ 2)).sum + ((conjugateParts p.parts).map (· ^ 2)).sum =
        2 * ∑ k ∈ Finset.Icc 1 (2 * n), k * diagonalSequence p.parts k ∧
      ∀ β : Nat.Partition n, diagonalSequence β.parts = diagonalSequence p.parts →
        (β.parts.map (· ^ 2)).sum + ((conjugateParts β.parts).map (· ^ 2)).sum =
          (p.parts.map (· ^ 2)).sum + ((conjugateParts p.parts).map (· ^ 2)).sum

/-- **Conjugation reverses majorization.** For partitions $\alpha$ and $\beta$ of $n$, with parts
listed in decreasing order, $\alpha$ majorizes $\beta$ if and only if the conjugate partition
$\beta^*$ majorizes the conjugate partition $\alpha^*$, again with parts listed in decreasing
order.

This is Theorem 7.B.5 of Marshall, Olkin and Arnold, as quoted in the source.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, proof of Proposition 5 (citing [4], Theorem 7.B.5). -/
public theorem_wanted partitionMajorizes_iff_conjugate {n : ℕ} (α β : Nat.Partition n) :
    PartitionMajorizes (α.parts.sort (· ≥ ·)) (β.parts.sort (· ≥ ·)) ↔
      PartitionMajorizes ((conjugateParts β.parts).sort (· ≥ ·))
        ((conjugateParts α.parts).sort (· ≥ ·))

/-- **The diagonal class lies between the maximal and minimal partitions in majorization.** Let
$p$ be a partition of $n$, let $q$ be a natural number and $s = (s_k)$ a sequence of natural
numbers, and suppose that the diagonal sequence of $p$ is $(1, 2, \dots, q, q^{(s_q)},
(q-1)^{(s_{q-1})}, \dots, 1^{(s_1)})$ followed by zeros, where $v^{(m)}$ denotes $m$ copies of
$v$. Let $\alpha$ be the parts of $p$ in decreasing order, let
$\bar\alpha = (\bar\alpha_1, \dots, \bar\alpha_q)$ with
$\bar\alpha_i = q - i + 1 + \sum_{k=i}^{q} s_k$, and let
$\underline\alpha = (q^{(s_q + 1)}, (q-1)^{(s_{q-1} + 1)}, \dots, 1^{(s_1 + 1)})$. Then
$\bar\alpha \succ \alpha$ and $\alpha \succ \underline\alpha$, where for lists $a$ and $b$,
$a \succ b$ means $b_1 + \dots + b_k \le a_1 + \dots + a_k$ for every $k$ up to the length of
the shorter list.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Proposition 5. -/
public theorem_wanted diagonalMaxPartition_majorizes_majorizes_min {n : ℕ}
    (p : Nat.Partition n) (q : ℕ) (s : ℕ → ℕ)
    (hd : diagonalSequence p.parts = diagonalOfList (diagonalNormalForm q s)) :
    PartitionMajorizes (diagonalMaxPartition q s) (p.parts.sort (· ≥ ·)) ∧
      PartitionMajorizes (p.parts.sort (· ≥ ·)) (diagonalMinPartition q s)

/-- **Counting vn-arrangements of a multiset.** Let $t$ be a natural number, let $b_0, b_1, \dots$
be natural numbers, and let $M$ be the multiset of integers containing $b_i$ copies of $i$ for
each $0 \le i \le t$, so that $M$ has $m = b_0 + \dots + b_t$ elements. Then the number of
vn-arrangements of $M$, that is, orderings $(v_1, \dots, v_m)$ of $M$ with $v_{j+1} - v_j \le 1$
for all $j$, is $\prod_{i=0}^{t-1} \binom{b_i + b_{i+1}}{b_i}$.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Proposition 6. -/
public theorem_wanted vnArrangementCount_one_eq_prod (t : ℕ) (b : ℕ → ℕ) :
    vnArrangementCount 1 (∑ i ∈ Finset.range (t + 1), Multiset.replicate (b i) (i : ℤ)) =
      ∏ i ∈ Finset.range t, (b i + b (i + 1)).choose (b i)

/-- **Vn-arrangements of consecutive integers.** For every integer $a$ and every natural number
$t \ge 1$, the set $\{a, a + 1, \dots, a + t - 1\}$ of $t$ consecutive integers has exactly
$2^{t-1}$ vn-arrangements, that is, orderings $(v_1, \dots, v_t)$ of its elements with
$v_{i+1} - v_i \le 1$ for all $i$.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Corollary 5. -/
public theorem_wanted vnArrangementCount_consecutive (a : ℤ) (t : ℕ) (ht : 1 ≤ t) :
    vnArrangementCount 1 (Finset.Ico a (a + t)).val = 2 ^ (t - 1)

/-- **Counting $k$-vn-arrangements of a multiset.** Let $k \le t$ be natural numbers, let
$b_0, b_1, \dots$ be natural numbers, and let $M$ be the multiset of integers containing $b_i$
copies of $i$ for each $0 \le i \le t$, so that $M$ has $m = b_0 + \dots + b_t$ elements. Then
the number of $k$-vn-arrangements of $M$, that is, orderings $(v_1, \dots, v_m)$ of $M$ with
$v_{j+1} - v_j \le k$ for all $j$, is
$$
\binom{b_0 + \dots + b_k}{b_0, \dots, b_k} \prod_{i=1}^{t-k} \binom{b_i + \dots + b_{i+k}}{b_{i+k}}
$$

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Proposition 7. -/
public theorem_wanted vnArrangementCount_eq_multinomial_mul_prod (t k : ℕ) (hk : k ≤ t)
    (b : ℕ → ℕ) :
    vnArrangementCount k (∑ i ∈ Finset.range (t + 1), Multiset.replicate (b i) (i : ℤ)) =
      Nat.multinomial (Finset.range (k + 1)) b *
        ∏ i ∈ Finset.Icc 1 (t - k), (∑ j ∈ Finset.Icc i (i + k), b j).choose (b (i + k))

/-- **Partitions in a diagonal class with as many parts as the initial staircase.** Let $\alpha$
be a partition of $n$ with diagonal sequence $\delta(\alpha) = (d_j)_{j \ge 1}$, set $d_0 = 0$,
and let $q, L \ge 0$ be integers with $d_j = j$ for all $1 \le j \le q$, $d_{q+1} \ne q + 1$,
$d_L \ne 0$ and $d_{L+1} = 0$. Put $b_i = \max(d_i - d_{i+1}, 0)$. Then the number of partitions
of $n$ with exactly $q$ parts whose diagonal sequence equals $\delta(\alpha)$ is
$$\prod_{i=q}^{L-1} \binom{b_i + b_{i+1}}{b_i}.$$

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Proposition 8. -/
public theorem_wanted card_diagonalClass_filter_card_parts_eq_q {n : ℕ} (p : Nat.Partition n)
    (q L : ℕ) (hq : ∀ j ∈ Finset.Icc 1 q, diagonalSequence p.parts j = j)
    (hq' : diagonalSequence p.parts (q + 1) ≠ q + 1) (hL : diagonalSequence p.parts L ≠ 0)
    (hL' : diagonalSequence p.parts (L + 1) = 0) :
    ((diagonalClass p).filter fun β => β.parts.card = q).card =
      ∏ i ∈ Finset.Ico q L,
        ((diagonalSequence p.parts i - diagonalSequence p.parts (i + 1)) +
            (diagonalSequence p.parts (i + 1) - diagonalSequence p.parts (i + 2))).choose
          (diagonalSequence p.parts i - diagonalSequence p.parts (i + 1))

/-- **Partitions in a diagonal class with more parts than the initial staircase.** Let $\alpha$
be a partition of $n$ with diagonal sequence $\delta(\alpha) = (d_j)_{j \ge 1}$, set $d_0 = 0$,
and let $q, L \ge 0$ be integers with $d_j = j$ for all $1 \le j \le q$, $d_{q+1} \ne q + 1$,
$d_L \ne 0$ and $d_{L+1} = 0$. Put $b_i = \max(d_i - d_{i+1}, 0)$. Then for every $k > q$ the
number of partitions of $n$ with exactly $k$ parts whose diagonal sequence equals
$\delta(\alpha)$ is
$$\binom{b_{k-1} + b_k}{b_{k-1} + 1} \prod_{i=q}^{k-2} \binom{b_i + b_{i+1} + 1}{b_i + 1}
\prod_{i=k}^{L-1} \binom{b_i + b_{i+1}}{b_i}.$$

For $k > L$ both sides are $0$.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Proposition 9. -/
public theorem_wanted card_diagonalClass_filter_card_parts_eq_of_lt {n : ℕ}
    (p : Nat.Partition n) (q L k : ℕ)
    (hq : ∀ j ∈ Finset.Icc 1 q, diagonalSequence p.parts j = j)
    (hq' : diagonalSequence p.parts (q + 1) ≠ q + 1) (hL : diagonalSequence p.parts L ≠ 0)
    (hL' : diagonalSequence p.parts (L + 1) = 0) (hk : q < k) :
    ((diagonalClass p).filter fun β => β.parts.card = k).card =
      ((diagonalSequence p.parts (k - 1) - diagonalSequence p.parts k) +
            (diagonalSequence p.parts k - diagonalSequence p.parts (k + 1))).choose
          (diagonalSequence p.parts (k - 1) - diagonalSequence p.parts k + 1) *
        (∏ i ∈ Finset.Ico q (k - 1),
          ((diagonalSequence p.parts i - diagonalSequence p.parts (i + 1)) +
              (diagonalSequence p.parts (i + 1) - diagonalSequence p.parts (i + 2)) + 1).choose
            (diagonalSequence p.parts i - diagonalSequence p.parts (i + 1) + 1)) *
        ∏ i ∈ Finset.Ico k L,
          ((diagonalSequence p.parts i - diagonalSequence p.parts (i + 1)) +
              (diagonalSequence p.parts (i + 1) - diagonalSequence p.parts (i + 2))).choose
            (diagonalSequence p.parts i - diagonalSequence p.parts (i + 1))

/-- **Number of partitions with a given diagonal sequence.** Let $\alpha$ be a partition of $n$
with diagonal sequence $\delta(\alpha) = (d_j)_{j \ge 1}$, set $d_0 = 0$, and let $q, L \ge 0$ be
integers with $d_j = j$ for all $1 \le j \le q$, $d_{q+1} \ne q + 1$, $d_L \ne 0$ and
$d_{L+1} = 0$. Put $b_i = \max(d_i - d_{i+1}, 0)$. Then the number of partitions of $n$ whose
diagonal sequence equals $\delta(\alpha)$ is
$$\prod_{i=q}^{L-1} \binom{b_i + b_{i+1} + 1}{b_i + 1}.$$

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Theorem 1. -/
public theorem_wanted card_diagonalClass_eq_prod_choose {n : ℕ} (p : Nat.Partition n) (q L : ℕ)
    (hq : ∀ j ∈ Finset.Icc 1 q, diagonalSequence p.parts j = j)
    (hq' : diagonalSequence p.parts (q + 1) ≠ q + 1) (hL : diagonalSequence p.parts L ≠ 0)
    (hL' : diagonalSequence p.parts (L + 1) = 0) :
    (diagonalClass p).card =
      ∏ i ∈ Finset.Ico q L,
        ((diagonalSequence p.parts i - diagonalSequence p.parts (i + 1)) +
            (diagonalSequence p.parts (i + 1) - diagonalSequence p.parts (i + 2)) + 1).choose
          (diagonalSequence p.parts i - diagonalSequence p.parts (i + 1) + 1)

/-- **Diagonal classes whose multiplicities are at least two.** Let $q \ge 1$, let
$s = (s_1, s_2, \dots)$ be a sequence of natural numbers, and let $\alpha$ be a partition of $n$
whose diagonal sequence $\delta(\alpha) = (d_i)_{i \ge 1}$ is
$(1, 2, \dots, q, q^{(s_q)}, (q-1)^{(s_{q-1})}, \dots, 1^{(s_1)})$ followed by zeros, where
$v^{(r)}$ means $r$ copies of $v$. Put $L = q + s_1 + \dots + s_q$. If $s_i \ge 2$ for all
$1 \le i < q$, then exactly one partition of $n$ with diagonal sequence $\delta(\alpha)$ has
exactly $q$ parts; if moreover $s_q \ge 1$, then the number of partitions of $n$ with diagonal
sequence $\delta(\alpha)$ is $\prod_{i=q}^{L} (\max(d_i - d_{i+1}, 0) + 1)$.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Corollary 6 (1), (2). -/
public theorem_wanted card_diagonalClass_of_two_le_s {n : ℕ} (p : Nat.Partition n) (q : ℕ)
    (hq : 1 ≤ q) (s : ℕ → ℕ)
    (hd : diagonalSequence p.parts = diagonalOfList (diagonalNormalForm q s))
    (hs : ∀ i ∈ Finset.Ico 1 q, 2 ≤ s i) :
    ((diagonalClass p).filter fun β => β.parts.card = q).card = 1 ∧
      (1 ≤ s q → (diagonalClass p).card =
        ∏ i ∈ Finset.Icc q (q + ∑ j ∈ Finset.Icc 1 q, s j),
          (diagonalSequence p.parts i - diagonalSequence p.parts (i + 1) + 1))

/-- **Every positive integer is the size of a diagonal class.** For every positive integer $m$
there are a natural number $n$ and a partition $\alpha$ of $n$ whose class, the set of partitions
of $n$ with the same diagonal sequence as $\alpha$, has exactly $m$ elements.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Corollary 6 (3). -/
public theorem_wanted exists_card_diagonalClass_eq (m : ℕ) (hm : 0 < m) :
    ∃ (n : ℕ) (p : Nat.Partition n), (diagonalClass p).card = m

/-- **Truncating the staircase of a diagonal sequence.** For $m \ge 0$ and a sequence
$s = (s_1, s_2, \dots)$ of natural numbers, let $d(m, s)$ be the sequence
$(1, 2, \dots, m, m^{(s_m)}, (m-1)^{(s_{m-1})}, \dots, 1^{(s_1)})$ followed by zeros, where
$v^{(r)}$ means $r$ copies of $v$, and let $n(m, s) = m(m+1)/2 + \sum_{j=1}^{m} j s_j$. Let
$1 \le k < q$ with $s_k \ge 2$ and $s_j = 0$ for all $k < j \le q$. Then the number of partitions
of $n(q, s)$ with diagonal sequence $d(q, s)$ equals the number of partitions of $n(k, s)$ with
diagonal sequence $d(k, s)$.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Corollary 6 (4). -/
public theorem_wanted card_diagonalClassOf_truncate (q k : ℕ) (s : ℕ → ℕ) (hk : 1 ≤ k)
    (hkq : k < q) (hsk : 2 ≤ s k) (hs : ∀ j ∈ Finset.Ioc k q, s j = 0) :
    (diagonalClassOf (q * (q + 1) / 2 + ∑ j ∈ Finset.Icc 1 q, j * s j)
        (diagonalOfList (diagonalNormalForm q s))).card =
      (diagonalClassOf (k * (k + 1) / 2 + ∑ j ∈ Finset.Icc 1 k, j * s j)
        (diagonalOfList (diagonalNormalForm k s))).card

/-- **Capping the multiplicities of a diagonal sequence at two.** For $m \ge 0$ and a sequence
$s = (s_1, s_2, \dots)$ of natural numbers, let $d(m, s)$ be the sequence
$(1, 2, \dots, m, m^{(s_m)}, (m-1)^{(s_{m-1})}, \dots, 1^{(s_1)})$ followed by zeros, where
$v^{(r)}$ means $r$ copies of $v$, and let $n(m, s) = m(m+1)/2 + \sum_{j=1}^{m} j s_j$. Let
$q \ge 1$ and $\sigma_j = \min(s_j, 2)$ for all $j$. Then the number of partitions of $n(q, s)$
with diagonal sequence $d(q, s)$ equals the number of partitions of $n(q, \sigma)$ with diagonal
sequence $d(q, \sigma)$.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Corollary 6 (5). -/
public theorem_wanted card_diagonalClassOf_min_two (q : ℕ) (hq : 1 ≤ q) (s : ℕ → ℕ) :
    (diagonalClassOf (q * (q + 1) / 2 + ∑ j ∈ Finset.Icc 1 q, j * s j)
        (diagonalOfList (diagonalNormalForm q s))).card =
      (diagonalClassOf (q * (q + 1) / 2 + ∑ j ∈ Finset.Icc 1 q, j * min (s j) 2)
        (diagonalOfList (diagonalNormalForm q fun j => min (s j) 2))).card

/-- **Diagonal classes of size at most three.** Let $\alpha$ be a partition of $n \ge 1$, let
$d = \delta(\alpha)$ be its diagonal sequence, written without its trailing zeros, and let
$[\alpha]$ be the set of partitions of $n$ with diagonal sequence $d$, each written by its parts
in decreasing order. Here $v^{(r)}$ means $r$ copies of $v$, and a run $a, a - 1, \dots, b$ with
$a < b$ is empty.
(1) If $|[\alpha]| = 1$, then there is $q \ge 1$ with $n = \binom{q+1}{2}$,
$d = (1, 2, \dots, q)$ and $[\alpha] = \{(q, q - 1, \dots, 1)\}$.
(2) If $|[\alpha]| = 2$, then either there are $q \ge 1$ and $k \ge 2$ with
$n = \binom{q+1}{2} + k$, $d = (1, 2, \dots, q, 1^{(k)})$ and
$[\alpha] = \{(q + k, q - 1, \dots, 1), (q, q - 1, \dots, 1, 1^{(k)})\}$, or $n = 2$,
$d = (1, 1)$ and $[\alpha] = \{(2), (1, 1)\}$.
(3) If $|[\alpha]| = 3$, then either there are $q \ge 2$ and $k \ge 2$ with
$n = \binom{q+1}{2} + 2k$, $d = (1, 2, \dots, q, 2^{(k)})$ and $[\alpha] = \{(q + k, q - 1 + k,
q - 2, \dots, 1), (q, q - 1, \dots, 3, 2^{(k+1)}, 1), (q + k, q - 1, \dots, 2, 1^{(k+1)})\}$, or
$d = (1, 2, 1)$ and $[\alpha] = \{(3, 1), (2, 2), (2, 1, 1)\}$, or $d = (1, 2, 2)$ and
$[\alpha] = \{(3, 2), (3, 1, 1), (2, 2, 1)\}$.

Part (4) of the corollary, on classes of size $4$, is false as printed and is not included.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Corollary 7 (1)–(3). -/
public theorem_wanted diagonalClass_classification_card_le_three {n : ℕ} (hn : 0 < n)
    (p : Nat.Partition n) :
    ((diagonalClass p).card = 1 →
      ∃ q, 1 ≤ q ∧ n = (q + 1).choose 2 ∧
        diagonalSequence p.parts = diagonalOfList (List.range' 1 q) ∧
        (diagonalClass p).image (·.parts) = {(((List.range' 1 q).reverse : List ℕ) : Multiset ℕ)}) ∧
    ((diagonalClass p).card = 2 →
      (∃ q k, 1 ≤ q ∧ 2 ≤ k ∧ n = (q + 1).choose 2 + k ∧
        diagonalSequence p.parts = diagonalOfList (List.range' 1 q ++ List.replicate k 1) ∧
        (diagonalClass p).image (·.parts) =
          {(((q + k) :: (List.range' 1 (q - 1)).reverse : List ℕ) : Multiset ℕ),
            (((List.range' 1 q).reverse ++ List.replicate k 1 : List ℕ) : Multiset ℕ)}) ∨
      (n = 2 ∧ diagonalSequence p.parts = diagonalOfList [1, 1] ∧
        (diagonalClass p).image (·.parts) = {{2}, {1, 1}})) ∧
    ((diagonalClass p).card = 3 →
      (∃ q k, 2 ≤ q ∧ 2 ≤ k ∧ n = (q + 1).choose 2 + 2 * k ∧
        diagonalSequence p.parts = diagonalOfList (List.range' 1 q ++ List.replicate k 2) ∧
        (diagonalClass p).image (·.parts) =
          {(([q + k, q - 1 + k] ++ (List.range' 1 (q - 2)).reverse : List ℕ) : Multiset ℕ),
            (((List.range' 3 (q - 2)).reverse ++ List.replicate (k + 1) 2 ++ [1] : List ℕ) :
              Multiset ℕ),
            (((q + k) :: ((List.range' 2 (q - 2)).reverse ++ List.replicate (k + 1) 1) :
              List ℕ) : Multiset ℕ)}) ∨
      (diagonalSequence p.parts = diagonalOfList [1, 2, 1] ∧
        (diagonalClass p).image (·.parts) = {{3, 1}, {2, 2}, {2, 1, 1}}) ∨
      (diagonalSequence p.parts = diagonalOfList [1, 2, 2] ∧
        (diagonalClass p).image (·.parts) = {{3, 2}, {3, 1, 1}, {2, 2, 1}}))

end

end MetaMathlibExt
