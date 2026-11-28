/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.Set.Card
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Interval.Finset.Basic
import Mathlib.Combinatorics.Enumerative.Partition.YoungDiagram
import Mathlib.Data.Finset.NatAntidiagonal

/-!
# Diagonal sequences of integer partitions

Definitions and results from Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer
Partitions*, INTEGERS 25 (2025), Article A60 (arXiv:2412.06856).

For a partition `α = (α₁ ≥ α₂ ≥ ⋯ ≥ α_t)` the diagonal sequence is `δ(α) = (d_k)_{k ≥ 1}` with
`d_k = |{i | 1 ≤ i ≤ k, α_i + i - 1 ≥ k}|`, the number of cells of the Young diagram on the
`k`-th upper-right to lower-left diagonal. Partitions are `Nat.Partition n`; a diagonal sequence
is a function `ℕ → ℕ` with the paper's indexing `d_1, d_2, …` and the value `0` at index `0`.
`[d]` is the set of partitions with diagonal sequence `d`. The definitions follow the arXiv
version of the paper (Definition (1.1), Proposition 2.3, Section 4).

To realize a class of size `k + 1`, take the staircase with row lengths `k, …, 1` and
add one cell on the next diagonal. The full inner diagonals determine the staircase,
and each of the `k + 1` positions for the extra cell gives a distinct partition.

## References

* Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*, INTEGERS 25
  (2025), Article A60, pp. 1–17. Section 1 (diagonal sequences and classes), Corollary 1 and
  Propositions 1–2 (normal form and extremal partitions), and Corollary 6 (3) (class sizes).
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

/-- **Membership in a diagonal class.** For partitions $p$ and $\beta$ of the same natural
number $n$, $\beta \in [\delta(p)]$ if and only if $\delta(\beta) = \delta(p)$. -/
theorem mem_diagonalClass_iff {n : ℕ} {p β : Nat.Partition n} :
    β ∈ diagonalClass p ↔ diagonalSequence β.parts = diagonalSequence p.parts := by
  simp [diagonalClass]

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

end

/-! ## Conjugating the maximal partition -/

namespace conjugateParts_diagonalMaxPartition

private theorem sup_cons_map_add (rows : Multiset ℕ) (d : ℕ) :
    (d ::ₘ rows.map (d + ·)).sup = d + rows.sup := by
  induction rows using Multiset.induction_on with
  | empty => simp
  | cons a rows ih =>
    rw [Multiset.map_cons, Multiset.cons_swap d, Multiset.sup_cons, ih, Multiset.sup_cons]
    omega

-- The first d columns meet every row. Later columns have their original heights.
private theorem conjugateParts_cons_map_add (rows : Multiset ℕ) (d : ℕ) :
    conjugateParts (d ::ₘ rows.map (d + ·)) =
      Multiset.replicate d (rows.card + 1) + conjugateParts rows := by
  rw [conjugateParts, sup_cons_map_add, Multiset.range_add, Multiset.map_add, Multiset.map_map]
  apply congrArg₂ (· + ·)
  · calc
      _ = (Multiset.range d).map (fun _ => rows.card + 1) := by
        apply Multiset.map_congr rfl
        intro j hj
        have hjd := Multiset.mem_range.mp hj
        simp [Multiset.countP_cons_of_pos _ hjd, Multiset.countP_map,
          show ∀ a : ℕ, j < d + a from fun a => by omega]
      _ = _ := by simp
  · apply Multiset.map_congr rfl
    intro j _
    simpa [Multiset.countP_cons, Multiset.countP_map] using
      (Multiset.countP_eq_card_filter (j < ·) rows).symm

private theorem diagonalMaxPartition_succ (q : ℕ) (s : ℕ → ℕ) :
    (↑(diagonalMaxPartition (q + 1) s) : Multiset ℕ) =
      (s (q + 1) + 1) ::ₘ (↑(diagonalMaxPartition q s) : Multiset ℕ).map (s (q + 1) + 1 + ·) := by
  simp only [diagonalMaxPartition, ← Multiset.map_coe, Multiset.coe_range, Multiset.range_succ,
    Multiset.map_cons, Multiset.map_map, Finset.Icc_self, Finset.sum_singleton]
  congr 1
  · omega
  · apply Multiset.map_congr rfl
    intro j hj
    have hjq := Multiset.mem_range.mp hj
    rw [Finset.sum_Icc_succ_top (by omega : j + 1 ≤ q + 1)]
    dsimp
    omega

end conjugateParts_diagonalMaxPartition

open conjugateParts_diagonalMaxPartition in
/-- **Conjugate of a partition with prescribed gaps between its parts.** Let $q \ge 0$ and let
$s_1, \dots, s_q$ be natural numbers. The conjugate of the partition $\bar\alpha$ with parts
$\bar\alpha_i = q - i + 1 + \sum_{k=i}^{q} s_k$ for $1 \le i \le q$ is the partition
$\underline{\alpha} = (q^{(s_q + 1)}, (q-1)^{(s_{q-1} + 1)}, \dots, 1^{(s_1 + 1)})$, where
$v^{(r)}$ means $r$ copies of $v$; the parts are compared as multisets.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Proposition 2. -/
public theorem conjugateParts_diagonalMaxPartition (q : ℕ) (s : ℕ → ℕ) :
    conjugateParts ↑(diagonalMaxPartition q s) = ↑(diagonalMinPartition q s) := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [diagonalMaxPartition_succ, conjugateParts_cons_map_add, ih]
    simp [diagonalMinPartition, List.range_succ, diagonalMaxPartition, ← Multiset.coe_add,
      Multiset.coe_replicate]

/-! ## A diagonal class of prescribed size -/

open Finset YoungDiagram

private theorem countP_parts_eq_colLen {n : ℕ} (p : Nat.Partition n) (j : ℕ) :
    p.parts.countP (j + 1 ≤ ·) = (ofPartition p).colLen j := by
  let μ := ofPartition p
  have hparts : p.parts = (μ.rowLens : Multiset ℕ) := by simp [μ]
  rw [hparts, rowLens, ← Multiset.map_coe, Multiset.countP_map]
  change ((range (μ.colLen 0)).filter fun i => j + 1 ≤ μ.rowLen i).card = μ.colLen j
  suffices ((range (μ.colLen 0)).filter fun i => j + 1 ≤ μ.rowLen i) = range (μ.colLen j) by
    rw [this, card_range]
  ext i
  simp only [mem_filter, mem_range, Nat.succ_le_iff, ← mem_iff_lt_rowLen, ← mem_iff_lt_colLen]
  exact ⟨And.right, fun h => ⟨μ.up_left_mem le_rfl (Nat.zero_le _) h, h⟩⟩

private theorem diagonalSequence_succ_eq_card {n : ℕ} (p : Nat.Partition n) (k : ℕ) :
    diagonalSequence p.parts (k + 1) =
      ((antidiagonal k).filter fun c => c ∈ ofPartition p).card := by
  have hrows : Icc 1 (k + 1) = (range (k + 1)).map (addRightEmbedding 1) := by
    simp [Nat.range_succ_eq_Icc_zero]
  rw [diagonalSequence, hrows, Finset.Nat.antidiagonal_eq_map]
  simp only [filter_map, card_map]
  apply congrArg card (filter_congr _)
  intro i hi
  have hik := mem_range.mp hi
  change i + 1 ≤ p.parts.countP (k + 1 + 1 - (i + 1) ≤ ·) ↔ (i, k - i) ∈ ofPartition p
  rw [show k + 1 + 1 - (i + 1) = (k - i) + 1 by omega, countP_parts_eq_colLen,
    mem_iff_lt_colLen, Nat.succ_le_iff]

private def staircaseCells (k : ℕ) : Finset (ℕ × ℕ) :=
  ((range k) ×ˢ (range k)).filter fun c => c.1 + c.2 < k

private theorem mem_staircaseCells {k : ℕ} {c : ℕ × ℕ} :
    c ∈ staircaseCells k ↔ c.1 + c.2 < k := by
  simp only [staircaseCells, mem_filter, mem_product, mem_range]
  omega

/-- A staircase with one additional cell on the next diagonal. -/
private def staircaseWithCell {k : ℕ} (c : ℕ × ℕ) (hc : c ∈ antidiagonal k) : YoungDiagram where
  cells := insert c (staircaseCells k)
  isLowerSet := by
    intro b a hab hb
    simp only [mem_coe, mem_insert, mem_staircaseCells] at hb ⊢
    have h₁ := hab.1
    have h₂ := hab.2
    rcases hb with rfl | hb
    · have := mem_antidiagonal.mp hc
      rw [Prod.ext_iff]
      omega
    · exact Or.inr (by omega)

private theorem mem_staircaseWithCell {k : ℕ} {a c : ℕ × ℕ} (hc : c ∈ antidiagonal k) :
    a ∈ staircaseWithCell c hc ↔ a = c ∨ a.1 + a.2 < k :=
  mem_insert.trans (or_congr Iff.rfl mem_staircaseCells)

private theorem card_staircaseWithCell {k : ℕ} {c : ℕ × ℕ} (hc : c ∈ antidiagonal k) :
    (staircaseWithCell c hc).card = (staircaseCells k).card + 1 := by
  apply card_insert_of_notMem
  exact fun h => (mem_staircaseCells.mp h).ne (mem_antidiagonal.mp hc)

private def staircasePartition {k : ℕ} (c : ℕ × ℕ) (hc : c ∈ antidiagonal k) :
    Nat.Partition ((staircaseCells k).card + 1) :=
  (staircaseWithCell c hc).toPartition (card_staircaseWithCell hc)

private theorem diagonalSequence_staircasePartition {k : ℕ} {c : ℕ × ℕ}
    (hc : c ∈ antidiagonal k) (j : ℕ) :
    diagonalSequence (staircasePartition c hc).parts (j + 1) =
      if j < k then j + 1 else if j = k then 1 else 0 := by
  rw [diagonalSequence_succ_eq_card, staircasePartition, ofPartition_toPartition]
  have hsum := mem_antidiagonal.mp hc
  by_cases hj : j < k
  · rw [ite_eq_left hj, filter_eq_self.mpr, Finset.Nat.card_antidiagonal]
    intro a ha
    exact mem_insert_of_mem (mem_staircaseCells.mpr ((mem_antidiagonal.mp ha).trans_lt hj))
  rw [ite_eq_right hj]
  by_cases heq : j = k
  · subst j
    rw [ite_eq_left rfl]
    refine card_eq_one.mpr ⟨c, Finset.ext fun a => ?_⟩
    rw [mem_filter, mem_antidiagonal, mem_staircaseWithCell, mem_singleton]
    grind
  · rw [ite_eq_right heq, card_eq_zero, filter_eq_empty_iff]
    intro a ha
    rw [mem_staircaseWithCell]
    have := mem_antidiagonal.mp ha
    grind

private theorem card_diagonalClass_staircasePartition {k : ℕ} {c : ℕ × ℕ}
    (hc : c ∈ antidiagonal k) : (diagonalClass (staircasePartition c hc)).card = k + 1 := by
  classical
  rw [← Finset.Nat.card_antidiagonal k]
  symm
  apply card_bij (staircasePartition (k := k))
  · intro a ha
    apply mem_filter.mpr
    refine ⟨mem_univ _, funext fun j => ?_⟩
    cases j with
    | zero => simp [diagonalSequence]
    | succ j => rw [diagonalSequence_staircasePartition, diagonalSequence_staircasePartition]
  · intro a ha b hb heq
    have hshape := congrArg ofPartition heq
    simp only [staircasePartition, ofPartition_toPartition] at hshape
    have hmem : a ∈ staircaseWithCell b hb := hshape ▸ (mem_staircaseWithCell ha).mpr (Or.inl rfl)
    exact ((mem_staircaseWithCell hb).mp hmem).resolve_right (by
      rw [mem_antidiagonal.mp ha]
      exact lt_irrefl k)
  · intro p hp
    have hd := (mem_filter.mp hp).2
    have hcounts (j : ℕ) :
        ((antidiagonal j).filter fun a => a ∈ ofPartition p).card =
          if j < k then j + 1 else if j = k then 1 else 0 := by
      rw [← diagonalSequence_succ_eq_card, congrFun hd, diagonalSequence_staircasePartition]
    have hlast : ((antidiagonal k).filter fun a => a ∈ ofPartition p).Nonempty :=
      card_pos.mp (by simp [hcounts])
    obtain ⟨a, ha⟩ := hlast
    obtain ⟨ha, hap⟩ := mem_filter.mp ha
    refine ⟨a, ha, ?_⟩
    -- Each inner diagonal is full, so the diagram contains the whole staircase.
    have hbase : staircaseCells k ⊆ (ofPartition p).cells := by
      intro b hb
      let j := b.1 + b.2
      have hj : j < k := mem_staircaseCells.mp hb
      have hfull := (hcounts j).trans (ite_eq_left hj)
      rw [← Finset.Nat.card_antidiagonal j] at hfull
      exact filter_card_eq hfull b (mem_antidiagonal.mpr rfl)
    have heq : staircaseWithCell a ha = ofPartition p := by
      apply YoungDiagram.ext
      apply eq_of_subset_of_card_le (insert_subset hap hbase)
      exact le_of_eq ((card_ofPartition p).trans (card_staircaseWithCell ha).symm)
    simp [staircasePartition, heq]

/-- **Every positive integer is the size of a diagonal class.** For every positive integer $m$
there are a natural number $n$ and a partition $\alpha$ of $n$ whose class, the set of partitions
of $n$ with the same diagonal sequence as $\alpha$, has exactly $m$ elements.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Corollary 6 (3). -/
public theorem exists_card_diagonalClass_eq (m : ℕ) (hm : 0 < m) :
    ∃ (n : ℕ) (p : Nat.Partition n), (diagonalClass p).card = m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  have hc : (k, 0) ∈ antidiagonal k := mem_antidiagonal.mpr (Nat.add_zero k)
  exact ⟨_, _, card_diagonalClass_staircasePartition hc⟩

end MetaMathlibExt
