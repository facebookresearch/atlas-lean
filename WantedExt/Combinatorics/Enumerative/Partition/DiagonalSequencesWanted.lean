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

/-- The diagonal sequence `δ(α) = (d_k)` of the partition with parts multiset `s`: `d_k` counts
the rows `1 ≤ i ≤ k` whose part satisfies `α_i + i - 1 ≥ k`. Since `α_i ≥ m` iff at least `i`
parts are at least `m`, `d_k` is the number of `i ∈ [1, k]` with at least `i` parts `≥ k + 1 - i`;
`d_0 = 0`.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Section 1, Definition of the diagonal sequence (1.1). -/
def diagonalSequence (s : Multiset ℕ) (k : ℕ) : ℕ :=
  ((Finset.Icc 1 k).filter fun i => i ≤ s.countP (k + 1 - i ≤ ·)).card

/-- The paper's running example: `δ((7,7,4,1,1,1)) = (1,2,3,4,4,4,2,1)`.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Section 1 (example after the definition); characteristic check
of `diagonalSequence`. -/
theorem diagonalSequence_seven_seven_four_one_one_one :
    (List.range 10).map (diagonalSequence {7, 7, 4, 1, 1, 1}) = [0, 1, 2, 3, 4, 4, 4, 2, 1, 0] := by
  decide +kernel

/-- The sequence `d_1, d_2, …, d_ℓ, 0, 0, …` given by a finite list `[d_1, …, d_ℓ]`, with value
`0` at index `0` (the indexing of `diagonalSequence`).

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Section 1 (trailing zeroes of `δ(α)` are omitted). -/
def diagonalOfList (l : List ℕ) (k : ℕ) : ℕ :=
  (0 :: l).getD k 0

/-- `diagonalOfList [1, 2, 1]` is `0, 1, 2, 1, 0, …`.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Section 1; characteristic check of `diagonalOfList`. -/
theorem diagonalOfList_one_two_one :
    (List.range 6).map (diagonalOfList [1, 2, 1]) = [0, 1, 2, 1, 0, 0] := by
  decide

/-- The normal form `(1, 2, …, q - 1, q, q^{(s_q)}, (q-1)^{(s_{q-1})}, …, 1^{(s_1)})` of a
diagonal sequence, as a list: `1, …, q` followed by `s_v` copies of `v` for `v = q, q-1, …, 1`.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Corollary 1, display (2.1). -/
def diagonalNormalForm (q : ℕ) (s : ℕ → ℕ) : List ℕ :=
  List.range' 1 q ++ (List.range q).reverse.flatMap fun j => List.replicate (s (j + 1)) (j + 1)

/-- With `q = 4`, `s_4 = 2`, `s_3 = 0`, `s_2 = 1`, `s_1 = 1` the normal form is
`(1,2,3,4,4,4,2,1)`.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Section 2 (example after Corollary 4); characteristic check of
`diagonalNormalForm`. -/
theorem diagonalNormalForm_four_example :
    diagonalNormalForm 4 (fun k => [0, 1, 1, 0, 2].getD k 0) = [1, 2, 3, 4, 4, 4, 2, 1] := by
  decide

/-- The partition `ᾱ = (ᾱ_1, …, ᾱ_q)` with `ᾱ_i = q - i + 1 + ∑_{k=i}^q s_k`, as the list of its
parts in decreasing order (entry `j` is `ᾱ_{j+1}`).

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Proposition 1. -/
def diagonalMaxPartition (q : ℕ) (s : ℕ → ℕ) : List ℕ :=
  (List.range q).map fun j => q - j + ∑ k ∈ Finset.Icc (j + 1) q, s k

/-- For `q = 4`, `s_4 = 2`, `s_3 = 0`, `s_2 = 1`, `s_1 = 1`, `ᾱ = (8, 6, 4, 3)`.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Section 2 (example after Corollary 4); characteristic check of
`diagonalMaxPartition`. -/
theorem diagonalMaxPartition_four_example :
    diagonalMaxPartition 4 (fun k => [0, 1, 1, 0, 2].getD k 0) = [8, 6, 4, 3] := by
  decide

/-- The partition `α̲ = (q^{(s_q + 1)}, (q-1)^{(s_{q-1} + 1)}, …, 1^{(s_1 + 1)})`, as the list of
its parts in decreasing order.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Proposition 2. -/
def diagonalMinPartition (q : ℕ) (s : ℕ → ℕ) : List ℕ :=
  (List.range q).reverse.flatMap fun j => List.replicate (s (j + 1) + 1) (j + 1)

/-- For `q = 4`, `s_4 = 2`, `s_3 = 0`, `s_2 = 1`, `s_1 = 1`, `α̲ = (4,4,4,3,2,2,1,1)`.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Section 2 (example after Corollary 4); characteristic check of
`diagonalMinPartition`. -/
theorem diagonalMinPartition_four_example :
    diagonalMinPartition 4 (fun k => [0, 1, 1, 0, 2].getD k 0) = [4, 4, 4, 3, 2, 2, 1, 1] := by
  decide

/-- The parts of the conjugate partition `α*`: for `0 ≤ j < max α`, the number of parts `> j`.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Section 1 (conjugate partition `α*`). -/
def conjugateParts (s : Multiset ℕ) : Multiset ℕ :=
  (Multiset.range s.sup).map fun j => s.countP (j < ·)

/-- The conjugate of `(3, 1)` is `(2, 1, 1)`.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Section 1; characteristic check of `conjugateParts`. -/
theorem conjugateParts_three_one : conjugateParts {3, 1} = {2, 1, 1} := by
  decide

/-- The equivalence class `[d] = δ⁻¹(δ(p)) ⊆ P(n)` of a partition `p`.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Section 1 (definition of `[d]`). -/
noncomputable def diagonalClass {n : ℕ} (p : Nat.Partition n) : Finset (Nat.Partition n) :=
  open Classical in Finset.univ.filter fun β => diagonalSequence β.parts = diagonalSequence p.parts

/-- Every partition lies in its own class.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Section 1 (definition of `[d]`); characteristic check of
`diagonalClass`. -/
theorem mem_diagonalClass_self {n : ℕ} (p : Nat.Partition n) : p ∈ diagonalClass p := by
  simp [diagonalClass]

/-- The partitions of `n` whose diagonal sequence is a given sequence `d`.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Section 1 (definition of `[d]` for `d ∈ Δ(n)`). -/
noncomputable def diagonalClassOf (n : ℕ) (d : ℕ → ℕ) : Finset (Nat.Partition n) :=
  open Classical in Finset.univ.filter fun β => diagonalSequence β.parts = d

/-- A partition `β` lies in the class of its own diagonal sequence.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Section 1 (definition of `[d]`); characteristic check of
`diagonalClassOf`. -/
theorem mem_diagonalClassOf_diagonalSequence {n : ℕ} (β : Nat.Partition n) :
    β ∈ diagonalClassOf n (diagonalSequence β.parts) := by
  simp [diagonalClassOf]

/-- The paper's majorization: `α ≻ β` iff `∑_{i ≤ k} α_i ≥ ∑_{i ≤ k} β_i` for all
`1 ≤ k ≤ min {s, t}`, for part lists in decreasing order.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Section 3 (definition of majorization). -/
def PartitionMajorizes (a b : List ℕ) : Prop :=
  ∀ k ≤ min a.length b.length, (b.take k).sum ≤ (a.take k).sum

/-- `(3, 1)` majorizes `(2, 2)`.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Section 3; characteristic check of `PartitionMajorizes`. -/
theorem partitionMajorizes_three_one_two_two : PartitionMajorizes [3, 1] [2, 2] := by
  unfold PartitionMajorizes
  decide

/-- The number of `k`-vn-arrangements of a finite multiset `M` of integers: orderings
`(v_1, …, v_b)` of `M` with `v_{i+1} - v_i ≤ k` for all `i`. For `k = 1` these are the
vn-arrangements.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Section 4 (definitions of vn-arrangement and
k-vn-arrangement). -/
noncomputable def vnArrangementCount (k : ℕ) (M : Multiset ℤ) : ℕ :=
  Set.ncard {l : List ℤ | (l : Multiset ℤ) = M ∧ l.IsChain fun a b => b - a ≤ (k : ℤ)}

/-- A one-element multiset has exactly one k-vn-arrangement.

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

/-- Lemma 1: `d_{k+1} - d_k ≤ 1`, with equality iff `d_j = j` for all `1 ≤ j ≤ k + 1`; and if
`d_k ≥ d_{k+1}` then `d_{k+1} ≥ d_{k+2}`. Stated for every `k`, including `k = 0` (`d_0 = 0`).

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Lemma 1. -/
public theorem_wanted diagonalSequence_succ_le_and_antitone {n : ℕ} (p : Nat.Partition n)
    (k : ℕ) :
    (diagonalSequence p.parts (k + 1) ≤ diagonalSequence p.parts k + 1 ∧
      (diagonalSequence p.parts (k + 1) = diagonalSequence p.parts k + 1 ↔
        ∀ j ∈ Finset.Icc 1 (k + 1), diagonalSequence p.parts j = j)) ∧
    (diagonalSequence p.parts (k + 1) ≤ diagonalSequence p.parts k →
      diagonalSequence p.parts (k + 2) ≤ diagonalSequence p.parts (k + 1))

/-- Corollary 1: for every partition `α` of `n ≥ 1` there are unique `q > 0` and
`s_1, …, s_q ≥ 0` with `δ(α) = (1, …, q, q^{(s_q)}, …, 1^{(s_1)})`, and then
`q(q+1)/2 + ∑ k s_k = n`. Uniqueness of `s` is on the indices `1, …, q`.

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

/-- Proposition 1: for `q > 0` and `s_1, …, s_q ≥ 0` with `q(q+1)/2 + ∑ k s_k = n`, the list
`ᾱ_i = q - i + 1 + ∑_{k=i}^q s_k` is a partition of `n` (positive parts summing to `n`) with
strictly decreasing parts, its diagonal sequence is `(1, …, q, q^{(s_q)}, …, 1^{(s_1)})`, and
`s_i = ᾱ_i - ᾱ_{i+1} - 1` for `1 ≤ i < q`, `s_q = ᾱ_q - 1`.

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

/-- Corollary 2: the number of diagonal sequences of partitions of `n`, `|Δ(n)|`, equals the
number of partitions of `n` into distinct parts, which equals the number of partitions of `n`
into odd parts. Stated for every `n`, including `n = 0`.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Corollary 2. -/
public theorem_wanted ncard_diagonalSequences_eq_card_distincts (n : ℕ) :
    (Set.range fun p : Nat.Partition n => diagonalSequence p.parts).ncard =
        (Nat.Partition.distincts n).card ∧
      (Nat.Partition.distincts n).card = (Nat.Partition.odds n).card

/-- Proposition 2: the conjugate of `ᾱ` is `α̲ = (q^{(s_q + 1)}, …, 1^{(s_1 + 1)})`. The
paper's hypothesis (a partition `α` with this normal form) only fixes `q` and `s` and is
omitted.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Proposition 2. -/
public theorem_wanted conjugateParts_diagonalMaxPartition (q : ℕ) (s : ℕ → ℕ) :
    conjugateParts ↑(diagonalMaxPartition q s) = ↑(diagonalMinPartition q s)

/-- Corollary 3: `δ(ᾱ) = δ(α̲)`, and the multiset of the (nonzero) entries of this diagonal
sequence, which is the normal form list, equals the multiset of parts of `α̲`.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Corollary 3. -/
public theorem_wanted diagonalSequence_max_eq_min_and_multiset (q : ℕ) (s : ℕ → ℕ) :
    diagonalSequence ↑(diagonalMaxPartition q s) =
        diagonalSequence ↑(diagonalMinPartition q s) ∧
      diagonalSequence ↑(diagonalMinPartition q s) = diagonalOfList (diagonalNormalForm q s) ∧
      (↑(diagonalNormalForm q s) : Multiset ℕ) = ↑(diagonalMinPartition q s)

/-- Corollary 4: let `α = (α_1, …, α_t)` have normal form `(q, s)`. If `α ≠ ᾱ` then
`α_i = α_{i+1}` for some `1 ≤ i < t`; if `α ≠ α̲` then `α_i - α_{i+1} > 1` for some
`1 ≤ i ≤ t` (with `α_{t+1} = 0`). Parts are listed in decreasing order, zero-based.

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

/-- Proposition 3: if `δ(α) = (1, …, q, q^{(s_q)}, …, 1^{(s_1)})` then the largest part `α_1`
lies in `A_1 = {q, q + s_q, q + s_q + s_{q-1}, …, q + ∑_{i=1}^q s_i}`. The paper's equivalent
rephrasing (`α ∈ P(n,k)*` for some `k ∈ A_1`) is the same statement.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Proposition 3. -/
public theorem_wanted sup_parts_mem_diagonalFirstPartSet {n : ℕ} (p : Nat.Partition n) (q : ℕ)
    (s : ℕ → ℕ) (hd : diagonalSequence p.parts = diagonalOfList (diagonalNormalForm q s)) :
    p.parts.sup ∈ (Finset.Icc 1 (q + 1)).image fun j => q + ∑ i ∈ Finset.Icc j q, s i

/-- Proposition 4: `s(α) + s(α*) = 2 ∑_k k d_k`, where `s(α)` is the sum of the squares of the
parts; consequently partitions with the same diagonal sequence have the same `s(α) + s(α*)`.
The paper sums to `r = t + α_1 - 1`; here the sum runs to `2n`, which adds only zero terms.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Proposition 4. -/
public theorem_wanted sum_sq_add_sum_sq_conjugate_eq {n : ℕ} (p : Nat.Partition n) :
    (p.parts.map (· ^ 2)).sum + ((conjugateParts p.parts).map (· ^ 2)).sum =
        2 * ∑ k ∈ Finset.Icc 1 (2 * n), k * diagonalSequence p.parts k ∧
      ∀ β : Nat.Partition n, diagonalSequence β.parts = diagonalSequence p.parts →
        (β.parts.map (· ^ 2)).sum + ((conjugateParts β.parts).map (· ^ 2)).sum =
          (p.parts.map (· ^ 2)).sum + ((conjugateParts p.parts).map (· ^ 2)).sum

/-- Conjugation reverses majorization (quoted from Marshall–Olkin–Arnold, Theorem 7.B.5): for
`α, β ∈ P(n)`, `α ≻ β` if and only if `β* ≻ α*`, in the paper's majorization order on
decreasing part lists.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, proof of Proposition 5 (citing [4], Theorem 7.B.5). -/
public theorem_wanted partitionMajorizes_iff_conjugate {n : ℕ} (α β : Nat.Partition n) :
    PartitionMajorizes (α.parts.sort (· ≥ ·)) (β.parts.sort (· ≥ ·)) ↔
      PartitionMajorizes ((conjugateParts β.parts).sort (· ≥ ·))
        ((conjugateParts α.parts).sort (· ≥ ·))

/-- Proposition 5: every `α ∈ [d]` satisfies `ᾱ ≻ α ≻ α̲` in the paper's majorization order.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Proposition 5. -/
public theorem_wanted diagonalMaxPartition_majorizes_majorizes_min {n : ℕ}
    (p : Nat.Partition n) (q : ℕ) (s : ℕ → ℕ)
    (hd : diagonalSequence p.parts = diagonalOfList (diagonalNormalForm q s)) :
    PartitionMajorizes (diagonalMaxPartition q s) (p.parts.sort (· ≥ ·)) ∧
      PartitionMajorizes (p.parts.sort (· ≥ ·)) (diagonalMinPartition q s)

/-- Proposition 6: the multiset `M = {0^{(b_0)}, 1^{(b_1)}, …, t^{(b_t)}}` has
`∏_{i=0}^{t-1} C(b_i + b_{i+1}, b_i)` vn-arrangements.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Proposition 6. -/
public theorem_wanted vnArrangementCount_one_eq_prod (t : ℕ) (b : ℕ → ℕ) :
    vnArrangementCount 1 (∑ i ∈ Finset.range (t + 1), Multiset.replicate (b i) (i : ℤ)) =
      ∏ i ∈ Finset.range t, (b i + b (i + 1)).choose (b i)

/-- Corollary 5: a set of `t ≥ 1` consecutive integers has `2^{t-1}` vn-arrangements.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Corollary 5. -/
public theorem_wanted vnArrangementCount_consecutive (a : ℤ) (t : ℕ) (ht : 1 ≤ t) :
    vnArrangementCount 1 (Finset.Ico a (a + t)).val = 2 ^ (t - 1)

/-- Proposition 7: for `0 ≤ k ≤ t` the multiset `M = {0^{(b_0)}, …, t^{(b_t)}}` has
`multinomial(b_0, …, b_k) · ∏_{i=1}^{t-k} C(b_i + ⋯ + b_{i+k}, b_{i+k})` k-vn-arrangements.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Proposition 7. -/
public theorem_wanted vnArrangementCount_eq_multinomial_mul_prod (t k : ℕ) (hk : k ≤ t)
    (b : ℕ → ℕ) :
    vnArrangementCount k (∑ i ∈ Finset.range (t + 1), Multiset.replicate (b i) (i : ℤ)) =
      Nat.multinomial (Finset.range (k + 1)) b *
        ∏ i ∈ Finset.Icc 1 (t - k), (∑ j ∈ Finset.Icc i (i + k), b j).choose (b (i + k))

/-- Proposition 8: write `δ(α) = (1, 2, …, q, d_{q+1}, …, d_L)` (`q` maximal with `d_j = j` for
`j ≤ q`, `d_L` the last nonzero entry) and `b_i = d_i - d_{i+1}` (so `b_L = d_L`). The number of
partitions in `[d]` with exactly `q` parts is `∏_{i=q}^{L-1} C(b_i + b_{i+1}, b_i)`.

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

/-- Proposition 9: with `q`, `L`, `b_i` as in Proposition 8 and `k > q`, the number of
partitions in `[d]` with exactly `k` parts is
`C(b_{k-1} + b_k, b_{k-1} + 1) ∏_{i=q}^{k-2} C(b_i + b_{i+1} + 1, b_i + 1)
∏_{i=k}^{L-1} C(b_i + b_{i+1}, b_i)`. Stated for every `k > q` (for `k > L` both sides vanish,
with `b_i = 0` for `i > L`). The record's follow-up remark (`[d]_k ≠ ∅` iff `k ∈ A_1`) is not
included.

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

/-- Theorem 1 (main theorem): with `q`, `L`, `b_i` as in Proposition 8, the number of partitions
with diagonal sequence `d = δ(α)` is `|[d]| = ∏_{i=q}^{L-1} C(b_i + b_{i+1} + 1, b_i + 1)`.

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

/-- Corollary 6, parts 1 and 2: let `δ(α) = (1, …, q, q^{(s_q)}, …, 1^{(s_1)})` with `q ≥ 1`,
`L = q + ∑ s_i` and `b_i = d_i - d_{i+1}`. If `s_i ≥ 2` for all `1 ≤ i < q` then exactly one
partition of `[d]` has `q` parts; if moreover `s_q ≥ 1` then `|[d]| = ∏_{i=q}^{L} (b_i + 1)`.

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

/-- Corollary 6, part 3: every positive integer `m` is the size `|[d]|` of the class of some
partition.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Corollary 6 (3). -/
public theorem_wanted exists_card_diagonalClass_eq (m : ℕ) (hm : 0 < m) :
    ∃ (n : ℕ) (p : Nat.Partition n), (diagonalClass p).card = m

/-- Corollary 6, part 4: if `d = (1, …, q, k^{(s_k)}, …, 1^{(s_1)})` (normal form with
`s_j = 0` for `k < j ≤ q`) with `1 ≤ k < q` and `s_k ≥ 2`, and
`d' = (1, …, k, k^{(s_k)}, …, 1^{(s_1)})`, then `|[d]| = |[d']|`; the classes live in `P(n)` and
`P(n')` with `n = q(q+1)/2 + ∑_{j ≤ q} j s_j`, `n' = k(k+1)/2 + ∑_{j ≤ k} j s_j`.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Corollary 6 (4). -/
public theorem_wanted card_diagonalClassOf_truncate (q k : ℕ) (s : ℕ → ℕ) (hk : 1 ≤ k)
    (hkq : k < q) (hsk : 2 ≤ s k) (hs : ∀ j ∈ Finset.Ioc k q, s j = 0) :
    (diagonalClassOf (q * (q + 1) / 2 + ∑ j ∈ Finset.Icc 1 q, j * s j)
        (diagonalOfList (diagonalNormalForm q s))).card =
      (diagonalClassOf (k * (k + 1) / 2 + ∑ j ∈ Finset.Icc 1 k, j * s j)
        (diagonalOfList (diagonalNormalForm k s))).card

/-- Corollary 6, part 5: replacing every `s_i` by `σ_i = min {s_i, 2}` does not change the
class size: `|[d]| = |[d']|` for `d = (1, …, q, q^{(s_q)}, …, 1^{(s_1)})` and
`d' = (1, …, q, q^{(σ_q)}, …, 1^{(σ_1)})`, `q ≥ 1`.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Corollary 6 (5). -/
public theorem_wanted card_diagonalClassOf_min_two (q : ℕ) (hq : 1 ≤ q) (s : ℕ → ℕ) :
    (diagonalClassOf (q * (q + 1) / 2 + ∑ j ∈ Finset.Icc 1 q, j * s j)
        (diagonalOfList (diagonalNormalForm q s))).card =
      (diagonalClassOf (q * (q + 1) / 2 + ∑ j ∈ Finset.Icc 1 q, j * min (s j) 2)
        (diagonalOfList (diagonalNormalForm q fun j => min (s j) 2))).card

/-- Corollary 7, parts 1–3: the classes of size `1`, `2`, `3`, for a partition `α` of `n ≥ 1`
with `d = δ(α)`, as multisets of parts.
(1) `|[d]| = 1`: `n = C(q+1, 2)`, `d = (1, …, q)`, `[d] = {(q, …, 1)}`.
(2) `|[d]| = 2`: `q ≥ 1`, `k ≥ 2`, `n = C(q+1, 2) + k`, `d = (1, …, q, 1^{(k)})`,
`[d] = {(q+k, q-1, …, 1), (q, …, 1, 1^{(k)})}`; or `n = 2`, `d = (1, 1)`, `[d] = {(2), (1,1)}`.
(3) `|[d]| = 3`: `q, k ≥ 2`, `n = C(q+1, 2) + 2k`, `d = (1, …, q, 2^{(k)})`,
`[d] = {(q+k, q-1+k, q-2, …, 1), (q, …, 3, 2^{(k+1)}, 1), (q+k, q-1, …, 2, 1^{(k+1)})}`; or
`d = (1, 2, 1)`; or `d = (1, 2, 2)` (with the listed classes).
Part 4 (`|[d]| = 4`) is false as printed and is not stated (see the audit table).

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
