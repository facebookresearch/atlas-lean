/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.RingTheory.PowerSeries.Basic

import Mathlib.Combinatorics.Enumerative.Partition.YoungDiagram
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Data.List.GetD
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Ring

/-!
# Rook decomposition of the partition function

We define the max-rook statistic on Ferrers boards and prove the generating function
for partitions whose max-rook number is three.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Max-rook number of a board.** For a finite board $B \subseteq \mathbb{N} \times \mathbb{N}$,
whose cell $(i, j)$ lies in row $i$ and column $j$, the max-rook number of $B$ is the largest
size of a subset of $B$ that contains at most one cell of each row and at most one cell of each
column, that is, the largest number of non-attacking rooks that can be placed on $B$.

Source: N. Guru Sharan, *Rook Decomposition of the Partition Function*,
Journal of Integer Sequences 29 (2026), Article 26.2.6, Section 2 (max-rook
number). -/
def boardMaxRookNumber (B : Finset (ℕ × ℕ)) : ℕ :=
  (B.powerset.filter fun S =>
    (S.image Prod.fst).card = S.card ∧ (S.image Prod.snd).card = S.card).sup Finset.card

/-- **Ferrers board of a partition.** Let $p$ be a partition of $n$, and number rows and columns
from $0$. The Ferrers board of $p$ is the finite set of cells
$(i, j) \in \mathbb{N} \times \mathbb{N}$ such that the $(i+1)$-st largest part of $p$ exceeds $j$,
that is, such that more than $i$ parts of $p$, counted with multiplicity, exceed $j$.

Source: N. Guru Sharan, *Rook Decomposition of the Partition Function*,
Journal of Integer Sequences 29 (2026), Article 26.2.6, Section 1 (Ferrers
diagram and Ferrers board). -/
def partitionFerrersBoard {n : ℕ} (p : Nat.Partition n) : Finset (ℕ × ℕ) :=
  ((Finset.range n) ×ˢ (Finset.range n)).filter fun c =>
    c.1 < (p.parts.filter (c.2 < ·)).card

/-- **Max-rook number of a partition.** The max-rook number $R(\pi)$ of a partition $\pi$ of $n$
is the largest number of non-attacking rooks on the Ferrers board of $\pi$: the largest number
of cells of the board, no two in the same row and no two in the same column.

Source: N. Guru Sharan, *Rook Decomposition of the Partition Function*,
Journal of Integer Sequences 29 (2026), Article 26.2.6, Section 2. -/
def partitionMaxRookNumber {n : ℕ} (p : Nat.Partition n) : ℕ :=
  boardMaxRookNumber (partitionFerrersBoard p)

/-- **Partitions with a given max-rook number.** For natural numbers $k$ and $n$, $R_k(n)$ is
the number of partitions of $n$ whose max-rook number, the largest number of non-attacking rooks
on the Ferrers board, equals $k$.

Source: N. Guru Sharan, *Rook Decomposition of the Partition Function*,
Journal of Integer Sequences 29 (2026), Article 26.2.6, Equation (2.2). -/
def maxRookPartitionCount (k n : ℕ) : ℕ :=
  (Finset.univ.filter fun p : Nat.Partition n => partitionMaxRookNumber p = k).card

/-- **Largest max-rook number among partitions of $n$.** For a natural number $n \ge 1$, $F(n)$
is the largest max-rook number $R(\pi)$ over all partitions $\pi$ of $n$, where $R(\pi)$ is the
largest number of non-attacking rooks on the Ferrers board of $\pi$. By convention $F(0) = 1$.

Source: N. Guru Sharan, *Rook Decomposition of the Partition Function*,
Journal of Integer Sequences 29 (2026), Article 26.2.6, Equation (2.1). -/
def partitionMaxRookNumberMax (n : ℕ) : ℕ :=
  if n = 0 then 1 else Finset.univ.sup fun p : Nat.Partition n => partitionMaxRookNumber p

/-- **Ferrers board of the partition $(2, 1)$.** With rows and columns numbered from $0$, the
Ferrers board of the partition $(2, 1)$ of $3$ consists of exactly the three cells $(0, 0)$,
$(0, 1)$ and $(1, 0)$.

Source: N. Guru Sharan, *Rook Decomposition of the Partition Function*,
Journal of Integer Sequences 29 (2026), Article 26.2.6, Section 1 (Ferrers
board); characteristic check of `partitionFerrersBoard`. -/
theorem partitionFerrersBoard_two_one :
    partitionFerrersBoard (Nat.Partition.ofMultiset ({2, 1} : Multiset ℕ)) =
      {(0, 0), (0, 1), (1, 0)} := by
  decide +kernel

/-- **Max-rook number of the partition $(5, 3, 2, 1)$.** The partition $(5, 3, 2, 1)$ of $11$
has max-rook number $4$.

Source: N. Guru Sharan, *Rook Decomposition of the Partition Function*,
Journal of Integer Sequences 29 (2026), Article 26.2.6, Figure 1. -/
theorem partitionMaxRookNumber_five_three_two_one :
    partitionMaxRookNumber (Nat.Partition.ofMultiset ({5, 3, 2, 1} : Multiset ℕ)) = 4 := by
  decide +kernel

/-- **The convention $F(0) = 1$.** The function $F$, whose value $F(n)$ for $n \ge 1$ is the
largest max-rook number of a partition of $n$, takes the value $F(0) = 1$ at $n = 0$.

Source: N. Guru Sharan, *Rook Decomposition of the Partition Function*,
Journal of Integer Sequences 29 (2026), Article 26.2.6, after Equation (2.1). -/
@[simp]
theorem partitionMaxRookNumberMax_zero : partitionMaxRookNumberMax 0 = 1 := rfl

end

namespace maxRookPartitionCount_three_genFun

open Finset Finset.HasAntidiagonal YoungDiagram PowerSeries

private theorem count_lt_sort_getD {a : ℕ} {l : List ℕ} (hl : l.SortedGE) (i : ℕ) :
    a < l.getD i 0 ↔ i < (l.filter (a < ·)).length := by
  induction l generalizing i with
  | nil => simp
  | cons x xs ih =>
    have hxs := hl.pairwise.of_cons.sortedGE
    by_cases hx : a < x
    · cases i with
      | zero => simp [hx]
      | succ i => simpa [List.getD, hx] using ih hxs i
    · have hfilter : xs.filter (a < ·) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro y hy
        simpa using (show ¬a < y by
          have := (List.pairwise_cons.mp hl.pairwise).1 y hy
          omega)
      cases i with
      | zero => simp [hx, hfilter]
      | succ i =>
        have h := ih hxs i
        simpa [List.getD, hx, hfilter] using h

private theorem ferrersBoard_eq {n : ℕ} (p : Nat.Partition n) :
    partitionFerrersBoard p = (ofPartition p).cells := by
  ext ⟨i, j⟩
  rw [partitionFerrersBoard, mem_filter, mem_product, mem_range, mem_range, mem_cells]
  have hm : (i, j) ∈ ofPartition p ↔ i < (p.parts.filter (j < ·)).card := by
    rw [ofPartition, mem_ofRowLens]
    let l := p.parts.sort (· ≥ ·)
    change (∃ h : i < l.length, j < l[i]) ↔ _
    have heq : (∃ h : i < l.length, j < l[i]) ↔ j < l.getD i 0 := by
      by_cases hi : i < l.length
      · simp [hi]
      · simp [hi]
    rw [heq, count_lt_sort_getD (Multiset.pairwise_sort _ _).sortedGE]
    have h := congrArg (fun s : Multiset ℕ => (s.filter (j < ·)).card)
      (Multiset.sort_eq (r := (· ≥ ·)) p.parts)
    change (l.filter (j < ·)).length = _ at h
    rw [h]
  refine ⟨fun h ↦ hm.mpr h.2, fun h ↦ ⟨⟨?_, ?_⟩, hm.mp h⟩⟩
  · apply (mem_iff_lt_colLen.mp h).trans_le
    rw [colLen_eq_card]
    exact (card_le_card fun _ hc => (mem_cells _).mpr (mem_col_iff.mp hc).1).trans
      (card_ofPartition p).le
  · apply (mem_iff_lt_rowLen.mp h).trans_le
    rw [rowLen_eq_card]
    exact (card_le_card fun _ hc => (mem_cells _).mpr (mem_row_iff.mp hc).1).trans
      (card_ofPartition p).le

private def hasStaircase (k : ℕ) (μ : YoungDiagram) : Prop :=
  ∀ i j : ℕ, i + j + 1 = k → (i, j) ∈ μ

private theorem le_rook_iff_staircase (μ : YoungDiagram) (k : ℕ) :
    k ≤ boardMaxRookNumber μ.cells ↔ hasStaircase k μ := by
  constructor
  · intro hk i j hij
    by_contra hmiss
    -- A missing cell forces every rook into one of the rows above or columns to its left.
    have hupper : boardMaxRookNumber μ.cells ≤ i + j := by
      apply Finset.sup_le
      intro S hS
      obtain ⟨hsub, hrow, hcol⟩ := mem_filter.mp hS
      have hsub := mem_powerset.mp hsub
      let R := S.filter fun c => c.1 < i
      let C := S.filter fun c => c.2 < j ∧ i ≤ c.1
      have hcover : S ⊆ R ∪ C := by
        intro c hc
        have hcell := mem_cells c |>.mp (hsub hc)
        by_cases hr : c.1 < i
        · exact mem_union_left _ (mem_filter.mpr ⟨hc, hr⟩)
        · have hj : c.2 < j := by
            by_contra! hj
            exact hmiss (μ.up_left_mem (by omega) hj hcell)
          exact mem_union_right _ (mem_filter.mpr ⟨hc, hj, by omega⟩)
      have hR : R.card ≤ i := by
        rw [← card_image_of_injOn ((card_image_iff.mp hrow).mono (filter_subset _ _))]
        simpa using card_le_card (show R.image Prod.fst ⊆ range i by
          rintro x hx
          obtain ⟨c, hc, rfl⟩ := mem_image.mp hx
          exact mem_range.mpr (mem_filter.mp hc).2)
      have hC : C.card ≤ j := by
        rw [← card_image_of_injOn ((card_image_iff.mp hcol).mono (filter_subset _ _))]
        simpa using card_le_card (show C.image Prod.snd ⊆ range j by
          rintro x hx
          obtain ⟨c, hc, rfl⟩ := mem_image.mp hx
          exact mem_range.mpr (mem_filter.mp hc).2.1)
      exact (card_le_card hcover).trans ((card_union_le R C).trans (Nat.add_le_add hR hC))
    omega
  · intro hk
    let S := antidiagonal (k - 1)
    by_cases h0 : k = 0
    · simp [h0]
    have hcard : S.card = k := by
      simp [S, Finset.Nat.card_antidiagonal]
      omega
    have hinj (f : ℕ × ℕ → ℕ) (hf : f = Prod.fst ∨ f = Prod.snd) :
        Set.InjOn f S := by
      intro a ha b hb hab
      have hA := mem_antidiagonal.mp ha
      have hB := mem_antidiagonal.mp hb
      rcases hf with rfl | rfl
      all_goals apply Prod.ext <;> omega
    rw [← hcard]
    exact Finset.le_sup (f := Finset.card) (mem_filter.mpr
      ⟨mem_powerset.mpr (fun c hc => (mem_cells _).mpr
          (hk _ _ (by have := mem_antidiagonal.mp hc; omega))),
        card_image_of_injOn (hinj _ (Or.inl rfl)),
        card_image_of_injOn (hinj _ (Or.inr rfl))⟩)

private theorem staircase_three (μ : YoungDiagram) :
    hasStaircase 3 μ ↔ (0, 2) ∈ μ ∧ (1, 1) ∈ μ ∧ (2, 0) ∈ μ := by
  refine ⟨fun h ↦ ⟨h 0 2 rfl, h 1 1 rfl, h 2 0 rfl⟩, ?_⟩
  intro h i j hij
  have hp : (i, j) = (0, 2) ∨ (i, j) = (1, 1) ∨ (i, j) = (2, 0) := by
    simp only [Prod.mk.injEq]
    omega
  rcases hp with hp | hp | hp <;> rw [hp]
  exacts [h.1, h.2.1, h.2.2]

private theorem staircase_four (μ : YoungDiagram) :
    hasStaircase 4 μ ↔ (0, 3) ∈ μ ∧ (1, 2) ∈ μ ∧ (2, 1) ∈ μ ∧ (3, 0) ∈ μ := by
  refine ⟨fun h ↦ ⟨h 0 3 rfl, h 1 2 rfl, h 2 1 rfl, h 3 0 rfl⟩, ?_⟩
  intro h i j hij
  have hp : (i, j) = (0, 3) ∨ (i, j) = (1, 2) ∨ (i, j) = (2, 1) ∨ (i, j) = (3, 0) := by
    simp only [Prod.mk.injEq]
    omega
  rcases hp with hp | hp | hp | hp <;> rw [hp]
  exacts [h.1, h.2.1, h.2.2.1, h.2.2.2]

private def rankThree (μ : YoungDiagram) : Prop :=
  hasStaircase 3 μ ∧ ¬hasStaircase 4 μ

private theorem rook_eq_three (μ : YoungDiagram) :
    boardMaxRookNumber μ.cells = 3 ↔ rankThree μ := by
  rw [rankThree, ← le_rook_iff_staircase, ← le_rook_iff_staircase]
  omega

/-! Cut at the largest square in the diagram. A 2 × 2 square allows an arm on each side.
For a 3 × 3 square, an arm is allowed on only one side. The arm coordinates are successive
differences in the row or column lengths, so their weights are 1, 2 and (for three rows) 3. -/

private def twoRows (a b : ℕ) : YoungDiagram :=
  ofRowLens [2 + b + a, 2 + b] (by simp [List.sortedGE_iff_pairwise])

private theorem mem_twoRows (a b i j : ℕ) :
    (i, j) ∈ twoRows a b ↔ (i = 0 ∧ j < 2 + b + a) ∨ (i = 1 ∧ j < 2 + b) := by
  rcases i with _ | _ | i <;> simp [twoRows, mem_ofRowLens, List.getElem_cons_succ]

private theorem card_twoRows (a b : ℕ) : (twoRows a b).card = 4 + (a + 2 * b) := by
  rw [← sum_rowLens_eq_card, twoRows, rowLens_ofRowLens_eq_self]
  · simp
    omega
  · simp

private def twoSquare (z : (ℕ × ℕ) × (ℕ × ℕ)) : YoungDiagram :=
  twoRows z.1.1 z.1.2 ⊔ (twoRows z.2.1 z.2.2).transpose

private theorem mem_twoSquare (a b c d i j : ℕ) :
    (i, j) ∈ twoSquare ((a, b), (c, d)) ↔
      (i = 0 ∧ j < 2 + b + a) ∨ (i = 1 ∧ j < 2 + b) ∨
      (j = 0 ∧ i < 2 + d + c) ∨ (j = 1 ∧ i < 2 + d) := by
  simp [twoSquare, mem_transpose, mem_twoRows, or_assoc]

private theorem card_twoSquare (a b c d : ℕ) :
    (twoSquare ((a, b), (c, d))).card = 4 + ((a + 2 * b) + (c + 2 * d)) := by
  have hi : ((twoRows a b ⊓ (twoRows c d).transpose).cells) = range 2 ×ˢ range 2 := by
    ext ⟨i, j⟩
    simp only [mem_cells, mem_inf, mem_transpose, Prod.swap_prod_mk, mem_twoRows, mem_product,
      mem_range]
    omega
  have h := Finset.card_union_add_card_inter (twoRows a b).cells ((twoRows c d).transpose.cells)
  rw [← cells_sup, ← cells_inf, hi, card_product, card_range] at h
  change (twoSquare ((a, b), (c, d))).card + 2 * 2 =
    (twoRows a b).card + (twoRows c d).transpose.card at h
  rw [card_transpose, card_twoRows, card_twoRows] at h
  omega

private theorem twoSquare_injective : Function.Injective twoSquare := by
  rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ ⟨⟨a', b'⟩, ⟨c', d'⟩⟩ h
  have hrow0 (j : ℕ) : j < 2 + b + a ↔ j < 2 + b' + a' := by
    have hmem := Iff.of_eq (congrArg (fun μ : YoungDiagram ↦ (0, j) ∈ μ) h)
    simp [mem_twoSquare] at hmem
    omega
  have hrow1 (j : ℕ) : j < 2 + b ↔ j < 2 + b' := by
    have hmem := Iff.of_eq (congrArg (fun μ : YoungDiagram ↦ (1, j) ∈ μ) h)
    simp [mem_twoSquare] at hmem
    omega
  have hcol0 (i : ℕ) : i < 2 + d + c ↔ i < 2 + d' + c' := by
    have hmem := Iff.of_eq (congrArg (fun μ : YoungDiagram ↦ (i, 0) ∈ μ) h)
    simp [mem_twoSquare] at hmem
    omega
  have hcol1 (i : ℕ) : i < 2 + d ↔ i < 2 + d' := by
    have hmem := Iff.of_eq (congrArg (fun μ : YoungDiagram ↦ (i, 1) ∈ μ) h)
    simp [mem_twoSquare] at hmem
    omega
  simp only [Prod.mk.injEq]
  have := eq_of_forall_lt_iff hrow0
  have := eq_of_forall_lt_iff hrow1
  have := eq_of_forall_lt_iff hcol0
  have := eq_of_forall_lt_iff hcol1
  omega

private theorem exists_twoSquare {μ : YoungDiagram} (hcore : (1, 1) ∈ μ)
    (hmiss : (2, 2) ∉ μ) : ∃ z, twoSquare z = μ := by
  let r := μ.rowLen
  let c := μ.colLen
  have hr : 2 ≤ r 1 := mem_iff_lt_rowLen.mp hcore
  have hc : 2 ≤ c 1 := mem_iff_lt_colLen.mp hcore
  have hr' : r 1 ≤ r 0 := μ.rowLen_anti 0 1 (by decide)
  have hc' : c 1 ≤ c 0 := μ.colLen_anti 0 1 (by decide)
  refine ⟨((r 0 - r 1, r 1 - 2), (c 0 - c 1, c 1 - 2)), ?_⟩
  ext ⟨i, j⟩
  simp only [mem_cells, mem_twoSquare]
  have hR : (i, j) ∈ μ ↔ j < r i := mem_iff_lt_rowLen
  have hC : (i, j) ∈ μ ↔ i < c j := mem_iff_lt_colLen
  by_cases hrow : i < 2
  · have hi : i = 0 ∨ i = 1 := by omega
    rcases hi with rfl | rfl <;> rw [hR] <;> omega
  · by_cases hcol : j < 2
    · have hj : j = 0 ∨ j = 1 := by omega
      rcases hj with rfl | rfl <;> rw [hC] <;> omega
    · have hn : (i, j) ∉ μ := fun h ↦ hmiss (μ.up_left_mem (by omega) (by omega) h)
      simp only [hn, iff_false]
      omega

private def threeRows (z : ℕ × ℕ × ℕ) : YoungDiagram :=
  ofRowLens [3 + z.2.2 + z.2.1 + z.1, 3 + z.2.2 + z.2.1, 3 + z.2.2] (by
    simp [List.sortedGE_iff_pairwise]
    omega)

private theorem mem_threeRows (a b c i j : ℕ) :
    (i, j) ∈ threeRows (a, b, c) ↔
      (i = 0 ∧ j < 3 + c + b + a) ∨ (i = 1 ∧ j < 3 + c + b) ∨ (i = 2 ∧ j < 3 + c) := by
  rcases i with _ | _ | _ | i <;> simp [threeRows, mem_ofRowLens, List.getElem_cons_succ]

private theorem card_threeRows (a b c : ℕ) :
    (threeRows (a, b, c)).card = 9 + (a + (2 * b + 3 * c)) := by
  rw [← sum_rowLens_eq_card, threeRows, rowLens_ofRowLens_eq_self]
  · simp
    omega
  · simp

private theorem threeRows_injective : Function.Injective threeRows := by
  rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
  have h0 (j : ℕ) : j < 3 + c + b + a ↔ j < 3 + c' + b' + a' := by
    simpa [mem_threeRows] using Iff.of_eq
      (congrArg (fun μ : YoungDiagram ↦ (0, j) ∈ μ) h)
  have h1 (j : ℕ) : j < 3 + c + b ↔ j < 3 + c' + b' := by
    simpa [mem_threeRows] using Iff.of_eq
      (congrArg (fun μ : YoungDiagram ↦ (1, j) ∈ μ) h)
  have h2 (j : ℕ) : j < 3 + c ↔ j < 3 + c' := by
    simpa [mem_threeRows] using Iff.of_eq
      (congrArg (fun μ : YoungDiagram ↦ (2, j) ∈ μ) h)
  simp only [Prod.mk.injEq]
  have := eq_of_forall_lt_iff h0
  have := eq_of_forall_lt_iff h1
  have := eq_of_forall_lt_iff h2
  omega

private theorem exists_threeRows {μ : YoungDiagram} (hcore : (2, 2) ∈ μ)
    (hmiss : (3, 0) ∉ μ) : ∃ z, threeRows z = μ := by
  let r := μ.rowLen
  have hr : 3 ≤ r 2 := mem_iff_lt_rowLen.mp hcore
  have h01 : r 1 ≤ r 0 := μ.rowLen_anti 0 1 (by decide)
  have h12 : r 2 ≤ r 1 := μ.rowLen_anti 1 2 (by decide)
  refine ⟨(r 0 - r 1, r 1 - r 2, r 2 - 3), ?_⟩
  ext ⟨i, j⟩
  simp only [mem_cells, mem_threeRows]
  have hR : (i, j) ∈ μ ↔ j < r i := mem_iff_lt_rowLen
  by_cases hrow : i < 3
  · have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hi with rfl | rfl | rfl <;> rw [hR] <;> omega
  · have hn : (i, j) ∉ μ := fun h ↦ hmiss (μ.up_left_mem (by omega) (by omega) h)
    simp only [hn, iff_false]
    omega

/-! The coefficients of a weight enumerator count the finite fibers of the weight map.
Products add weights, and multiplying by a monomial adds a fixed weight. -/

private noncomputable def enumerator {α : Type*} (w : α → ℕ) : ℤ⟦X⟧ :=
  mk fun n ↦ (Nat.card {a // w a = n} : ℤ)

private def finiteFibers {α : Type*} (w : α → ℕ) : Prop :=
  ∀ n, Finite {a // w a = n}

private theorem finiteFibers_subtype {α : Type*} {w : α → ℕ} (hw : finiteFibers w)
    (p : α → Prop) : finiteFibers (fun a : Subtype p ↦ w a.1) := by
  intro n
  let _ := hw n
  exact Finite.of_injective (fun a ↦ (⟨a.1.1, a.2⟩ : {x // w x = n}))
    (fun a b h ↦ Subtype.ext (Subtype.ext (congrArg (fun x : {x // w x = n} ↦ x.1) h)))

private theorem enumerator_congr {α β : Type*} (u : α → ℕ) (v : β → ℕ)
    (e : α ≃ β) (h : ∀ a, u a = v (e a)) : enumerator u = enumerator v := by
  ext n
  simp only [enumerator, coeff_mk]
  exact_mod_cast Nat.card_congr (e.subtypeEquiv fun a ↦ by rw [h a])

private def sumFiberEquiv {α β : Type*} (u : α → ℕ) (v : β → ℕ) (n : ℕ) :
    {z : α × β // u z.1 + v z.2 = n} ≃
      (Σ m : antidiagonal n, {a // u a = m.1.1} × {b // v b = m.1.2}) where
  toFun z := ⟨⟨(u z.1.1, v z.1.2), mem_antidiagonal.mpr z.2⟩, ⟨z.1.1, rfl⟩, ⟨z.1.2, rfl⟩⟩
  invFun z := ⟨(z.2.1.1, z.2.2.1), by
    rw [z.2.1.2, z.2.2.2]
    exact mem_antidiagonal.mp z.1.2⟩
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨⟨i, j⟩, hij⟩, ⟨a, ha⟩, ⟨b, hb⟩⟩
    cases ha
    cases hb
    rfl

private theorem finiteFibers_prod {α β : Type*} {u : α → ℕ} {v : β → ℕ}
    (hu : finiteFibers u) (hv : finiteFibers v) :
    finiteFibers (fun z : α × β ↦ u z.1 + v z.2) := by
  intro n
  let _ (m : antidiagonal n) : Fintype ({a // u a = m.1.1} × {b // v b = m.1.2}) :=
    have := hu m.1.1
    have := hv m.1.2
    Fintype.ofFinite _
  exact Finite.of_equiv _ (sumFiberEquiv u v n).symm

private theorem enumerator_prod {α β : Type*} {u : α → ℕ} {v : β → ℕ}
    (hu : finiteFibers u) (hv : finiteFibers v) :
    enumerator (fun z : α × β ↦ u z.1 + v z.2) = enumerator u * enumerator v := by
  ext n
  let _ (m : antidiagonal n) : Finite ({a // u a = m.1.1} × {b // v b = m.1.2}) :=
    have := hu m.1.1
    have := hv m.1.2
    inferInstance
  rw [coeff_mul]
  simp only [enumerator, coeff_mk]
  rw [Nat.card_congr (sumFiberEquiv u v n), Nat.card_sigma, Nat.cast_sum]
  simp only [Nat.card_prod, Nat.cast_mul]
  exact sum_attach (antidiagonal n) (fun m ↦
    (Nat.card {a // u a = m.1} : ℤ) * (Nat.card {b // v b = m.2} : ℤ))

private theorem enumerator_sum {α β : Type*} {u : α → ℕ} {v : β → ℕ}
    (hu : finiteFibers u) (hv : finiteFibers v) :
    enumerator (Sum.elim u v) = enumerator u + enumerator v := by
  ext n
  let _ := hu n
  let _ := hv n
  let e : {z : α ⊕ β // Sum.elim u v z = n} ≃
      {a // u a = n} ⊕ {b // v b = n} :=
    { toFun := fun ⟨z, hz⟩ ↦ match z with
        | .inl a => .inl ⟨a, hz⟩
        | .inr b => .inr ⟨b, hz⟩
      invFun := fun z ↦ match z with
        | .inl a => ⟨.inl a.1, a.2⟩
        | .inr b => ⟨.inr b.1, b.2⟩
      left_inv := by rintro ⟨_ | _, _⟩ <;> rfl
      right_inv := by rintro (_ | _) <;> rfl }
  simp [enumerator, Nat.card_congr e]

private theorem enumerator_split {α : Type*} {w : α → ℕ} (hw : finiteFibers w)
    (p : α → Prop) :
    enumerator w = enumerator (fun a : Subtype p ↦ w a.1) +
      enumerator (fun a : {a // ¬p a} ↦ w a.1) := by
  classical
  rw [← enumerator_sum (finiteFibers_subtype hw p) (finiteFibers_subtype hw _)]
  exact (enumerator_congr _ _ (Equiv.sumCompl p) (by intro a; cases a <;> rfl)).symm

private theorem enumerator_shift {α : Type*} (w : α → ℕ) (k : ℕ) :
    enumerator (fun a ↦ k + w a) = X ^ k * enumerator w := by
  ext n
  rw [coeff_X_pow_mul']
  simp only [enumerator, coeff_mk]
  split_ifs with h
  · have e : {a // k + w a = n} ≃ {a // w a = n - k} :=
      Equiv.subtypeEquivRight fun a ↦ by omega
    rw [Nat.card_congr e]
  · have : IsEmpty {a // k + w a = n} := ⟨fun a ↦ h (by
      have ha : k + w a.1 = n := a.2
      omega)⟩
    simp

private theorem enumerator_zero {α : Type*} [Nonempty α] [Subsingleton α] :
    enumerator (fun _ : α ↦ 0) = 1 := by
  ext n
  cases n with
  | zero => simp [enumerator, Nat.card_unique]
  | succ n => simp [enumerator, coeff_one]

private theorem enumerator_positive {α : Type*} {w : α → ℕ} (hw : finiteFibers w)
    (a₀ : α) (h₀ : ∀ a, w a = 0 ↔ a = a₀) :
    enumerator (fun a : {a // 0 < w a} ↦ w a.1) = enumerator w - 1 := by
  have hsplit := enumerator_split hw (fun a ↦ w a = 0)
  let _ : Nonempty {a // w a = 0} := ⟨⟨a₀, (h₀ _).mpr rfl⟩⟩
  let _ : Subsingleton {a // w a = 0} :=
    ⟨fun a b ↦ Subtype.ext (((h₀ _).mp a.2).trans ((h₀ _).mp b.2).symm)⟩
  have hz : enumerator (fun a : {a // w a = 0} ↦ w a.1) = 1 := by
    rw [show (fun a : {a // w a = 0} ↦ w a.1) = (fun _ ↦ 0) from funext (·.2)]
    exact enumerator_zero
  have he := enumerator_congr
    (fun a : {a // 0 < w a} ↦ w a.1) (fun a : {a // ¬w a = 0} ↦ w a.1)
    (Equiv.subtypeEquivRight fun _ ↦ Nat.pos_iff_ne_zero) (fun _ ↦ rfl)
  rw [hz, ← he] at hsplit
  rw [hsplit, add_comm 1, add_sub_cancel_right]

private noncomputable def geom (k : ℕ) : ℤ⟦X⟧ := enumerator (fun a : ℕ ↦ k * a)

private theorem finiteFibers_mul_nat {k : ℕ} (hk : 0 < k) :
    finiteFibers (fun a : ℕ ↦ k * a) := by
  intro n
  let _ : Subsingleton {a // k * a = n} :=
    ⟨fun a b ↦ Subtype.ext (Nat.eq_of_mul_eq_mul_left hk (a.2.trans b.2.symm))⟩
  infer_instance

private theorem geom_mul {k : ℕ} (hk : 0 < k) : (1 - X ^ k) * geom k = 1 := by
  have hsplit := enumerator_positive (finiteFibers_mul_nat hk) 0 (fun a ↦ by
    simp [Nat.ne_of_gt hk])
  let e : ℕ ≃ {a : ℕ // 0 < k * a} :=
    { toFun := fun a ↦ ⟨a + 1, Nat.mul_pos hk (Nat.succ_pos _)⟩
      invFun := fun a ↦ a.1 - 1
      left_inv := by intro a; simp
      right_inv := by
        intro a
        have ha : a.1 ≠ 0 := by
          intro hz
          have := a.2
          simp [hz] at this
        exact Subtype.ext (by dsimp; omega) }
  have he := enumerator_congr (fun a : ℕ ↦ k + k * a) (fun a : {a // 0 < k * a} ↦ k * a.1)
    e (by intro a; simp [e, Nat.mul_add, Nat.add_comm])
  rw [enumerator_shift, hsplit] at he
  unfold geom
  rw [sub_mul, one_mul, he]
  ring

private def weightTwo (z : ℕ × ℕ) : ℕ := z.1 + 2 * z.2

private def weightThree (z : ℕ × ℕ × ℕ) : ℕ := z.1 + (2 * z.2.1 + 3 * z.2.2)

private abbrev ArmTwo := {z // 0 < weightTwo z}

private abbrev ArmThree := {z // 0 < weightThree z}

private def weightArms (z : ArmTwo × ArmTwo) : ℕ := weightTwo z.1.1 + weightTwo z.2.1

/-- An arm reaches the next staircase when both extensions are at least one
and the longer is at least two. -/
private def reachesFour (z : ArmTwo) : Prop := 0 < z.1.2 ∧ 2 ≤ z.1.1 + z.1.2

private abbrev TwoCase := {z : ArmTwo × ArmTwo // ¬ (reachesFour z.1 ∧ reachesFour z.2)}

private abbrev ThreeCase := (ℕ × ℕ × ℕ) ⊕ ArmThree

private theorem twoSquare_rankThree (a b c d : ℕ) :
    rankThree (twoSquare ((a, b), (c, d))) ↔
      0 < weightTwo (a, b) ∧ 0 < weightTwo (c, d) ∧
        ¬ ((0 < b ∧ 2 ≤ a + b) ∧ (0 < d ∧ 2 ≤ c + d)) := by
  simp [rankThree, staircase_three, staircase_four, mem_twoSquare, weightTwo]
  omega

private noncomputable def twoCaseEquiv :
    TwoCase ≃ {μ : Subtype rankThree // (2, 2) ∉ μ.1} := by
  refine Equiv.ofBijective (fun z ↦
    ⟨⟨twoSquare (z.1.1.1, z.1.2.1), ?_⟩, ?_⟩) ⟨?_, ?_⟩
  · rcases z with ⟨⟨⟨⟨a, b⟩, ha⟩, ⟨⟨c, d⟩, hc⟩⟩, hz⟩
    exact (twoSquare_rankThree a b c d).mpr ⟨ha, hc, hz⟩
  · rcases z with ⟨⟨⟨⟨a, b⟩, _⟩, ⟨⟨c, d⟩, _⟩⟩, _⟩
    simp [mem_twoSquare]
  · intro z z' h
    have he := twoSquare_injective (congrArg (fun μ : {μ : Subtype rankThree //
      (2, 2) ∉ μ.1} ↦ μ.1.1) h)
    exact Subtype.ext (Prod.ext (Subtype.ext (congrArg Prod.fst he))
      (Subtype.ext (congrArg Prod.snd he)))
  · rintro ⟨⟨μ, hμ⟩, hmiss⟩
    have hcore := (staircase_three μ).mp hμ.1 |>.2.1
    obtain ⟨⟨⟨a, b⟩, ⟨c, d⟩⟩, rfl⟩ := exists_twoSquare hcore hmiss
    obtain ⟨ha, hc, hz⟩ := (twoSquare_rankThree a b c d).mp hμ
    exact ⟨⟨(⟨(a, b), ha⟩, ⟨(c, d), hc⟩), hz⟩, rfl⟩

private theorem rankThree_transpose (μ : YoungDiagram) :
    rankThree μ.transpose ↔ rankThree μ := by
  simp [rankThree, staircase_three, staircase_four, mem_transpose]
  tauto

private def threeCaseDiagram : ThreeCase → YoungDiagram
  | .inl z => threeRows z
  | .inr z => (threeRows z.1).transpose

private noncomputable def threeCaseEquiv :
    ThreeCase ≃ {μ : Subtype rankThree // (2, 2) ∈ μ.1} := by
  have hrow (z : ℕ × ℕ × ℕ) :
      rankThree (threeRows z) ∧ (2, 2) ∈ threeRows z ∧ (3, 0) ∉ threeRows z := by
    rcases z with ⟨a, b, c⟩
    simp [rankThree, staircase_three, staircase_four, mem_threeRows]
    omega
  have hlong (z : ArmThree) : (3, 0) ∈ (threeRows z.1).transpose := by
    rcases z with ⟨⟨a, b, c⟩, hz⟩
    change 0 < a + (2 * b + 3 * c) at hz
    simpa [mem_transpose, mem_threeRows] using (show 3 < 3 + c + b + a by omega)
  refine Equiv.ofBijective (fun z ↦ ⟨⟨threeCaseDiagram z, ?_⟩, ?_⟩) ⟨?_, ?_⟩
  · cases z with
    | inl z => exact (hrow z).1
    | inr z => exact (rankThree_transpose _).mpr (hrow z.1).1
  · cases z with
    | inl z => exact (hrow z).2.1
    | inr z => exact mem_transpose.mpr (hrow z.1).2.1
  · intro z z' h
    have he := congrArg (fun μ : {μ : Subtype rankThree // (2, 2) ∈ μ.1} ↦ μ.1.1) h
    change threeCaseDiagram z = threeCaseDiagram z' at he
    cases z with
    | inl u =>
      cases z' with
      | inl v => exact congrArg Sum.inl (threeRows_injective he)
      | inr v =>
        change threeRows u = (threeRows v.1).transpose at he
        exact False.elim ((hrow u).2.2 (he.symm ▸ hlong v))
    | inr u =>
      cases z' with
      | inl v =>
        change (threeRows u.1).transpose = threeRows v at he
        exact False.elim ((hrow v).2.2 (he ▸ hlong u))
      | inr v =>
        exact congrArg Sum.inr (Subtype.ext (threeRows_injective (transpose_eq_iff.mp he)))
  · rintro ⟨⟨μ, hμ⟩, hcore⟩
    by_cases hdown : (3, 0) ∈ μ
    · have hright : (0, 3) ∉ μ := by
        intro h
        apply hμ.2
        exact (staircase_four μ).mpr
          ⟨h, μ.up_left_mem (by decide) le_rfl hcore,
            μ.up_left_mem le_rfl (by decide) hcore, hdown⟩
      obtain ⟨⟨a, b, c⟩, he⟩ := exists_threeRows (μ := μ.transpose)
        (mem_transpose.mpr hcore) (fun h ↦ hright (mem_transpose.mp h))
      have ht : (threeRows (a, b, c)).transpose = μ := by rw [he, transpose_transpose]
      have hlong' : 0 < weightThree (a, b, c) := by
        rw [← ht, mem_transpose, Prod.swap_prod_mk, mem_threeRows] at hdown
        simp [weightThree] at hdown ⊢
        omega
      exact ⟨Sum.inr ⟨(a, b, c), hlong'⟩, Subtype.ext (Subtype.ext ht)⟩
    · obtain ⟨z, hz⟩ := exists_threeRows hcore hdown
      exact ⟨Sum.inl z, Subtype.ext (Subtype.ext hz)⟩

private theorem finiteFibers_weightTwo : finiteFibers weightTwo := by
  have h := finiteFibers_prod (finiteFibers_mul_nat (k := 1) (by decide))
    (finiteFibers_mul_nat (k := 2) (by decide))
  unfold weightTwo
  simpa using h

private theorem finiteFibers_weightThree : finiteFibers weightThree := by
  have h := finiteFibers_prod (finiteFibers_mul_nat (k := 1) (by decide))
    (finiteFibers_prod (finiteFibers_mul_nat (k := 2) (by decide))
      (finiteFibers_mul_nat (k := 3) (by decide)))
  unfold weightThree
  simpa using h

private theorem finiteFibers_armTwo : finiteFibers (fun z : ArmTwo ↦ weightTwo z.1) :=
  finiteFibers_subtype finiteFibers_weightTwo _

private theorem finiteFibers_armThree : finiteFibers (fun z : ArmThree ↦ weightThree z.1) :=
  finiteFibers_subtype finiteFibers_weightThree _

private theorem enumerator_weightTwo : enumerator weightTwo = geom 1 * geom 2 := by
  have h := enumerator_prod (finiteFibers_mul_nat (k := 1) (by decide))
    (finiteFibers_mul_nat (k := 2) (by decide))
  unfold weightTwo
  simpa [geom] using h

private theorem enumerator_weightThree : enumerator weightThree = geom 1 * (geom 2 * geom 3) := by
  have h₂ := finiteFibers_mul_nat (k := 2) (by decide)
  have h₃ := finiteFibers_mul_nat (k := 3) (by decide)
  have h := enumerator_prod (finiteFibers_mul_nat (k := 1) (by decide)) (finiteFibers_prod h₂ h₃)
  rw [enumerator_prod h₂ h₃] at h
  unfold weightThree
  simpa [geom] using h

private theorem enumerator_armTwo :
    enumerator (fun z : ArmTwo ↦ weightTwo z.1) = geom 1 * geom 2 - 1 := by
  rw [enumerator_positive finiteFibers_weightTwo (0, 0), enumerator_weightTwo]
  rintro ⟨a, b⟩
  simp only [weightTwo, Prod.mk.injEq]
  omega

private theorem enumerator_armThree :
    enumerator (fun z : ArmThree ↦ weightThree z.1) = geom 1 * (geom 2 * geom 3) - 1 := by
  rw [enumerator_positive finiteFibers_weightThree (0, 0, 0), enumerator_weightThree]
  rintro ⟨a, b, c⟩
  simp only [weightThree, Prod.mk.injEq]
  omega

private def extendArm : ArmTwo ≃ Subtype reachesFour where
  toFun z := ⟨⟨(z.1.1, z.1.2 + 1), by simp [weightTwo]⟩, by
    have hz := z.2
    simp [weightTwo] at hz
    simp [reachesFour]
    omega⟩
  invFun z := ⟨(z.1.1.1, z.1.1.2 - 1), by
    have hz := z.2
    simp only [reachesFour] at hz
    simp [weightTwo]
    omega⟩
  left_inv z := by
    apply Subtype.ext
    exact Prod.ext rfl (Nat.add_sub_cancel _ _)
  right_inv z := by
    have hz := z.2.1
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext rfl (by dsimp; omega)

private theorem enumerator_twoCase :
    enumerator (fun z : TwoCase ↦ 4 + weightArms z.1) =
      X ^ 4 * (1 - X ^ 4) * (geom 1 * geom 2 - 1) ^ 2 := by
  -- Subtract placements that reach the fourth staircase on both sides of the square.
  have hArms : enumerator weightArms = (geom 1 * geom 2 - 1) ^ 2 :=
    (enumerator_prod finiteFibers_armTwo finiteFibers_armTwo).trans
      (by rw [enumerator_armTwo, pow_two])
  have hsplit := enumerator_split (w := weightArms)
    (finiteFibers_prod finiteFibers_armTwo finiteFibers_armTwo)
    (fun z ↦ reachesFour z.1 ∧ reachesFour z.2)
  rw [hArms] at hsplit
  let e : (ArmTwo × ArmTwo) ≃ {z : ArmTwo × ArmTwo // reachesFour z.1 ∧ reachesFour z.2} :=
    (Equiv.prodCongr extendArm extendArm).trans Equiv.subtypeProdEquivProd.symm
  have he := enumerator_congr (fun z ↦ 4 + weightArms z)
    (fun z : {z : ArmTwo × ArmTwo // reachesFour z.1 ∧ reachesFour z.2} ↦ weightArms z.1)
    e (by
      rintro ⟨⟨⟨a, b⟩, ha⟩, ⟨⟨c, d⟩, hc⟩⟩
      change 4 + (a + 2 * b + (c + 2 * d)) = a + 2 * (b + 1) + (c + 2 * (d + 1))
      omega)
  rw [enumerator_shift, hArms] at he
  rw [← he] at hsplit
  have hgood : enumerator (fun z : TwoCase ↦ weightArms z.1) =
      (geom 1 * geom 2 - 1) ^ 2 - X ^ 4 * (geom 1 * geom 2 - 1) ^ 2 :=
    eq_sub_of_add_eq (by rw [add_comm, ← hsplit])
  rw [enumerator_shift, hgood]
  ring

private theorem enumerator_threeCase :
    enumerator (fun z ↦ 9 + Sum.elim weightThree (fun v : ArmThree ↦ weightThree v.1) z) =
      X ^ 9 * (2 * (geom 1 * (geom 2 * geom 3)) - 1) := by
  rw [enumerator_shift, enumerator_sum finiteFibers_weightThree finiteFibers_armThree,
    enumerator_weightThree, enumerator_armThree]
  ring

private theorem rookEnumerator :
    mk (fun n => (maxRookPartitionCount 3 n : ℤ)) =
      enumerator (fun μ : Subtype rankThree ↦ μ.1.card) := by
  classical
  ext n
  simp only [enumerator, coeff_mk]
  apply congrArg (fun n : ℕ ↦ (n : ℤ))
  let e : {μ : Subtype rankThree // μ.1.card = n} ≃
      {p : Nat.Partition n // partitionMaxRookNumber p = 3} :=
    (Equiv.subtypeSubtypeEquivSubtypeInter _ _).trans
      ((Equiv.subtypeEquivRight (fun _ ↦ and_comm)).trans
        (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm) |>.trans
      (YoungDiagram.equivPartition.subtypeEquiv (fun μ ↦ by
        change rankThree μ.1 ↔ partitionMaxRookNumber (μ.1.toPartition μ.2) = 3
        simp only [partitionMaxRookNumber, ferrersBoard_eq, ofPartition_toPartition]
        exact (rook_eq_three _).symm))
  rw [Nat.card_congr e]
  unfold maxRookPartitionCount
  rw [Nat.card_eq_fintype_card, ← Fintype.card_coe]
  apply Fintype.card_congr
  exact Equiv.subtypeEquivRight (fun p ↦ by simp)

private theorem enumerator_rankThree :
    mk (fun n => (maxRookPartitionCount 3 n : ℤ)) =
      X ^ 4 * (1 - X ^ 4) * (geom 1 * geom 2 - 1) ^ 2 +
        X ^ 9 * (2 * (geom 1 * (geom 2 * geom 3)) - 1) := by
  have hf : finiteFibers (fun μ : YoungDiagram ↦ μ.card) := by
    intro n
    exact Finite.of_equiv (Nat.Partition n) YoungDiagram.equivPartition.symm
  rw [rookEnumerator, enumerator_split (finiteFibers_subtype hf rankThree)
    (fun μ => (2, 2) ∈ μ.1)]
  rw [← enumerator_congr (fun z : TwoCase ↦ 4 + weightArms z.1) _ twoCaseEquiv (fun z ↦ by
    rcases z with ⟨⟨⟨⟨a, b⟩, _⟩, ⟨⟨c, d⟩, _⟩⟩, _⟩
    exact (card_twoSquare a b c d).symm)]
  rw [← enumerator_congr
    (fun z ↦ 9 + Sum.elim weightThree (fun v : ArmThree ↦ weightThree v.1) z)
    _ threeCaseEquiv (fun z ↦ by
    rcases z with ⟨a, b, c⟩ | ⟨⟨a, b, c⟩, _⟩
    · exact (card_threeRows a b c).symm
    · exact ((card_transpose _).trans (card_threeRows a b c)).symm)]
  rw [enumerator_twoCase, enumerator_threeCase, add_comm]

private theorem clearDenominator :
    (1 - X) ^ 3 * (1 + X + X ^ 2) *
        (X ^ 4 * (1 - X ^ 4) * (geom 1 * geom 2 - 1) ^ 2 +
          X ^ 9 * (2 * (geom 1 * (geom 2 * geom 3)) - 1)) =
      X ^ 6 * (1 + 2 * X + X ^ 2 + 2 * X ^ 3 - X ^ 4 - X ^ 6 - X ^ 7 + X ^ 8) := by
  let x : ℤ⟦X⟧ := X
  let d₁ := 1 - x
  let d₂ := 1 - x ^ 2
  let d₃ := 1 - x ^ 3
  have h₁ : d₁ * geom 1 = 1 := by simpa [d₁, x] using geom_mul (k := 1) (by decide)
  have h₂ : d₂ * geom 2 = 1 := geom_mul (by decide)
  have h₃ : d₃ * geom 3 = 1 := geom_mul (by decide)
  have h₁₂ : d₁ * d₂ * (geom 1 * geom 2 - 1) = 1 - d₁ * d₂ := by
    calc
      _ = (d₁ * geom 1) * (d₂ * geom 2) - d₁ * d₂ := by ring
      _ = _ := by rw [h₁, h₂, one_mul]
  have h₁₂₃ : d₁ * d₂ * d₃ * (geom 1 * (geom 2 * geom 3)) = 1 := by
    calc
      _ = (d₁ * geom 1) * (d₂ * geom 2) * (d₃ * geom 3) := by ring
      _ = _ := by rw [h₁, h₂, h₃, one_mul, one_mul]
  -- Clear the extra factor of `1 - X^2` shared by the two counting cases.
  apply (IsUnit.of_mul_eq_one _ h₂).mul_left_cancel
  calc
    _ = x ^ 4 * (1 + x ^ 2) * d₃ * (d₁ * d₂ * (geom 1 * geom 2 - 1)) ^ 2 +
        x ^ 9 * (2 * d₁ * (d₁ * d₂ * d₃ * (geom 1 * (geom 2 * geom 3))) -
          d₁ ^ 2 * d₂ * d₃) := by dsimp [d₁, d₂, d₃, x]; ring
    _ = _ := by rw [h₁₂, h₁₂₃]; dsimp [d₁, d₂, d₃, x]; ring

end maxRookPartitionCount_three_genFun

open PowerSeries

/-- **Generating function of $R_3(n)$.** Let $R_3(n)$ be the number of partitions of $n$ with
max-rook number $3$. In the ring $\mathbb{Z}[[q]]$ of formal power series with integer
coefficients,

$$(1-q)^3(1+q+q^2) \sum_{n \ge 0} R_3(n)\, q^n = q^6(1+2q+q^2+2q^3-q^4-q^6-q^7+q^8).$$

This is the rational generating function of $R_3(n)$ with its denominator cleared.

Source: N. Guru Sharan, *Rook Decomposition of the Partition Function*,
Journal of Integer Sequences 29 (2026), Article 26.2.6, Theorem 2
(`jis-2026-26.2.6-thm-2`). -/
public theorem maxRookPartitionCount_three_genFun :
    (1 - X) ^ 3 * (1 + X + X ^ 2) * mk (fun n => (maxRookPartitionCount 3 n : ℤ)) =
      X ^ 6 * (1 + 2 * X + X ^ 2 + 2 * X ^ 3 - X ^ 4 - X ^ 6 - X ^ 7 + X ^ 8) := by
  rw [maxRookPartitionCount_three_genFun.enumerator_rankThree]
  exact maxRookPartitionCount_three_genFun.clearDenominator

end MetaMathlibExt
