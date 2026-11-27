/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Induction
import Mathlib.Tactic.Ring

/-!
# Weighted file placements on Ferrers boards

This module defines weighted file numbers and proves their factorization in the basis of
$m$-falling factorials by adjoining one column at a time.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Cells of a Ferrers board.** For a list $b = (b_1, \ldots, b_n)$ of natural numbers, the
cells of the Ferrers board with column heights $b$ are the pairs $(i, r)$ of natural numbers with
$i < n$ and $r < b_{i+1}$; columns and rows are numbered from $0$, so column $i$ has height
$b_{i+1}$.

Source: Kenny Barrese, *Weighted File Placements on Singleton Boards*, INTEGERS 24 (2024),
Article A58, Section 2.1 (definition of the Ferrers board `B = (b_1, …, b_n)`). -/
def ferrersBoardCells (b : List ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range b.length) ×ˢ (Finset.range b.sum)).filter fun c => c.2 < b.getD c.1 0

/-- **The board $(1, 1, 2, 4)$ has eight cells.** The Ferrers board with column heights
$(1, 1, 2, 4)$, the board $B_1$ of Figure 2, has exactly $8$ cells.

Source: Kenny Barrese, *Weighted File Placements on Singleton Boards*, INTEGERS 24 (2024),
Article A58, Figure 2. -/
theorem ferrersBoardCells_card_1124 : (ferrersBoardCells [1, 1, 2, 4]).card = 8 := by
  decide

/-- **File placements.** A file placement on the Ferrers board with column heights $b$ is a set of
cells of the board no two of which lie in the same column.

Source: Kenny Barrese, *Weighted File Placements on Singleton Boards*, INTEGERS 24 (2024),
Article A58, Section 3.1 (definition of a file placement). -/
def filePlacements (b : List ℕ) : Finset (Finset (ℕ × ℕ)) :=
  (ferrersBoardCells b).powerset.filter fun F => (F.image Prod.fst).card = F.card

/-- **Level rook placements.** Let $m$ be a natural number and let $B$ be the board with column
heights $b_1, \dots, b_n$, rows numbered from $0$, where row $r$ lies in level $\lfloor r/m \rfloor$
(every row lies in level $0$ when $m = 0$). An $m$-level rook placement on $B$ is a file placement
on $B$, that is a set of cells of $B$ with no two in the same column, that has no two cells in the
same level.

Source: Kenny Barrese, *Weighted File Placements on Singleton Boards*, INTEGERS 24 (2024),
Article A58, Section 2.2 (definition of `m`-level rook placements, after Briggs and Remmel). -/
def levelRookPlacements (m : ℕ) (b : List ℕ) : Finset (Finset (ℕ × ℕ)) :=
  (filePlacements b).filter fun F => (F.image fun c => c.2 / m).card = F.card

/-- **Level rook number.** Let $m$ and $k$ be natural numbers and let $B$ be the board with column
heights $b_1, \dots, b_n$, with rows numbered from $0$, where row $r$ lies in level
$\lfloor r/m \rfloor$ (every row lies in level $0$ when $m = 0$). The $k$-th $m$-level rook number
$r_{k,m}(B)$ is the number of $m$-level rook placements on $B$ with exactly $k$ cells, that is, of
sets of $k$ cells of $B$ with no two in the same column and no two in the same level.

Source: Kenny Barrese, *Weighted File Placements on Singleton Boards*, INTEGERS 24 (2024),
Article A58, Section 2.2. -/
def levelRookNumber (m : ℕ) (b : List ℕ) (k : ℕ) : ℕ :=
  ((levelRookPlacements m b).filter fun F => F.card = k).card

/-- **The $m$-falling factorial.** For an integer $x$ and natural numbers $k$ and $m$, the
$m$-falling factorial is the integer
$x\downarrow_{k,m} = \prod_{i=0}^{k-1} (x - mi) = x(x-m)\cdots(x-(k-1)m)$, which is $1$ for $k = 0$.

Source: Kenny Barrese, *Weighted File Placements on Singleton Boards*, INTEGERS 24 (2024),
Article A58, Section 2.2 (definition of the `m`-falling factorial). -/
def mFallingFactorial (x : ℤ) (k m : ℕ) : ℤ :=
  ∏ i ∈ Finset.range k, (x - m * i)

/-- **The value $1\downarrow_{3,2} = 3$.** The $2$-falling factorial of $1$ with three factors is
$1\downarrow_{3,2} = 1 \cdot (1 - 2) \cdot (1 - 4) = 3$.

Source: Kenny Barrese, *Weighted File Placements on Singleton Boards*, INTEGERS 24 (2024),
Article A58, Section 4 (value `1↓_{3,2} = 3` after Lemma 8). -/
theorem mFallingFactorial_one_three_two : mFallingFactorial 1 3 2 = 3 := by
  decide

/-- **The $m$-weight of a file placement.** For a natural number $m$ and a finite set $F$ of cells
$(i, j)$ (column $i$, row $j$), let $f_j$ be the number of cells of $F$ in row $j$. The $m$-weight
of $F$ is $\mathrm{wt}_m(F) = \prod_j 1\downarrow_{f_j, m}$, the product over the rows $j$ that
contain a cell of $F$, where $x\downarrow_{k, m} = \prod_{i < k} (x - m i)$ is the $m$-falling
factorial.

Source: Kenny Barrese, *Weighted File Placements on Singleton Boards*, INTEGERS 24 (2024),
Article A58, Section 3.1 (definition of `wt_m`). -/
def filePlacementWeight (m : ℕ) (F : Finset (ℕ × ℕ)) : ℤ :=
  ∏ j ∈ F.image Prod.snd, mFallingFactorial 1 (F.filter fun c => c.2 = j).card m

/-- **The $3$-weight of the placement of Figure 4.** The file placement $F$ consisting of the cells
$(0, 1)$, $(1, 1)$, $(2, 3)$, $(3, 3)$ and $(4, 3)$, written as (column, row) and numbered from
$0$, has two cells in the second row and three in the fourth, and its $3$-weight is
$\mathrm{wt}_3(F) = -20$.

Source: Kenny Barrese, *Weighted File Placements on Singleton Boards*, INTEGERS 24 (2024),
Article A58, Figure 4 and the computation of `wt_3(F)`. -/
theorem filePlacementWeight_figure_four :
    filePlacementWeight 3 {(0, 1), (1, 1), (2, 3), (3, 3), (4, 3)} = -20 := by
  decide

/-- **Weighted file placement numbers.** For a board $B$ given by a list of column heights and for
$m, k \in \mathbb{N}$, the $k$-th $m$-weighted file placement number of $B$ is the integer
$f_{k,m}(B) = \sum_F \mathrm{wt}_m(F)$, where $F$ runs over the file placements on $B$ with exactly
$k$ cells and $\mathrm{wt}_m(F)$ is the $m$-weight of $F$.

Source: Kenny Barrese, *Weighted File Placements on Singleton Boards*, INTEGERS 24 (2024),
Article A58, Section 3.1. -/
def weightedFileNumber (m : ℕ) (b : List ℕ) (k : ℕ) : ℤ :=
  ∑ F ∈ (filePlacements b).filter (fun F => F.card = k), filePlacementWeight m F

/-- **Two rooks on the $2 \times 2$ board with $m = 2$.** For the board $B = (2, 2)$, the number
$r_{2,2}(B)$ of $2$-level rook placements of two rooks on $B$ is $0$, and the weighted file
placement number $f_{2,2}(B)$, the sum of the $2$-weights of the file placements of two rooks
on $B$, is also $0$.

The four file placements of two rooks have $2$-weights $1, 1, -1, -1$, which cancel.

Source: Kenny Barrese, *Weighted File Placements on Singleton Boards*, INTEGERS 24 (2024),
Article A58, Section 3.2 (cancellation of the weights of non-rook file placements). -/
theorem levelRookNumber_weightedFileNumber_two_two :
    levelRookNumber 2 [2, 2] 2 = 0 ∧ weightedFileNumber 2 [2, 2] 2 = 0 := by
  decide

/-- **Singleton boards.** For natural numbers $h$ and $m$, write $\lfloor h \rfloor_m$ for the
largest multiple of $m$ that is at most $h$. A list $b = (b_1, \ldots, b_n)$ of natural numbers
is a singleton board for $m$ when it is weakly increasing (the column heights of a Ferrers board)
and, for every $1 \le i < n$, $b_i - \lfloor b_i \rfloor_m \ne 0$ implies
$\lfloor b_i \rfloor_m < \lfloor b_{i+1} \rfloor_m$.

Source: Kenny Barrese, *Weighted File Placements on Singleton Boards*, INTEGERS 24 (2024),
Article A58, Section 2.2 (definition of singleton boards). -/
def IsSingletonBoard (m : ℕ) (b : List ℕ) : Prop :=
  b.Pairwise (· ≤ ·) ∧ ∀ i < b.length - 1,
    b.getD i 0 % m ≠ 0 → b.getD i 0 / m * m < b.getD (i + 1) 0 / m * m

/-- **A singleton board for $2$ but not for $3$.** The Ferrers board with column heights
$(1, 2, 2, 3)$ is a singleton board for $m = 2$ and is not a singleton board for $m = 3$.

Source: Kenny Barrese, *Weighted File Placements on Singleton Boards*, INTEGERS 24 (2024),
Article A58, Figure 3 and the discussion after it. -/
theorem isSingletonBoard_1223 :
    IsSingletonBoard 2 [1, 2, 2, 3] ∧ ¬ IsSingletonBoard 3 [1, 2, 2, 3] := by
  unfold IsSingletonBoard
  decide

/-- **The chosen level and its leftmost cell.** Let $m$ be a natural number and $F_0$ a finite set
of cells $(i, r)$ (column $i$, row $r$), and call the rows $r$ with $\lfloor r/m \rfloor = l$
level $l$ (for $m = 0$, every row lies in level $0$). A level $l$ and a cell $c_0$ are chosen for
$F_0$ when level $l$ contains at least two cells of $F_0$; every level $l'$ containing at least
two cells of $F_0$ contains strictly more cells of $F_0$ than level $l$, or exactly as many with
$l \le l'$; and $c_0$ is a cell of $F_0$ in level $l$ whose column is at most the column of every
cell of $F_0$ in level $l$.

Source: Kenny Barrese, *Weighted File Placements on Singleton Boards*, INTEGERS 24 (2024),
Article A58, Section 4 (choice of the level `l` and its leftmost rook). -/
def IsChosenLevelAndLeftmost (m : ℕ) (F₀ : Finset (ℕ × ℕ)) (l : ℕ) (c₀ : ℕ × ℕ) : Prop :=
  2 ≤ (F₀.filter fun c => c.2 / m = l).card ∧
    (∀ l', 2 ≤ (F₀.filter fun c => c.2 / m = l').card →
      (F₀.filter fun c => c.2 / m = l).card < (F₀.filter fun c => c.2 / m = l').card ∨
        ((F₀.filter fun c => c.2 / m = l).card = (F₀.filter fun c => c.2 / m = l').card ∧
          l ≤ l')) ∧
    c₀ ∈ F₀ ∧ c₀.2 / m = l ∧ ∀ c ∈ F₀, c.2 / m = l → c₀.1 ≤ c.1

/-- **The block $P(F_0)$.** Let $B$ be the Ferrers board with column heights $b$, let $m$ and $l$
be natural numbers, and call the rows $r$ with $\lfloor r/m \rfloor = l$ level $l$ (for $m = 0$,
every row lies in level $0$). For a set $F_0$ of cells and a cell $c_0$, the block $P(F_0)$ is
the set of file placements $F$ on $B$ such that $F$ and $F_0$ have the same cells outside level
$l$, the cells of $F$ in level $l$ occupy exactly the same columns as the cells of $F_0$ in level
$l$, and $c_0 \in F$.

In Section 4, $l$ is the chosen level of $F_0$ and $c_0$ is the leftmost cell of $F_0$ in it.

Source: Kenny Barrese, *Weighted File Placements on Singleton Boards*, INTEGERS 24 (2024),
Article A58, Section 4 (definition of `P(F₀)`). -/
def filePlacementBlock (m : ℕ) (b : List ℕ) (F₀ : Finset (ℕ × ℕ)) (l : ℕ) (c₀ : ℕ × ℕ) :
    Finset (Finset (ℕ × ℕ)) :=
  (filePlacements b).filter fun F =>
    F.filter (fun c => c.2 / m ≠ l) = F₀.filter (fun c => c.2 / m ≠ l) ∧
      (F.filter fun c => c.2 / m = l).image Prod.fst =
        (F₀.filter fun c => c.2 / m = l).image Prod.fst ∧
      c₀ ∈ F

end

namespace weightedFileNumber_factorization

open Finset

private theorem mem_cells {b : List ℕ} {c : ℕ × ℕ} :
    c ∈ ferrersBoardCells b ↔ c.1 < b.length ∧ c.2 < b.getD c.1 0 := by
  simp only [ferrersBoardCells, mem_filter, mem_product, mem_range]
  refine ⟨fun h => ⟨h.1.1, h.2⟩, fun ⟨hi, hr⟩ => ⟨⟨hi, hr.trans_le ?_⟩, hr⟩⟩
  rw [b.getD_eq_getElem _ hi]
  exact List.le_sum_of_mem (List.getElem_mem hi)

private theorem mem_cells_append {b : List ℕ} {h : ℕ} {c : ℕ × ℕ} :
    c ∈ ferrersBoardCells (b ++ [h]) ↔
      c ∈ ferrersBoardCells b ∨ c.1 = b.length ∧ c.2 < h := by
  simp only [mem_cells, List.length_append, List.length_singleton]
  by_cases hi : c.1 < b.length
  · simp [hi, hi.ne, Nat.lt_succ_of_lt hi]
  · rw [b.getD_append_right [h] 0 _ (Nat.le_of_not_gt hi)]
    have hle : c.1 < b.length + 1 ↔ c.1 = b.length := by omega
    by_cases he : c.1 = b.length <;> simp [he, hi, hle]

private theorem mem_placements {b : List ℕ} {F : Finset (ℕ × ℕ)} :
    F ∈ filePlacements b ↔ F ⊆ ferrersBoardCells b ∧ Set.InjOn Prod.fst (F : Set (ℕ × ℕ)) := by
  simp [filePlacements, card_image_iff]

private theorem card_le_columns {b : List ℕ} {F : Finset (ℕ × ℕ)} (hF : F ∈ filePlacements b) :
    F.card ≤ b.length := by
  obtain ⟨hsub, hinj⟩ := mem_placements.mp hF
  rw [← card_image_iff.mpr hinj, ← card_range b.length]
  apply card_le_card
  exact image_subset_iff.mpr fun c hc => mem_range.mpr (mem_cells.mp (hsub hc)).1

private theorem sum_by_card (m : ℕ) (b : List ℕ) (v : ℕ → ℤ) :
    ∑ k ∈ range (b.length + 1), weightedFileNumber m b k * v k =
      ∑ F ∈ filePlacements b, filePlacementWeight m F * v F.card := by
  unfold weightedFileNumber
  simp_rw [sum_mul]
  rw [← sum_fiberwise_of_maps_to (g := Finset.card) (t := range (b.length + 1))
    (fun F hF => mem_range.mpr (Nat.lt_succ_of_le (card_le_columns hF)))
    (fun F => filePlacementWeight m F * v F.card)]
  exact sum_congr rfl fun k _ => sum_congr rfl fun F hF => by rw [(mem_filter.mp hF).2]

private def restrictCols (n : ℕ) (F : Finset (ℕ × ℕ)) := F.filter (fun c => c.1 < n)

private theorem col_lt {b : List ℕ} {F : Finset (ℕ × ℕ)} (hF : F ∈ filePlacements b)
    {c : ℕ × ℕ} (hc : c ∈ F) : c.1 < b.length :=
  (mem_cells.mp ((mem_placements.mp hF).1 hc)).1

private theorem restrict_mem {b : List ℕ} {h : ℕ} {G : Finset (ℕ × ℕ)}
    (hG : G ∈ filePlacements (b ++ [h])) : restrictCols b.length G ∈ filePlacements b := by
  obtain ⟨hsub, hinj⟩ := mem_placements.mp hG
  refine mem_placements.mpr ⟨fun c hc => ?_, hinj.mono (filter_subset _ G)⟩
  obtain ⟨hcG, hlt⟩ := mem_filter.mp hc
  exact (mem_cells_append.mp (hsub hcG)).resolve_right fun he => hlt.ne he.1

private theorem fiber_append {b : List ℕ} {h : ℕ} {F : Finset (ℕ × ℕ)}
    (hF : F ∈ filePlacements b) :
    (filePlacements (b ++ [h])).filter (fun G => restrictCols b.length G = F) =
      insert F ((range h).image fun r => insert (b.length, r) F) := by
  have hnew (r : ℕ) : (b.length, r) ∉ F := fun hc => (col_lt hF hc).false
  have hres : restrictCols b.length F = F := filter_eq_self.mpr fun _ => col_lt hF
  have hsub : F ⊆ ferrersBoardCells (b ++ [h]) :=
    fun _ hc => mem_cells_append.mpr (.inl ((mem_placements.mp hF).1 hc))
  ext G
  simp only [mem_filter, mem_insert, mem_image, mem_range]
  constructor
  · rintro ⟨hG, rfl⟩
    have hcell := (mem_placements.mp hG).1
    by_cases hex : ∃ r, (b.length, r) ∈ G
    · obtain ⟨r, hr⟩ := hex
      have hrlt : r < h := ((mem_cells_append.mp (hcell hr)).resolve_left
        (fun hc => (mem_cells.mp hc).1.false)).2
      refine Or.inr ⟨r, hrlt, Finset.ext fun c => ?_⟩
      simp only [mem_insert, restrictCols, mem_filter]
      constructor
      · rintro (rfl | hc)
        exacts [hr, hc.1]
      · intro hc
        rcases mem_cells_append.mp (hcell hc) with hold | hlast
        · exact Or.inr ⟨hc, (mem_cells.mp hold).1⟩
        · exact Or.inl ((mem_placements.mp hG).2 hc hr hlast.1)
    · left
      apply Eq.symm (filter_eq_self.mpr ?_)
      intro c hc
      apply (mem_cells.mp _).1
      exact (mem_cells_append.mp (hcell hc)).resolve_right fun he => hex ⟨c.2, he.1 ▸ hc⟩
  · rintro (rfl | ⟨r, hr, rfl⟩)
    · exact ⟨mem_placements.mpr ⟨hsub, (mem_placements.mp hF).2⟩, hres⟩
    · refine ⟨mem_placements.mpr ⟨?_, ?_⟩, ?_⟩
      · exact insert_subset (mem_cells_append.mpr (.inr ⟨rfl, hr⟩)) hsub
      · rw [coe_insert, Set.injOn_insert (hnew r)]
        exact ⟨(mem_placements.mp hF).2, fun ⟨c, hc, he⟩ => (col_lt hF hc).ne he⟩
      · simpa [restrictCols, filter_insert] using hres

private theorem sum_append (b : List ℕ) (h : ℕ) (v : Finset (ℕ × ℕ) → ℤ) :
    ∑ G ∈ filePlacements (b ++ [h]), v G =
      ∑ F ∈ filePlacements b, (v F + ∑ r ∈ range h, v (insert (b.length, r) F)) := by
  rw [← sum_fiberwise_of_maps_to (g := restrictCols b.length) (t := filePlacements b)
    (fun _ => restrict_mem) v]
  refine sum_congr rfl fun F hF => ?_
  have hnew (r : ℕ) : (b.length, r) ∉ F := fun hc => (col_lt hF hc).false
  rw [fiber_append hF, sum_insert, sum_image]
  · intro r _ s _ he
    have hc := mem_insert_self (b.length, r) F
    change insert (b.length, r) F = insert (b.length, s) F at he
    rw [he] at hc
    simpa [hnew] using hc
  · rintro hmem
    obtain ⟨r, _, he⟩ := mem_image.mp hmem
    exact hnew r (he ▸ mem_insert_self _ _)

private theorem falling_succ (x : ℤ) (k m : ℕ) :
    mFallingFactorial x (k + 1) m = mFallingFactorial x k m * (x - m * k) :=
  prod_range_succ _ _

private theorem weight_over_rows (m : ℕ) {F : Finset (ℕ × ℕ)} {h : ℕ}
    (hrows : ∀ c ∈ F, c.2 < h) :
    filePlacementWeight m F =
      ∏ r ∈ range h, mFallingFactorial 1 (F.filter fun c => c.2 = r).card m := by
  apply prod_subset (image_subset_iff.mpr fun c hc => mem_range.mpr (hrows c hc))
  intro r _ hr
  have he : (F.filter fun c => c.2 = r) = ∅ :=
    filter_eq_empty_iff.mpr fun c hc he => hr (he ▸ mem_image_of_mem Prod.snd hc)
  simp [he, mFallingFactorial]

private theorem weight_insert (m : ℕ) {F : Finset (ℕ × ℕ)} {h i r : ℕ}
    (hrows : ∀ c ∈ F, c.2 < h) (hr : r < h) (hf : (i, r) ∉ F) :
    filePlacementWeight m (insert (i, r) F) =
      filePlacementWeight m F * (1 - m * ((F.filter fun c => c.2 = r).card : ℤ)) := by
  have hrows' : ∀ c ∈ insert (i, r) F, c.2 < h := by
    intro c hc
    rcases mem_insert.mp hc with rfl | hc
    exacts [hr, hrows _ hc]
  rw [weight_over_rows m hrows', weight_over_rows m hrows,
    ← prod_ite_eq_of_mem' (range h) r (fun j => 1 - (m : ℤ) * (F.filter fun c => c.2 = j).card)
      (mem_range.mpr hr), ← prod_mul_distrib]
  refine prod_congr rfl fun j _ => ?_
  by_cases he : r = j
  · subst j
    have hf' : (i, r) ∉ F.filter (fun c => c.2 = r) := fun hc => hf (mem_filter.mp hc).1
    simp [filter_insert, hf', falling_succ]
  · simp [filter_insert, he, Ne.symm he]

private theorem sum_insert_weights (m : ℕ) {F : Finset (ℕ × ℕ)} {h i : ℕ}
    (hrows : ∀ c ∈ F, c.2 < h) (hnew : ∀ r, (i, r) ∉ F) :
    ∑ r ∈ range h, filePlacementWeight m (insert (i, r) F) =
      filePlacementWeight m F * (h - (m : ℤ) * F.card) := by
  have hcard := card_eq_sum_card_fiberwise (f := Prod.snd)
    (fun c hc => mem_range.mpr (hrows c hc))
  calc
    _ = ∑ r ∈ range h, filePlacementWeight m F *
          (1 - m * ((F.filter fun c => c.2 = r).card : ℤ)) :=
      sum_congr rfl fun r hr => weight_insert m hrows (mem_range.mp hr) (hnew r)
    _ = _ := by simp [← mul_sum, sum_sub_distrib, ← Nat.cast_sum, ← hcard]

-- Leaving the new column empty adds a falling-factorial factor. Occupying it
-- contributes the sum of the row weights, with every old rook counted once.
private theorem sum_extensions (m : ℕ) (x : ℤ) {b : List ℕ} {h : ℕ}
    (hmax : ∀ a ∈ b, a ≤ h) {F : Finset (ℕ × ℕ)} (hF : F ∈ filePlacements b) :
    filePlacementWeight m F * mFallingFactorial x (b.length + 1 - F.card) m +
        ∑ r ∈ range h, filePlacementWeight m (insert (b.length, r) F) *
          mFallingFactorial x (b.length + 1 - (insert (b.length, r) F).card) m =
      filePlacementWeight m F * mFallingFactorial x (b.length - F.card) m *
        (x + h - m * b.length) := by
  have hnew (r : ℕ) : (b.length, r) ∉ F := fun hc => (col_lt hF hc).false
  have hrows (c) (hc : c ∈ F) : c.2 < h := by
    obtain ⟨hi, hr⟩ := mem_cells.mp ((mem_placements.mp hF).1 hc)
    rw [b.getD_eq_getElem _ hi] at hr
    exact hr.trans_le (hmax _ (List.getElem_mem hi))
  have hk := card_le_columns hF
  simp only [card_insert_of_notMem (hnew _), Nat.add_sub_add_right]
  rw [← sum_mul, sum_insert_weights m hrows hnew,
    show b.length + 1 - F.card = b.length - F.card + 1 by omega, falling_succ,
    Nat.cast_sub hk]
  ring

end weightedFileNumber_factorization

section

open Finset weightedFileNumber_factorization

-- Any occupied column strictly to the right of a cell in level `l` is
-- complete in that level. If the left column stops there, the singleton
-- condition forces the next column to reach at least the end of the level.
private theorem level_full_to_right {m : ℕ} (hm : 0 < m) {b : List ℕ}
    (hb : IsSingletonBoard m b) {l : ℕ} {c : ℕ × ℕ}
    (hc : c ∈ ferrersBoardCells b) (hl : c.2 / m = l) {j : ℕ}
    (hij : c.1 < j) (hj : j < b.length) : (l + 1) * m ≤ b.getD j 0 := by
  have hmono {i : ℕ} (hi : i ≤ j) : b.getD i 0 ≤ b.getD j 0 := by
    rcases hi.eq_or_lt with rfl | hlt
    · rfl
    · rw [b.getD_eq_getElem _ (hlt.trans hj), b.getD_eq_getElem _ hj]
      exact List.pairwise_iff_getElem.mp hb.1 _ _ _ _ hlt
  have hlow : l * m < b.getD c.1 0 := by
    rw [← hl]
    exact (Nat.div_mul_le_self _ _).trans_lt (mem_cells.mp hc).2
  have hle := (Nat.le_div_iff_mul_le hm).2 hlow.le
  rcases hle.eq_or_lt with heq | hlt
  · have hrem : b.getD c.1 0 % m ≠ 0 := by
      intro hzero
      have h := Nat.div_add_mod (b.getD c.1 0) m
      rw [← heq, hzero, Nat.add_zero, Nat.mul_comm m l] at h
      exact hlow.ne h
    have hstep := hb.2 c.1 (by omega) hrem
    rw [← heq] at hstep
    exact ((Nat.le_div_iff_mul_le hm).1 (Nat.lt_of_mul_lt_mul_right hstep)).trans
      (hmono (by omega))
  · exact ((Nat.le_div_iff_mul_le hm).1 hlt).trans (hmono hij.le)

-- The chosen-level hypothesis already rules out a level rook placement.
-- Keep `hF₀r` in the original public signature.
set_option linter.unusedVariables false in
/-- **Size of the block $P(F_0)$.** Let $m \ge 2$, let $B$ be a singleton board for $m$, and call
the rows $r$ with $\lfloor r/m \rfloor = l$ level $l$. Let $F_0$ be a file placement on $B$ that is
not an $m$-level rook placement, let $l$ and $c_0$ be its chosen level and the leftmost cell of
$F_0$ in that level, and suppose level $l$ contains $n$ cells of $F_0$. Then the block $P(F_0)$
determined by $l$ and $c_0$ has exactly $m^{n-1}$ members.

Source: Kenny Barrese, *Weighted File Placements on Singleton Boards*, INTEGERS 24 (2024),
Article A58, Lemma 7 (`integers-2024-A58-lem-7`). -/
public theorem filePlacementBlock_card (m : ℕ) (hm : 2 ≤ m) (b : List ℕ)
    (hb : IsSingletonBoard m b) (F₀ : Finset (ℕ × ℕ)) (hF₀ : F₀ ∈ filePlacements b)
    (hF₀r : F₀ ∉ levelRookPlacements m b) (l : ℕ) (c₀ : ℕ × ℕ)
    (hl : IsChosenLevelAndLeftmost m F₀ l c₀) (n : ℕ)
    (hn : (F₀.filter fun c => c.2 / m = l).card = n) :
    (filePlacementBlock m b F₀ l c₀).card = m ^ (n - 1) := by
  classical
  obtain ⟨_, _, hc₀, hc₀l, hleft⟩ := hl
  obtain ⟨hboard, hinj⟩ := mem_placements.mp hF₀
  have hm₀ : 0 < m := by omega
  let L := F₀.filter fun c => c.2 / m = l
  let moving := L.erase c₀
  have hL : c₀ ∈ L := mem_filter.mpr ⟨hc₀, hc₀l⟩
  have moves {c : ℕ × ℕ} (hc : c ∈ moving) : c ≠ c₀ ∧ c ∈ F₀ ∧ c.2 / m = l := by
    obtain ⟨hne, hmem⟩ := mem_erase.mp hc
    exact ⟨hne, mem_filter.mp hmem⟩
  have hfull (c : moving) : (l + 1) * m ≤ b.getD c.1.1 0 := by
    obtain ⟨hne, hc, hcl⟩ := moves c.2
    have hlt := (hleft c hc hcl).lt_of_ne fun he => hne (hinj hc hc₀ he.symm)
    exact level_full_to_right hm₀ hb (hboard hc₀) hc₀l hlt (mem_cells.mp (hboard hc)).1
  -- Index the offsets by the original cells: their columns are distinct.
  let move (f : moving → Fin m) (c : ℕ × ℕ) : ℕ × ℕ :=
    if hc : c ∈ moving then (c.1, (f ⟨c, hc⟩ : ℕ) + l * m) else c
  have col (f : moving → Fin m) (c : ℕ × ℕ) : (move f c).1 = c.1 := by
    unfold move
    split <;> rfl
  have level (f : moving → Fin m) (c : ℕ × ℕ) : (move f c).2 / m = c.2 / m := by
    by_cases hc : c ∈ moving
    · simp [move, hc, (moves hc).2.2, Nat.add_mul_div_right _ _ hm₀,
        Nat.div_eq_of_lt (f ⟨c, hc⟩).isLt]
    · simp [move, hc]
  have fixed (f : moving → Fin m) {c : ℕ × ℕ} (hc : c.2 / m ≠ l) : move f c = c :=
    dite_eq_right fun h => hc (moves h).2.2
  have count : (univ : Finset (moving → Fin m)).card = (filePlacementBlock m b F₀ l c₀).card := by
    refine card_nbij (fun f => F₀.image (move f)) (fun f _ => ?_) (fun f _ g _ he => ?_)
      (fun F hF => ?_)
    · change F₀.image (move f) ∈ filePlacementBlock m b F₀ l c₀
      refine mem_filter.mpr ⟨mem_placements.mpr ⟨?_, ?_⟩, ?_, ?_, ?_⟩
      · intro d hd
        obtain ⟨c, hc, rfl⟩ := mem_image.mp hd
        by_cases h : c ∈ moving
        · have hr := (f ⟨c, h⟩).isLt
          have hlt := hfull ⟨c, h⟩
          refine mem_cells.mpr ⟨by simpa only [col] using (mem_cells.mp (hboard hc)).1, ?_⟩
          simp only [move, dite_eq_left h]
          rw [Nat.add_mul, Nat.one_mul, Nat.add_comm (l * m)] at hlt
          exact (Nat.add_lt_add_right hr _).trans_le hlt
        · simpa [move, h] using hboard hc
      · intro d hd e he hde
        obtain ⟨c, hc, rfl⟩ := mem_image.mp hd
        obtain ⟨a, ha, rfl⟩ := mem_image.mp he
        exact congrArg (move f) (hinj hc ha (by simpa only [col] using hde))
      · simp only [filter_image, level]
        exact (image_congr fun _ hc => fixed f (mem_filter.mp hc).2).trans image_id'
      · simp [filter_image, level, image_image, Function.comp_def, col]
      · exact mem_image.mpr ⟨c₀, hc₀, by simp [move, moving]⟩
    · change F₀.image (move f) = F₀.image (move g) at he
      funext c
      have hc := mem_image_of_mem (move f) (moves c.2).2.1
      rw [he] at hc
      obtain ⟨d, hd, hd'⟩ := mem_image.mp hc
      have hdc := hinj hd (moves c.2).2.1 (by simpa only [col] using congrArg Prod.fst hd')
      subst d
      apply Fin.ext
      exact Nat.add_right_cancel (by
        simpa only [move, dite_eq_left c.2] using congrArg Prod.snd hd'.symm)
    · obtain ⟨hF, hout, hcols, hfix⟩ := mem_filter.mp hF
      have hFinj := (mem_placements.mp hF).2
      have existsCell (c : moving) : ∃ d ∈ F, d.1 = c.1.1 ∧ d.2 / m = l := by
        have hc : c.1 ∈ L := (mem_erase.mp c.2).2
        have hcol := mem_image_of_mem Prod.fst hc
        rw [← hcols] at hcol
        obtain ⟨d, hd, hdcol⟩ := mem_image.mp hcol
        exact ⟨d, (mem_filter.mp hd).1, hdcol, (mem_filter.mp hd).2⟩
      choose d hd hdcol hdl using existsCell
      let f (c : moving) : Fin m := ⟨(d c).2 % m, Nat.mod_lt _ hm₀⟩
      have hmove (c : ℕ × ℕ) (hc : c ∈ F₀) : move f c ∈ F := by
        by_cases hv : c ∈ moving
        · have heq : move f c = d ⟨c, hv⟩ := by
            apply Prod.ext
            · exact (col f c).trans (hdcol ⟨c, hv⟩).symm
            · simp only [move, dite_eq_left hv, f]
              rw [Nat.mul_comm l m, ← hdl ⟨c, hv⟩]
              exact Nat.mod_add_div _ _
          exact heq ▸ hd ⟨c, hv⟩
        · rw [show move f c = c from dite_eq_right hv]
          by_cases hcl : c.2 / m = l
          · have heq : c = c₀ := by
              by_contra hne
              exact hv (mem_erase.mpr ⟨hne, mem_filter.mpr ⟨hc, hcl⟩⟩)
            exact heq ▸ hfix
          · have hc' : c ∈ F₀.filter (fun a => a.2 / m ≠ l) := mem_filter.mpr ⟨hc, hcl⟩
            rw [← hout] at hc'
            exact (mem_filter.mp hc').1
      refine ⟨f, mem_univ _, le_antisymm (image_subset_iff.mpr hmove) ?_⟩
      intro e he
      by_cases hel : e.2 / m = l
      · have he' : e ∈ F.filter (fun a => a.2 / m = l) := mem_filter.mpr ⟨he, hel⟩
        have hecol := mem_image_of_mem Prod.fst he'
        rw [hcols] at hecol
        obtain ⟨c, hc, hce⟩ := mem_image.mp hecol
        have hc' := (mem_filter.mp hc).1
        exact mem_image.mpr ⟨c, hc', hFinj (hmove c hc') he ((col f c).trans hce)⟩
      · have he' : e ∈ F.filter (fun a => a.2 / m ≠ l) := mem_filter.mpr ⟨he, hel⟩
        rw [hout] at he'
        exact mem_image.mpr ⟨e, (mem_filter.mp he').1, fixed f hel⟩
  rw [← count, card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe,
    card_erase_of_mem hL, hn]

end

open weightedFileNumber_factorization in
/-- **Factorization theorem for weighted file placements.** Let $m \ge 1$ and let $B$ be a Ferrers
board with $n$ columns of weakly increasing heights $b_0 \le b_1 \le \dots \le b_{n-1}$ (columns
indexed from $0$). Then for every integer $x$,
$$\sum_{k=0}^{n} f_{k,m}(B)\, x\downarrow_{n-k,m} = \prod_{i=0}^{n-1} (x + b_i - mi),$$
where $f_{k,m}(B)$ is the $k$-th $m$-weighted file placement number of $B$ and
$x\downarrow_{j,m} = \prod_{i<j} (x - mi)$ is the $m$-falling factorial.

Source: Kenny Barrese, *Weighted File Placements on Singleton Boards*, INTEGERS 24 (2024),
Article A58, Theorem 5 (Barrese, Loehr, Remmel and Sagan) (`integers-2024-A58-thm-5`). -/
public theorem weightedFileNumber_factorization (m : ℕ) (_hm : 1 ≤ m) (b : List ℕ)
    (hb : b.Pairwise (· ≤ ·)) (x : ℤ) :
    ∑ k ∈ Finset.range (b.length + 1),
        weightedFileNumber m b k * mFallingFactorial x (b.length - k) m =
      ∏ i ∈ Finset.range b.length, (x + b.getD i 0 - m * i) := by
  rw [sum_by_card]
  induction b using List.reverseRecOn with
  | nil =>
    have hempty : filePlacements [] = {∅} := by decide
    simp [hempty, filePlacementWeight, mFallingFactorial]
  | append_singleton b h ih =>
    obtain ⟨hb, _, hmax⟩ := List.pairwise_append.mp hb
    simp only [List.mem_singleton, forall_eq] at hmax
    simp only [List.length_append, List.length_singleton]
    rw [sum_append, Finset.prod_range_succ, List.getD_append_right _ _ _ _ le_rfl]
    simp only [Nat.sub_self, List.getD_cons_zero]
    calc
      _ = ∑ F ∈ filePlacements b, filePlacementWeight m F *
            mFallingFactorial x (b.length - F.card) m * (x + h - m * b.length) :=
        Finset.sum_congr rfl fun F hF => sum_extensions m x hmax hF
      _ = _ := by
        rw [← Finset.sum_mul, ih hb]
        congr 1
        exact Finset.prod_congr rfl fun i hi => by
          rw [b.getD_append [h] 0 i (Finset.mem_range.mp hi)]

end MetaMathlibExt
