/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Powerset

/-!
# Weighted file placements on singleton boards

Statements from Kenny Barrese, *Weighted File Placements on Singleton Boards*, INTEGERS 24
(2024), Article A58. A Ferrers board is given by its weakly increasing list of column heights
`b = [b_1, …, b_n]`; cells are pairs `(column, row)`, both `0`-indexed, so column `i` holds the
rows `0, …, b_{i+1} - 1` and row `r` lies in level `r / m`. Polynomial identities are stated
for every integer `x`, which is equivalent for polynomials over `ℤ`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- The cells of the Ferrers board with column heights `b`: `(i, r)` with `i < n` and
`r < b_{i+1}` (`0`-indexed column `i`).

Source: Kenny Barrese, *Weighted File Placements on Singleton Boards*, INTEGERS 24 (2024),
Article A58, Section 2.1 (definition of the Ferrers board `B = (b_1, …, b_n)`). -/
def ferrersBoardCells (b : List ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range b.length) ×ˢ (Finset.range b.sum)).filter fun c => c.2 < b.getD c.1 0

/-- The board `B_1 = (1, 1, 2, 4)` of Figure 2 has `8` cells.

Source: Kenny Barrese, *Weighted File Placements on Singleton Boards*, INTEGERS 24 (2024),
Article A58, Figure 2. -/
theorem ferrersBoardCells_card_1124 : (ferrersBoardCells [1, 1, 2, 4]).card = 8 := by
  decide

/-- File placements on the board: sets of cells with no two in the same column.

Source: Kenny Barrese, *Weighted File Placements on Singleton Boards*, INTEGERS 24 (2024),
Article A58, Section 3.1 (definition of a file placement). -/
def filePlacements (b : List ℕ) : Finset (Finset (ℕ × ℕ)) :=
  (ferrersBoardCells b).powerset.filter fun F => (F.image Prod.fst).card = F.card

/-- `m`-level rook placements: file placements with no two cells in the same level (rows
`r` with the same `r / m`).

Source: Kenny Barrese, *Weighted File Placements on Singleton Boards*, INTEGERS 24 (2024),
Article A58, Section 2.2 (definition of `m`-level rook placements, after Briggs and Remmel). -/
def levelRookPlacements (m : ℕ) (b : List ℕ) : Finset (Finset (ℕ × ℕ)) :=
  (filePlacements b).filter fun F => (F.image fun c => c.2 / m).card = F.card

/-- The `k`-th `m`-level rook number `r_{k,m}(B)`.

Source: Kenny Barrese, *Weighted File Placements on Singleton Boards*, INTEGERS 24 (2024),
Article A58, Section 2.2. -/
def levelRookNumber (m : ℕ) (b : List ℕ) (k : ℕ) : ℕ :=
  ((levelRookPlacements m b).filter fun F => F.card = k).card

/-- The `m`-falling factorial `x↓_{k,m} = ∏_{i<k} (x - m i)`.

Source: Kenny Barrese, *Weighted File Placements on Singleton Boards*, INTEGERS 24 (2024),
Article A58, Section 2.2 (definition of the `m`-falling factorial). -/
def mFallingFactorial (x : ℤ) (k m : ℕ) : ℤ :=
  ∏ i ∈ Finset.range k, (x - m * i)

/-- `1↓_{3,2} = 1 · (-1) · (-3) = 3`.

Source: Kenny Barrese, *Weighted File Placements on Singleton Boards*, INTEGERS 24 (2024),
Article A58, Section 4 (value `1↓_{3,2} = 3` after Lemma 8). -/
theorem mFallingFactorial_one_three_two : mFallingFactorial 1 3 2 = 3 := by
  decide

/-- The `m`-weight `wt_m(F) = ∏_j 1↓_{f_j,m}` of a file placement, `f_j` the number of cells of `F`
in row `j` (rows without cells contribute `1`).

Source: Kenny Barrese, *Weighted File Placements on Singleton Boards*, INTEGERS 24 (2024),
Article A58, Section 3.1 (definition of `wt_m`). -/
def filePlacementWeight (m : ℕ) (F : Finset (ℕ × ℕ)) : ℤ :=
  ∏ j ∈ F.image Prod.snd, mFallingFactorial 1 (F.filter fun c => c.2 = j).card m

/-- The placement of Figure 4 (two rooks in the second row, three in the fourth) has
`3`-weight `-20`.

Source: Kenny Barrese, *Weighted File Placements on Singleton Boards*, INTEGERS 24 (2024),
Article A58, Figure 4 and the computation of `wt_3(F)`. -/
theorem filePlacementWeight_figure_four :
    filePlacementWeight 3 {(0, 1), (1, 1), (2, 3), (3, 3), (4, 3)} = -20 := by
  decide

/-- The `k`-th `m`-weighted file placement number `f_{k,m}(B) = Σ_{F ∈ 𝓕_k} wt_m(F)`.

Source: Kenny Barrese, *Weighted File Placements on Singleton Boards*, INTEGERS 24 (2024),
Article A58, Section 3.1. -/
def weightedFileNumber (m : ℕ) (b : List ℕ) (k : ℕ) : ℤ :=
  ∑ F ∈ (filePlacements b).filter (fun F => F.card = k), filePlacementWeight m F

/-- On the `2 × 2` board with `m = 2` there is no `2`-level rook placement of two rooks, and the
four two-rook file placements have `2`-weights `1, 1, -1, -1`.

Source: Kenny Barrese, *Weighted File Placements on Singleton Boards*, INTEGERS 24 (2024),
Article A58, Section 3.2 (cancellation of the weights of non-rook file placements). -/
theorem levelRookNumber_weightedFileNumber_two_two :
    levelRookNumber 2 [2, 2] 2 = 0 ∧ weightedFileNumber 2 [2, 2] 2 = 0 := by
  decide

/-- A singleton board for `m`: a Ferrers board (weakly increasing heights) such that
`b_i - ⌊b_i⌋_m ≠ 0` implies `⌊b_i⌋_m < ⌊b_{i+1}⌋_m` for consecutive columns, where `⌊b⌋_m` is the
largest multiple of `m` that is at most `b`.

Source: Kenny Barrese, *Weighted File Placements on Singleton Boards*, INTEGERS 24 (2024),
Article A58, Section 2.2 (definition of singleton boards). -/
def IsSingletonBoard (m : ℕ) (b : List ℕ) : Prop :=
  b.Pairwise (· ≤ ·) ∧ ∀ i < b.length - 1,
    b.getD i 0 % m ≠ 0 → b.getD i 0 / m * m < b.getD (i + 1) 0 / m * m

/-- `B = (1, 2, 2, 3)` is a singleton board for `m = 2` but not for `m = 3`.

Source: Kenny Barrese, *Weighted File Placements on Singleton Boards*, INTEGERS 24 (2024),
Article A58, Figure 3 and the discussion after it. -/
theorem isSingletonBoard_1223 :
    IsSingletonBoard 2 [1, 2, 2, 3] ∧ ¬ IsSingletonBoard 3 [1, 2, 2, 3] := by
  unfold IsSingletonBoard
  decide

/-- Goldman, Joichi and White: for a Ferrers board `B = (b_1, …, b_n)`,
`Σ_k r_k(B) x↓_{n-k} = ∏_i (x + b_i - (i - 1))`; here `r_k = r_{k,1}` and `x↓_k = x↓_{k,1}`, with
`0`-indexed columns.

Source: Kenny Barrese, *Weighted File Placements on Singleton Boards*, INTEGERS 24 (2024),
Article A58, Theorem 1 (Goldman, Joichi and White) (`integers-2024-A58-thm-1`). -/
public theorem_wanted rookNumber_factorization (b : List ℕ) (hb : b.Pairwise (· ≤ ·)) (x : ℤ) :
    ∑ k ∈ Finset.range (b.length + 1),
        (levelRookNumber 1 b k : ℤ) * mFallingFactorial x (b.length - k) 1 =
      ∏ i ∈ Finset.range b.length, (x + b.getD i 0 - i)

/-- Briggs and Remmel: for a singleton board `B = (b_1, …, b_n)` for `m ≥ 1`,
`p_m(B, x) = Σ_k r_{k,m}(B) x↓_{n-k,m} = ∏_i (x + b_i - m(i - 1))` (`0`-indexed columns).

Source: Kenny Barrese, *Weighted File Placements on Singleton Boards*, INTEGERS 24 (2024),
Article A58, Theorem 2 (Briggs and Remmel) (`integers-2024-A58-thm-2`). -/
public theorem_wanted levelRookNumber_factorization_of_singleton (m : ℕ) (hm : 1 ≤ m)
    (b : List ℕ) (hb : IsSingletonBoard m b) (x : ℤ) :
    ∑ k ∈ Finset.range (b.length + 1),
        (levelRookNumber m b k : ℤ) * mFallingFactorial x (b.length - k) m =
      ∏ i ∈ Finset.range b.length, (x + b.getD i 0 - m * i)

/-- Barrese, Loehr, Remmel and Sagan, zone form: for any Ferrers board and `m ≥ 1`,
`p_m(B, x) = ∏_i (x + ⌊b_i⌋_m - (i - 1)m + [i last in its zone z] ρ_z)`, where a zone is a maximal
run of columns with equal `⌊b_i⌋_m`, `ρ_i = b_i - ⌊b_i⌋_m` and `ρ_z = Σ_{k ∈ z} ρ_k`. Column `i` is
last in its zone when it is the last column or `⌊b_{i+1}⌋_m ≠ ⌊b_i⌋_m`; since the heights are
weakly increasing, the zone of `i` is the set of columns `k` with `⌊b_k⌋_m = ⌊b_i⌋_m`.

Source: Kenny Barrese, *Weighted File Placements on Singleton Boards*, INTEGERS 24 (2024),
Article A58, Theorem 3 (Barrese, Loehr, Remmel and Sagan) (`integers-2024-A58-thm-3`). -/
public theorem_wanted levelRookNumber_factorization_zones (m : ℕ) (hm : 1 ≤ m) (b : List ℕ)
    (hb : b.Pairwise (· ≤ ·)) (x : ℤ) :
    ∑ k ∈ Finset.range (b.length + 1),
        (levelRookNumber m b k : ℤ) * mFallingFactorial x (b.length - k) m =
      ∏ i ∈ Finset.range b.length,
        (x + (b.getD i 0 / m * m : ℕ) - m * i +
          if i + 1 = b.length ∨ b.getD (i + 1) 0 / m ≠ b.getD i 0 / m then
            ∑ k ∈ (Finset.range b.length).filter (fun k => b.getD k 0 / m = b.getD i 0 / m),
              ((b.getD k 0 % m : ℕ) : ℤ)
          else 0)

/-- Barrese, Loehr, Remmel and Sagan, level-number form: for a Ferrers board with `n` columns in
`Sq_{n,m}` (all heights at most `mn`) and `m ≥ 1`, `p_m(B, x) = ∏_j (x + l_j - m(j - 1))`, where
`l_j` is the number of cells in the `j`-th level from the top (`0`-indexed `j`: level index
`n - 1 - j` from the bottom). Hypothesis `b_i ≤ mn` makes the board lie in `n` levels, as in the
paper's setting; without it the formula fails (`m = 1`, `B = (2)`).

Source: Kenny Barrese, *Weighted File Placements on Singleton Boards*, INTEGERS 24 (2024),
Article A58, Theorem 4 (Barrese, Loehr, Remmel and Sagan) (`integers-2024-A58-thm-4`). -/
public theorem_wanted levelRookNumber_factorization_levels (m : ℕ) (hm : 1 ≤ m) (b : List ℕ)
    (hb : b.Pairwise (· ≤ ·)) (hbn : ∀ h ∈ b, h ≤ m * b.length) (x : ℤ) :
    ∑ k ∈ Finset.range (b.length + 1),
        (levelRookNumber m b k : ℤ) * mFallingFactorial x (b.length - k) m =
      ∏ j ∈ Finset.range b.length,
        (x + ((ferrersBoardCells b).filter fun c => c.2 / m = b.length - 1 - j).card - m * j)

/-- Barrese, Loehr, Remmel and Sagan: for any Ferrers board and `m ≥ 1`,
`Σ_k f_{k,m}(B) x↓_{n-k,m} = ∏_i (x + b_i - (i - 1)m)` (`0`-indexed columns).

Source: Kenny Barrese, *Weighted File Placements on Singleton Boards*, INTEGERS 24 (2024),
Article A58, Theorem 5 (Barrese, Loehr, Remmel and Sagan) (`integers-2024-A58-thm-5`). -/
public theorem_wanted weightedFileNumber_factorization (m : ℕ) (hm : 1 ≤ m) (b : List ℕ)
    (hb : b.Pairwise (· ≤ ·)) (x : ℤ) :
    ∑ k ∈ Finset.range (b.length + 1),
        weightedFileNumber m b k * mFallingFactorial x (b.length - k) m =
      ∏ i ∈ Finset.range b.length, (x + b.getD i 0 - m * i)

/-- For a singleton board for `m ≥ 1`, `f_{k,m}(B) = r_{k,m}(B)` for every `k`: the `m`-weights of
the file placements that are not `m`-level rook placements cancel. The printed corollary is the
polynomial identity `Σ_k f_{k,m}(B) x↓_{n-k,m} = Σ_k r_{k,m}(B) x↓_{n-k,m}`, which follows by
summing; the paper derives it from this per-`k` cancellation (`Σ_{F ∈ F'_k} wt_m(F) = 0`, stated
just before the corollary).

Source: Kenny Barrese, *Weighted File Placements on Singleton Boards*, INTEGERS 24 (2024),
Article A58, Corollary 6 and the sentence before it (`integers-2024-A58-cor-6`). -/
public theorem_wanted weightedFileNumber_eq_levelRookNumber_of_singleton (m : ℕ) (hm : 1 ≤ m)
    (b : List ℕ) (hb : IsSingletonBoard m b) (k : ℕ) :
    weightedFileNumber m b k = (levelRookNumber m b k : ℤ)

/-- The level `l` and cell `c₀` of Section 4 for a file placement `F₀`: among the levels holding at
least two cells of `F₀`, `l` holds the fewest (the lowest such level on ties), and `c₀` is the
leftmost cell of `F₀` in level `l`.

Source: Kenny Barrese, *Weighted File Placements on Singleton Boards*, INTEGERS 24 (2024),
Article A58, Section 4 (choice of the level `l` and its leftmost rook). -/
def IsChosenLevelAndLeftmost (m : ℕ) (F₀ : Finset (ℕ × ℕ)) (l : ℕ) (c₀ : ℕ × ℕ) : Prop :=
  2 ≤ (F₀.filter fun c => c.2 / m = l).card ∧
    (∀ l', 2 ≤ (F₀.filter fun c => c.2 / m = l').card →
      (F₀.filter fun c => c.2 / m = l).card < (F₀.filter fun c => c.2 / m = l').card ∨
        ((F₀.filter fun c => c.2 / m = l).card = (F₀.filter fun c => c.2 / m = l').card ∧
          l ≤ l')) ∧
    c₀ ∈ F₀ ∧ c₀.2 / m = l ∧ ∀ c ∈ F₀, c.2 / m = l → c₀.1 ≤ c.1

/-- The block `P(F₀)` of Section 4: file placements on `B` that agree with `F₀` outside level `l`,
use the same columns as `F₀` inside level `l`, and contain the leftmost rook `c₀` of level `l`;
every other rook of level `l` may sit in any cell of its column inside level `l`.

Source: Kenny Barrese, *Weighted File Placements on Singleton Boards*, INTEGERS 24 (2024),
Article A58, Section 4 (definition of `P(F₀)`). -/
def filePlacementBlock (m : ℕ) (b : List ℕ) (F₀ : Finset (ℕ × ℕ)) (l : ℕ) (c₀ : ℕ × ℕ) :
    Finset (Finset (ℕ × ℕ)) :=
  (filePlacements b).filter fun F =>
    F.filter (fun c => c.2 / m ≠ l) = F₀.filter (fun c => c.2 / m ≠ l) ∧
      (F.filter fun c => c.2 / m = l).image Prod.fst =
        (F₀.filter fun c => c.2 / m = l).image Prod.fst ∧
      c₀ ∈ F

/-- On a singleton board for `m ≥ 2`, if `F₀` is a file placement that is not an `m`-level rook
placement and its chosen level `l` contains `n` rooks, then `P(F₀)` has `m^{n-1}` members.

Source: Kenny Barrese, *Weighted File Placements on Singleton Boards*, INTEGERS 24 (2024),
Article A58, Lemma 7 (`integers-2024-A58-lem-7`). -/
public theorem_wanted filePlacementBlock_card (m : ℕ) (hm : 2 ≤ m) (b : List ℕ)
    (hb : IsSingletonBoard m b) (F₀ : Finset (ℕ × ℕ)) (hF₀ : F₀ ∈ filePlacements b)
    (hF₀r : F₀ ∉ levelRookPlacements m b) (l : ℕ) (c₀ : ℕ × ℕ)
    (hl : IsChosenLevelAndLeftmost m F₀ l c₀) (n : ℕ)
    (hn : (F₀.filter fun c => c.2 / m = l).card = n) :
    (filePlacementBlock m b F₀ l c₀).card = m ^ (n - 1)

/-- On a singleton board for `m ≥ 2`, if the chosen level `l` of `F₀` contains exactly two rooks,
the `m`-weights over `P(F₀)` (the rightmost rook of level `l` moving within its column and level)
sum to `0`.

Source: Kenny Barrese, *Weighted File Placements on Singleton Boards*, INTEGERS 24 (2024),
Article A58, Lemma 8 (`integers-2024-A58-lem-8`). -/
public theorem_wanted sum_filePlacementWeight_block_of_two (m : ℕ) (hm : 2 ≤ m) (b : List ℕ)
    (hb : IsSingletonBoard m b) (F₀ : Finset (ℕ × ℕ)) (hF₀ : F₀ ∈ filePlacements b)
    (l : ℕ) (c₀ : ℕ × ℕ) (hl : IsChosenLevelAndLeftmost m F₀ l c₀)
    (h2 : (F₀.filter fun c => c.2 / m = l).card = 2) :
    ∑ F ∈ filePlacementBlock m b F₀ l c₀, filePlacementWeight m F = 0

/-- On a singleton board for `m ≥ 2`, for every file placement `F₀` that is not an `m`-level rook
placement, the `m`-weights over its block `P(F₀)` sum to `0`.

Source: Kenny Barrese, *Weighted File Placements on Singleton Boards*, INTEGERS 24 (2024),
Article A58, Theorem 9 (`integers-2024-A58-thm-9`). -/
public theorem_wanted sum_filePlacementWeight_block (m : ℕ) (hm : 2 ≤ m) (b : List ℕ)
    (hb : IsSingletonBoard m b) (F₀ : Finset (ℕ × ℕ)) (hF₀ : F₀ ∈ filePlacements b)
    (hF₀r : F₀ ∉ levelRookPlacements m b) (l : ℕ) (c₀ : ℕ × ℕ)
    (hl : IsChosenLevelAndLeftmost m F₀ l c₀) :
    ∑ F ∈ filePlacementBlock m b F₀ l c₀, filePlacementWeight m F = 0

end

end MetaMathlibExt
