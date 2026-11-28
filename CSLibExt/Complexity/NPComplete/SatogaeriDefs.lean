/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Prod
public import Mathlib.Data.Nat.Dist

/-!
# SATOGAERI: definitions

Satogaeri (Nikoli) is played on a rectangular grid divided by bold lines into regions
("countries"); some cells hold a circle, possibly with a number. Nikoli's rules (translated):
1. Move each circle straight, vertically or horizontally, so that every region bounded by bold
   lines contains exactly one circle.
2. The number in a circle is the number of cells it moves. For a circle without a number, how
   many cells it moves is not known; it may also not move.
3. A circle cannot move onto the track of another circle's move or onto a place where another
   circle is.

INSTANCE: a rectangular grid divided into regions, with some cells holding a circle (with or
without a number). QUESTION: can the circles be moved according to rules 1-3? (Kanehiro and
Takenaga 2015 prove this NP-complete; their full text was not available, so the rules follow
Nikoli's rules page.)

The grid is given row by row: entry `c` of row `r` is `(region, clue)` for cell `(r, c)`, with
clue `0` (no circle), `1` (circle without a number) or `d + 2` (circle with number `d`); regions
are `0, …, R - 1`. `WellFormed` requires at least one row and one column, rows of equal length,
region indices below `R`, and every region a nonempty connected set of cells (the region a
closed bold boundary encloses).

Cells are `Fin m × Fin n`. A solution sends each circle `x` to its destination `D x`, in the
row or the column of `x` (`D x = x` when it does not move); its track is the segment of cells
from `x` to `D x`, and it moves `|D x - x|` cells. Rule 3 says that the tracks of two different
circles, each including its start and end cell, are disjoint: a circle neither moves across or
onto another circle's track nor across or onto another circle's start or end cell. Rule 1 says
that every region contains the destination of exactly one circle.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

Source:
S. Kanehiro and Y. Takenaga, "Satogaeri, Hebi, and Suraromu are NP-complete", 2015 3rd
International Conference on Applied Computing and Information Technology / 2nd International
Conference on Computational Science and Intelligence (ACIT-CSI 2015), IEEE,
doi:10.1109/ACIT-CSI.2015.17;
puzzle rules: Nikoli Co., Ltd., "Satogaeri" (Japanese rules page),
https://www.nikoli.co.jp/ja/puzzles/satogaeri/.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Satogaeri

/-- An instance: the number of regions `R`, and the grid row by row, each cell
`(region, clue)` with clue `0` (no circle), `1` (circle without a number) or `d + 2` (circle
with number `d`). -/
abbrev SatogaeriInstance := ℕ × List (List (ℕ × ℕ))

/-- The number of rows. -/
def rows (i : SatogaeriInstance) : ℕ := i.2.length

/-- The number of columns (the length of the first row). -/
def cols (i : SatogaeriInstance) : ℕ := (i.2.headD []).length

/-- A cell of the grid. -/
abbrev Cell (i : SatogaeriInstance) := Fin (rows i) × Fin (cols i)

/-- The entry `(region, clue)` of cell `x`. -/
def cell (i : SatogaeriInstance) (x : Cell i) : ℕ × ℕ :=
  (i.2.getD x.1 []).getD x.2 (0, 0)

/-- The grid graph on the cells: cells sharing a side are adjacent. -/
abbrev Grid (i : SatogaeriInstance) : SimpleGraph (Cell i) :=
  SimpleGraph.pathGraph (rows i) □ SimpleGraph.pathGraph (cols i)

/-- Well-formedness: at least one row and one column, rows of equal length, region indices
below `R`, and every region a nonempty connected set of cells. -/
def WellFormed (i : SatogaeriInstance) : Prop :=
  0 < rows i ∧ 0 < cols i ∧ (∀ row ∈ i.2, row.length = cols i) ∧
    (∀ row ∈ i.2, ∀ e ∈ row, e.1 < i.1) ∧
    ∀ k < i.1, ((Grid i).induce {x | (cell i x).1 = k}).Connected

/-- Cell `z` lies on the track from `x` to `y` (cells of a common row or column): the segment
of cells between them, both included. -/
def OnTrack {i : SatogaeriInstance} (x y z : Cell i) : Prop :=
  (z.1 = x.1 ∧ y.1 = x.1 ∧ min x.2 y.2 ≤ z.2 ∧ z.2 ≤ max x.2 y.2) ∨
    (z.2 = x.2 ∧ y.2 = x.2 ∧ min x.1 y.1 ≤ z.1 ∧ z.1 ≤ max x.1 y.1)

/-- The destinations `D` satisfy rules 1-3. -/
def Solves (i : SatogaeriInstance) (D : Cell i → Cell i) : Prop :=
  -- each circle moves straight: its destination is in its row or its column
  (∀ x, (cell i x).2 ≠ 0 → (D x).1 = x.1 ∨ (D x).2 = x.2) ∧
  -- 2. a circle with number `d` moves exactly `d` cells
  (∀ x, 2 ≤ (cell i x).2 →
    Nat.dist x.1 (D x).1 + Nat.dist x.2 (D x).2 = (cell i x).2 - 2) ∧
  -- 3. the tracks of different circles are disjoint
  (∀ x y, (cell i x).2 ≠ 0 → (cell i y).2 ≠ 0 → x ≠ y →
    ∀ z, ¬ (OnTrack x (D x) z ∧ OnTrack y (D y) z)) ∧
  -- 1. every region contains the destination of exactly one circle
  ∀ k < i.1, ∃! x, (cell i x).2 ≠ 0 ∧ (cell i (D x)).1 = k

/-- Some destinations of the circles satisfy the rules. -/
def SatogaeriFeasible (i : SatogaeriInstance) : Prop :=
  ∃ D : Cell i → Cell i, Solves i D

open Classical in
/-- SATOGAERI as a decision problem over bitstrings. -/
noncomputable def satogaeriDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SatogaeriInstance) x with
  | some i => decide (WellFormed i ∧ SatogaeriFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.Satogaeri
