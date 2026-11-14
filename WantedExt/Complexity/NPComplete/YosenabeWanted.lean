/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# YOSENABE is NP-complete

Source:
C. Iwamoto, "Yosenabe is NP-complete", Journal of Information Processing 22(1) (2014), 40-43,
doi:10.2197/ipsjjip.22.40; rules as published by Nikoli (nikoli.co.jp, "Yosenabe").
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Prod

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Yosenabe

/-!
# YOSENABE is NP-complete

INSTANCE: a rectangular grid in which some cells are gray, two gray cells being connected when
they are adjacent vertically or horizontally (a set of connected gray cells is a gray area); some
gray areas are labelled with numbers, and some non-gray cells contain circles with numbers.
QUESTION: can arrows be drawn vertically or horizontally from all circles to gray areas so that
(i) the arrows do not bend and do not cross other circles or lines of other arrows, (ii) the
number of a labelled gray area equals the total of the numbers of the circles that enter it, and
(iii) at least one circle (arrow tip) enters each gray area?

The grid is given explicitly, row by row: each cell is `(k, a)` with `k = 0` an empty white cell,
`k = 1` a white cell with a circle numbered `a`, and `k = 2` a gray cell, labelled `a` if `a ≠ 0`.
Gray areas are the connected components of the gray cells in the grid graph
`pathGraph m □ pathGraph n` (`SameArea`). A solution gives every circle `x` the tip `tip x` of
its arrow, a gray cell in the same row or column; the arrow's line is the cells from `x`
(excluded) to `tip x` (included) (`OnArrow`). Following Nikoli's rules ("the tip of the arrow in a
grey cell", "they go straight to their grey area"), once the line reaches a gray cell it stays
on gray cells up to its tip (`GrayToTip`), so it enters exactly one gray area, the tip's, and
does not pass over another. No line contains a circle, and lines of different arrows share no
cell; in particular at most one arrow tip enters each gray cell, as the source notes.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the grid row by row; each cell is `(k, a)`: `k = 0` empty white, `k = 1` a circle
numbered `a`, `k = 2` gray, labelled `a` when `a ≠ 0`. -/
abbrev YosenabeInstance := List (List (ℕ × ℕ))

/-- The number of rows. -/
abbrev rows (i : YosenabeInstance) : ℕ := i.length

/-- The number of columns (the length of the first row). -/
abbrev cols (i : YosenabeInstance) : ℕ := (i.headD []).length

/-- The cells of the grid. -/
abbrev Cell (i : YosenabeInstance) := Fin (rows i) × Fin (cols i)

/-- The content `(k, a)` of a cell. -/
def cell (i : YosenabeInstance) (x : Cell i) : ℕ × ℕ := (i.getD x.1 []).getD x.2 (0, 0)

/-- The cell is gray. -/
def Gray (i : YosenabeInstance) (x : Cell i) : Prop := (cell i x).1 = 2

/-- The cell contains a circle. -/
def Circle (i : YosenabeInstance) (x : Cell i) : Prop := (cell i x).1 = 1

/-- Adjacent gray cells (sharing a side). -/
def GrayGraph (i : YosenabeInstance) : SimpleGraph (Cell i) :=
  SimpleGraph.fromRel fun x y =>
    (SimpleGraph.pathGraph (rows i) □ SimpleGraph.pathGraph (cols i)).Adj x y ∧ Gray i x ∧ Gray i y

/-- The gray cells `x` and `y` are in the same gray area. -/
def SameArea (i : YosenabeInstance) (x y : Cell i) : Prop :=
  Gray i x ∧ Gray i y ∧ (GrayGraph i).Reachable x y

/-- The cell `z` is on the line of the arrow from `x` to its tip `t` (in the same row or column as
`x`): between `x` (excluded) and `t` (included). -/
def OnArrow (i : YosenabeInstance) (x t z : Cell i) : Prop :=
  z ≠ x ∧
    ((z.1 = x.1 ∧ t.1 = x.1 ∧ min (x.2 : ℕ) t.2 ≤ z.2 ∧ (z.2 : ℕ) ≤ max (x.2 : ℕ) t.2) ∨
      (z.2 = x.2 ∧ t.2 = x.2 ∧ min (x.1 : ℕ) t.1 ≤ z.1 ∧ (z.1 : ℕ) ≤ max (x.1 : ℕ) t.1))

/-- Along the arrow from `x` to `t`, every cell from a gray cell `z` of the line to the tip is
gray: the line stays on gray cells from where it first reaches one to its tip. -/
def GrayToTip (i : YosenabeInstance) (x t : Cell i) : Prop :=
  ∀ z w, OnArrow i x t z → Gray i z → OnArrow i z t w → Gray i w

/-- Well-formedness of an instance: the grid has at least one row and one column, all rows have
the same length, every cell kind is `0`, `1` or `2`, every circle has a positive number, and each
gray area has at most one label. -/
def WellFormed (i : YosenabeInstance) : Prop :=
  0 < rows i ∧ 0 < cols i ∧ (∀ row ∈ i, row.length = cols i) ∧
    (∀ row ∈ i, ∀ e ∈ row, e.1 ≤ 2 ∧ (e.1 = 1 → 0 < e.2)) ∧
    ∀ g g', SameArea i g g' → (cell i g).2 ≠ 0 → (cell i g').2 ≠ 0 → g = g'

open Classical in
/-- Some arrows (tips `tip x` for the circles `x`) satisfy the rules: each tip is a gray cell in
the circle's row or column, the line stays on gray cells once it reaches one, no line contains a
circle, lines of different arrows share no cell, every labelled area receives circles whose
numbers sum to its label, and every area receives at least one circle. -/
def YosenabeFeasible (i : YosenabeInstance) : Prop :=
  ∃ tip : Cell i → Cell i,
    (∀ x, Circle i x → Gray i (tip x) ∧ ((tip x).1 = x.1 ∨ (tip x).2 = x.2) ∧
      GrayToTip i x (tip x) ∧ ∀ z, OnArrow i x (tip x) z → ¬ Circle i z) ∧
    (∀ x x', Circle i x → Circle i x' → x ≠ x' → ∀ z,
      ¬ (OnArrow i x (tip x) z ∧ OnArrow i x' (tip x') z)) ∧
    (∀ g, Gray i g → (cell i g).2 ≠ 0 →
      ∑ x ∈ Finset.univ.filter (fun x => Circle i x ∧ SameArea i (tip x) g), (cell i x).2 =
        (cell i g).2) ∧
    ∀ g, Gray i g → ∃ x, Circle i x ∧ SameArea i (tip x) g

open Classical in
/-- YOSENABE as a decision problem over bitstrings. -/
noncomputable def yosenabeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := YosenabeInstance) x with
  | some i => decide (WellFormed i ∧ YosenabeFeasible i)
  | none => false

/-- **YOSENABE is NP-complete.** Source: Iwamoto (2014). -/
public theorem_wanted yosenabe_npComplete :
    yosenabeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L yosenabeDec

end MetaMathlibExt.Complexity.NPComplete.Yosenabe
