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
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Prod
public import Mathlib.Logic.Relation

/-!
# YAGIT: definitions

Kiatchaipipat and Ruangwises (2025), Section 2.4: "In Yagit, we have a grid in which some cells
are filled with either a sheep or a wolf. Each grid intersection point may have a black dot.
The goal is to partition the grid into regions using any number of lines such that each region
must contain at least one sheep or at least one wolf, but not both. Each partition lines must
start and end at unique points on the border of the grid and may only turn 90 degrees at a
black dot, but they are not required to do so. The partition lines can intersect, but only
where there are no black dots. Not all of the black dots must be used." Janko's English rules:
"Divide the grid along the grid lines in regions. A region must contain either sheep or wolves
(but not both) and must not be empty. The border lines of the regions start and end on the
edges of the grid; may turn by 90° in black grid dots (but nowhere else) and may cross
themselves in any grid dot except the black ones." The paper proves Yagit NP-complete.

INSTANCE: an `m × n` grid whose squares are empty or hold a sheep or a wolf, and a set of black
dots on the grid points.
QUESTION: can the grid be divided into regions by lines along the grid lines as above?

Representation. The squares are given row by row (`0` empty, `1` sheep, `2` wolf), the black
dots as the `(m + 1) × (n + 1)` grid of points `(a, b)`, `a ≤ m`, `b ≤ n`, row by row; the
instance size is proportional to the area. Square `(r, c)` has corners `(r, c)` and
`(r + 1, c + 1)`. A unit segment `(true, a, b)` joins points `(a, b)` and `(a, b + 1)`, and
`(false, a, b)` joins `(a, b)` and `(a + 1, b)`; it is inner when it lies inside the grid
rather than on its border, i.e. it separates two squares (`wall`). The lines are given by the
set of inner segments they cover, a predicate `F` (segments on the border separate nothing).
A region is a connected component (`SimpleGraph.ConnectedComponent`) of Mathlib's grid graph
`pathGraph m □ pathGraph n` on the squares after deleting the edges between squares whose
common side is drawn. At an inner point the drawn segments are, as `PointRule` requires:
none; two collinear ones (a line passing); two perpendicular ones only at a black dot (a line
turning); all four only at a point without a black dot (two lines crossing). One or three
segments would make a line end inside the grid or branch, and four at a black dot would make
lines meet there. Lines are then the maximal chains of drawn segments in which consecutive
segments meet at an inner point and are collinear or meet at a black dot (`Linked`); such a
chain either reaches the border at both ends or closes up inside the grid, and the rules
require the former: every drawn segment is linked through a chain to a segment with an end on
the border (`LinesReachBorder`). A point on the border lies on at most one inner segment, so
different lines end at different points.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

Source:
N. Kiatchaipipat and S. Ruangwises, "NP-completeness proofs of puzzles using the T-metacell
framework", arXiv:2508.11570 (2025), Section 2.4;
puzzle rules: A. Janko and O. Janko, "Yagit", https://www.janko.at/Raetsel/Yagit/index.htm.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Yagit

/-- An instance `(A, D)`: the squares row by row (`0` empty, `1` sheep, `2` wolf) and the black
dots on the grid points row by row (`true` = black dot). -/
abbrev YagitInstance := List (List ℕ) × List (List Bool)

/-- The number of rows `m`. -/
def rows (i : YagitInstance) : ℕ := i.1.length

/-- The number of columns `n` (the length of the first row). -/
def cols (i : YagitInstance) : ℕ := (i.1.headD []).length

/-- The content of square `(r, c)`: `0` empty, `1` sheep, `2` wolf. -/
def animal (i : YagitInstance) (r c : ℕ) : ℕ := (i.1.getD r []).getD c 0

/-- The grid point `p` carries a black dot. -/
def IsDot (i : YagitInstance) (p : ℕ × ℕ) : Prop := (i.2.getD p.1 []).getD p.2 false = true

/-- A unit segment of the grid lines: `(true, a, b)` joins `(a, b)` and `(a, b + 1)`,
`(false, a, b)` joins `(a, b)` and `(a + 1, b)`. -/
abbrev Segment := Bool × ℕ × ℕ

/-- The two ends of a segment. -/
def ends (s : Segment) : List (ℕ × ℕ) :=
  if s.1 then [(s.2.1, s.2.2), (s.2.1, s.2.2 + 1)] else [(s.2.1, s.2.2), (s.2.1 + 1, s.2.2)]

/-- The grid point `p` lies inside the grid, off its border. -/
def IsInnerPoint (i : YagitInstance) (p : ℕ × ℕ) : Prop :=
  0 < p.1 ∧ p.1 < rows i ∧ 0 < p.2 ∧ p.2 < cols i

/-- The segment lies inside the grid and separates two squares. -/
def IsInner (i : YagitInstance) (s : Segment) : Prop :=
  if s.1 then 0 < s.2.1 ∧ s.2.1 < rows i ∧ s.2.2 < cols i
  else s.2.1 < rows i ∧ 0 < s.2.2 ∧ s.2.2 < cols i

/-- The segment is an inner segment drawn by the lines `F`. -/
def Drawn (i : YagitInstance) (F : Segment → Bool) (s : Segment) : Prop :=
  IsInner i s ∧ F s = true

/-- The common side of two squares `x` and `y` that share a side. -/
def wall (x y : ℕ × ℕ) : Segment :=
  if x.1 = y.1 then (false, x.1, max x.2 y.2) else (true, max x.1 y.1, x.2)

/-- The grid graph on the squares: squares sharing a side are adjacent. -/
abbrev Grid (i : YagitInstance) : SimpleGraph (Fin (rows i) × Fin (cols i)) :=
  SimpleGraph.pathGraph (rows i) □ SimpleGraph.pathGraph (cols i)

/-- The squares connected within a region: adjacent squares whose common side is not drawn. -/
def Regions (i : YagitInstance) (F : Segment → Bool) :
    SimpleGraph (Fin (rows i) × Fin (cols i)) :=
  (Grid i).deleteEdges
    {e | ∃ x y : Fin (rows i) × Fin (cols i), e = s(x, y) ∧ F (wall (x.1, x.2) (y.1, y.2))}

/-- The local rule at the grid point `p`, with `u`, `d`, `l`, `r` the segments above, below, to
the left and to the right of `p`: none is drawn; `u` and `d` only; `l` and `r` only; all four,
if `p` has no black dot; or exactly one of `u`, `d` and exactly one of `l`, `r`, if `p` has a
black dot. -/
def PointRule (i : YagitInstance) (F : Segment → Bool) (p : ℕ × ℕ) : Prop :=
  (¬ Drawn i F (false, p.1 - 1, p.2) ∧ ¬ Drawn i F (false, p.1, p.2) ∧
      ¬ Drawn i F (true, p.1, p.2 - 1) ∧ ¬ Drawn i F (true, p.1, p.2)) ∨
    (Drawn i F (false, p.1 - 1, p.2) ∧ Drawn i F (false, p.1, p.2) ∧
      ¬ Drawn i F (true, p.1, p.2 - 1) ∧ ¬ Drawn i F (true, p.1, p.2)) ∨
    (¬ Drawn i F (false, p.1 - 1, p.2) ∧ ¬ Drawn i F (false, p.1, p.2) ∧
      Drawn i F (true, p.1, p.2 - 1) ∧ Drawn i F (true, p.1, p.2)) ∨
    (¬ IsDot i p ∧ Drawn i F (false, p.1 - 1, p.2) ∧ Drawn i F (false, p.1, p.2) ∧
      Drawn i F (true, p.1, p.2 - 1) ∧ Drawn i F (true, p.1, p.2)) ∨
    (IsDot i p ∧ (Drawn i F (false, p.1 - 1, p.2) ↔ ¬ Drawn i F (false, p.1, p.2)) ∧
      (Drawn i F (true, p.1, p.2 - 1) ↔ ¬ Drawn i F (true, p.1, p.2)))

/-- Two drawn segments continue each other on one line: they are different and meet at an inner
point, where they are collinear or which carries a black dot (the line turns there). -/
def Linked (i : YagitInstance) (F : Segment → Bool) (s t : Segment) : Prop :=
  s ≠ t ∧ Drawn i F s ∧ Drawn i F t ∧
    ∃ p ∈ ends s, p ∈ ends t ∧ IsInnerPoint i p ∧ (s.1 = t.1 ∨ IsDot i p)

/-- Every line starts and ends on the border: from every drawn segment a chain of linked
segments leads to a segment with an end on the border. -/
def LinesReachBorder (i : YagitInstance) (F : Segment → Bool) : Prop :=
  ∀ s, Drawn i F s →
    ∃ t, Relation.ReflTransGen (Linked i F) s t ∧ ∃ p ∈ ends t, ¬ IsInnerPoint i p

/-- Every region contains a sheep or a wolf, but not both. -/
def RegionRule (i : YagitInstance) (F : Segment → Bool) : Prop :=
  ∀ C : (Regions i F).ConnectedComponent,
    (∃ x ∈ C.supp, animal i x.1 x.2 ≠ 0) ∧
      ¬ ((∃ x ∈ C.supp, animal i x.1 x.2 = 1) ∧ ∃ y ∈ C.supp, animal i y.1 y.2 = 2)

/-- Well-formedness: at least one row and one column, rows of equal length, entries at most `2`,
and a dot grid of `m + 1` rows of `n + 1` points. -/
def WellFormed (i : YagitInstance) : Prop :=
  0 < rows i ∧ 0 < cols i ∧ (∀ row ∈ i.1, row.length = cols i) ∧
    (∀ row ∈ i.1, ∀ a ∈ row, a ≤ 2) ∧
    i.2.length = rows i + 1 ∧ ∀ row ∈ i.2, row.length = cols i + 1

/-- Some lines satisfy the local rule at every inner point, start and end on the border, and
divide the grid into admissible regions. -/
def YagitFeasible (i : YagitInstance) : Prop :=
  ∃ F : Segment → Bool,
    (∀ p, IsInnerPoint i p → PointRule i F p) ∧ LinesReachBorder i F ∧ RegionRule i F

open Classical in
/-- YAGIT as a decision problem over bitstrings. -/
noncomputable def yagitDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := YagitInstance) x with
  | some i => decide (WellFormed i ∧ YagitFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.Yagit
