/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# KAKURO (CROSS SUM): definitions

Source:
T. Seta, "The complexities of puzzles, cross sum and their another solution problems (ASP)",
senior thesis, Department of Information Science, University of Tokyo (2002), Section 2.1;
T. Yato and T. Seta, "Complexity and completeness of finding another solution and its
application to puzzles", IEICE Transactions on Fundamentals of Electronics, Communications and
Computer Sciences E86-A(5) (2003), 1052-1060.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Prod

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Kakuro

/-- A box `(w, h, v)`: white if `w = true`; `h` and `v` are the sums of the horizontal and the
vertical line starting at this box (`0` where no line starts). -/
abbrev Box := Bool × ℕ × ℕ

/-- An instance: the board row by row. -/
abbrev KakuroInstance := List (List Box)

/-- The number of rows `H`. -/
def rows (i : KakuroInstance) : ℕ := i.length

/-- The number of columns `W` (the length of the first row). -/
def cols (i : KakuroInstance) : ℕ := (i.headD []).length

/-- The box in row `r` and column `c` (a black box without sums off the board). -/
def box (i : KakuroInstance) (r c : ℕ) : Box := (i.getD r []).getD c (false, 0, 0)

/-- The box in row `r` and column `c` is white. -/
def IsWhite (i : KakuroInstance) (r c : ℕ) : Prop := (box i r c).1 = true

/-- The box `(r, c)` starts a horizontal line: it is white and the box to its left is black or
off the board. -/
def HStart (i : KakuroInstance) (r c : ℕ) : Prop :=
  IsWhite i r c ∧ (c = 0 ∨ ¬ IsWhite i r (c - 1))

/-- The box `(r, c)` starts a vertical line: it is white and the box above it is black or off
the board. -/
def VStart (i : KakuroInstance) (r c : ℕ) : Prop :=
  IsWhite i r c ∧ (r = 0 ∨ ¬ IsWhite i (r - 1) c)

/-- The number of consecutive white boxes `(r, c), (r, c + 1), …` (the length of the horizontal
line starting at a line start). -/
def hLen (i : KakuroInstance) (r c : ℕ) : ℕ :=
  ((List.range (cols i)).takeWhile fun t => (box i r (c + t)).1).length

/-- The number of consecutive white boxes `(r, c), (r + 1, c), …` (the length of the vertical
line starting at a line start). -/
def vLen (i : KakuroInstance) (r c : ℕ) : ℕ :=
  ((List.range (rows i)).takeWhile fun t => (box i (r + t) c).1).length

/-- The numbers that the setting `f` puts in the horizontal line starting at `(r, c)`. -/
def hLine (i : KakuroInstance) (f : ℕ → ℕ → ℕ) (r c : ℕ) : List ℕ :=
  (List.range (hLen i r c)).map fun t => f r (c + t)

/-- The numbers that the setting `f` puts in the vertical line starting at `(r, c)`. -/
def vLine (i : KakuroInstance) (f : ℕ → ℕ → ℕ) (r c : ℕ) : List ℕ :=
  (List.range (vLen i r c)).map fun t => f (r + t) c

/-- The grid graph on the boxes: boxes sharing a side are adjacent. -/
abbrev Grid (i : KakuroInstance) : SimpleGraph (Fin (rows i) × Fin (cols i)) :=
  SimpleGraph.pathGraph (rows i) □ SimpleGraph.pathGraph (cols i)

/-- Well-formedness: a board with at least one row and one column and rows of equal length;
every line has at least two white boxes (clause 5); sums are stored only at line starts
(clause 2); there are white boxes and they are connected (clause 3). -/
def WellFormed (i : KakuroInstance) : Prop :=
  0 < rows i ∧ 0 < cols i ∧ (∀ row ∈ i, row.length = cols i) ∧
  (∀ r < rows i, ∀ c < cols i,
    (HStart i r c → 2 ≤ hLen i r c) ∧ (VStart i r c → 2 ≤ vLen i r c) ∧
    (¬ HStart i r c → (box i r c).2.1 = 0) ∧ (¬ VStart i r c → (box i r c).2.2 = 0)) ∧
  ((Grid i).induce {x | IsWhite i x.1 x.2}).Connected

/-- Some setting puts a number from `1` to `9` in every white box (clause 6) so that every line
sums to its sum (clause 7) and has no repeated number (clause 8). -/
def KakuroFeasible (i : KakuroInstance) : Prop :=
  ∃ f : ℕ → ℕ → ℕ,
    (∀ r < rows i, ∀ c < cols i, IsWhite i r c → 1 ≤ f r c ∧ f r c ≤ 9) ∧
    (∀ r < rows i, ∀ c < cols i, HStart i r c →
      (hLine i f r c).sum = (box i r c).2.1 ∧ (hLine i f r c).Nodup) ∧
    (∀ r < rows i, ∀ c < cols i, VStart i r c →
      (vLine i f r c).sum = (box i r c).2.2 ∧ (vLine i f r c).Nodup)

open Classical in
/-- KAKURO (CROSS SUM) as a decision problem over bitstrings. -/
noncomputable def kakuroDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := KakuroInstance) x with
  | some i => decide (WellFormed i ∧ KakuroFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.Kakuro
