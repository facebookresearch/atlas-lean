/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# KAKURO (CROSS SUM) is NP-complete

Source:
T. Seta, "The complexities of puzzles, cross sum and their another solution problems (ASP)",
senior thesis, Department of Information Science, University of Tokyo (2002), Section 2.1;
T. Yato and T. Seta, "Complexity and completeness of finding another solution and its
application to puzzles", IEICE Transactions on Fundamentals of Electronics, Communications and
Computer Sciences E86-A(5) (2003), 1052-1060.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Prod

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Kakuro

/-!
# KAKURO (CROSS SUM) is NP-complete

Seta (2002), Section 2.1.1, defines the puzzle (Nikoli's Kakuro):

Input: a `W × H` board such that
1. "The board is made of white boxes and black boxes."
2. "Numbers called sum are given one for each vertical or horizontal line of white boxes. (And
   the numbers are put in the black boxes on the beginning of the white line.)"
3. "White boxes are connected, not separated by black boxes."
4. "Black boxes can be located next to each other not like CROSS WORD."
5. "Any line of white boxes has at least two white boxes."

Question: is there a setting of numbers in the white boxes such that
6. "Numbers in white boxes are from 1 to 9."
7. "The sum of numbers in one line is same to the given sum."
8. "Any number appears at most once in one white line."

Seta proves this NP-complete (Section 2.1); Yato and Seta (2003) prove its another-solution
problem ASP-complete, which implies NP-completeness.

Representation. The board is given row by row; a cell is a triple `(w, h, v)` with `w = true`
for a white box. A line is a maximal horizontal or vertical run of white boxes. Instead of
writing a line's sum in the black box before it, the sum is stored in the line's first white
box: `h` is the sum of the horizontal line that starts at this box and `v` that of the vertical
line, and both are `0` wherever no line starts (`WellFormed`). Thus each line carries exactly
one sum, and the representation also covers lines that start at the edge of the board. A box
starts a horizontal line when it is white and the box to its left is black or off the board
(`HStart`); the line consists of the white boxes from it to the right up to the next black box
or the edge (`hLen` boxes). Vertical lines are read downward in the same way. Clause 3 is
`SimpleGraph.Connected` (nonempty and preconnected) of the subgraph that Mathlib's grid graph
`pathGraph H □ pathGraph W` induces on the white boxes; clause 4 needs no condition; clause 5
says `2 ≤ hLen` and `2 ≤ vLen` at every line start. A setting is a function `ℕ → ℕ → ℕ` read
on the white boxes. The instance size is proportional to the area of the board plus the binary
length of the sums.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **KAKURO (CROSS SUM) is NP-complete.** Source: Seta (2002), Section 2.1; Yato and Seta
(2003). -/
public theorem_wanted kakuro_npComplete :
    kakuroDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L kakuroDec

end MetaMathlibExt.Complexity.NPComplete.Kakuro
