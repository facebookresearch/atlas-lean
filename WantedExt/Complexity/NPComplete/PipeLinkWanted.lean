/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PIPE LINK is NP-complete

Source:
A. Uejima, H. Suzuki and A. Okada, "The Complexity of Generalized Pipe Link Puzzles",
Journal of Information Processing 25 (2017), 724-729, doi:10.2197/ipsjjip.25.724
(Section 1, rules (1)-(4), the Pipe Link Decision Problem and Theorem 1).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Prod

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PipeLink

/-!
# PIPE LINK is NP-complete

Pipe Link (Nikoli) is played on a rectangular grid `B` of `m × n` squares, some of which carry
pre-given lines, the clue pieces. Each piece is one of seven pipes: two straight pipes
(`I₁`, `I₂`), four corner pipes (`L₁`, …, `L₄`) and the cross pipe `X`. The player constructs a
single closed loop containing all the clue pieces by drawing one of the seven pipes in each
blank square so that (Uejima, Suzuki and Okada 2017):
1. a pipe must be placed in every blank square, which is a square without clue pieces;
2. no lines can be added to the squares with clue pieces;
3. `X` pipes represent the three-dimensional intersection of two straight lines;
4. the segments of the line loop run horizontally or vertically between the center points of
   orthogonally adjacent squares.

INSTANCE: a rectangular grid `B` of size `m × n`, with some squares having clue pieces.
QUESTION: is there an arrangement of pipes on the blank squares in `B` satisfying rules 1-4,
with all the lines forming a single closed loop?

The grid is given row by row: entry `j` of row `k` is `0` for a blank square, or the code of
its clue piece, with row `0` on top: `1` horizontal straight pipe (left and right), `2`
vertical straight pipe (up and down), `3` corner up-right, `4` corner right-down, `5` corner
down-left, `6` corner left-up, `7` cross pipe `X` (all four sides). `WellFormed` requires
`m, n ≥ 1`, rows of equal length, codes at most `7`, and no clue piece with a line leaving the
grid (by rule 4 such a line cannot be part of the loop).

Squares are `Fin m × Fin n`, orthogonally adjacent when adjacent in Mathlib's grid graph
`pathGraph m □ pathGraph n`. The loop is a closed walk `c` of the grid graph with no repeated
segment (`SimpleGraph.Walk.IsCircuit`); the pipe of a square consists of the segments of `c`
at that square, so every line lies on the loop. Rule 1 (with the clue pieces lying on the loop)
says every square is on the loop. Rule 2 says that at a clue square the segments of the loop
are exactly the sides of its piece. Rule 3: a square the loop passes twice holds an `X` pipe,
so both passes go straight through it; a square passed once holds a straight or a corner pipe.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the grid row by row, `0` for a blank square and `1`-`7` for a clue piece. -/
abbrev PipeLinkInstance := List (List ℕ)

/-- The number of rows. -/
def rows (i : PipeLinkInstance) : ℕ := i.length

/-- The number of columns (the length of the first row). -/
def cols (i : PipeLinkInstance) : ℕ := (i.headD []).length

/-- The entry of square `x`: `0` if blank, otherwise the code of its clue piece. -/
def piece (i : PipeLinkInstance) (x : Fin (rows i) × Fin (cols i)) : ℕ :=
  (i.getD x.1 []).getD x.2 0

/-- The grid graph on the squares: orthogonally adjacent squares are adjacent. -/
abbrev Grid (i : PipeLinkInstance) : SimpleGraph (Fin (rows i) × Fin (cols i)) :=
  SimpleGraph.pathGraph (rows i) □ SimpleGraph.pathGraph (cols i)

/-- Well-formedness: at least one row and one column, rows of equal length, codes at most
`7`, and no clue piece has a line leaving the grid (rule 4): no upward line in the top row, no
downward line in the bottom row, no leftward line in the first column and no rightward line in
the last column. -/
def WellFormed (i : PipeLinkInstance) : Prop :=
  0 < rows i ∧ 0 < cols i ∧ (∀ row ∈ i, row.length = cols i) ∧
    (∀ row ∈ i, ∀ p ∈ row, p ≤ 7) ∧
    ∀ x : Fin (rows i) × Fin (cols i),
      ((x.1 : ℕ) = 0 → piece i x ∉ [2, 3, 6, 7]) ∧
      ((x.1 : ℕ) + 1 = rows i → piece i x ∉ [2, 4, 5, 7]) ∧
      ((x.2 : ℕ) = 0 → piece i x ∉ [1, 5, 6, 7]) ∧
      ((x.2 : ℕ) + 1 = cols i → piece i x ∉ [1, 3, 4, 7])

/-- The piece with code `p` in square `v` has a line on the side of `v` facing the square `w`
(up, down, left or right of `v`). -/
def OpensToward {m n : ℕ} (p : ℕ) (v w : Fin m × Fin n) : Prop :=
  ((w.1 : ℕ) + 1 = v.1 ∧ w.2 = v.2 ∧ p ∈ [2, 3, 6, 7]) ∨
    ((v.1 : ℕ) + 1 = w.1 ∧ w.2 = v.2 ∧ p ∈ [2, 4, 5, 7]) ∨
    (w.1 = v.1 ∧ (w.2 : ℕ) + 1 = v.2 ∧ p ∈ [1, 5, 6, 7]) ∨
    (w.1 = v.1 ∧ (v.2 : ℕ) + 1 = w.2 ∧ p ∈ [1, 3, 4, 7])

/-- The closed walk `c` is a loop solving the instance: rules 1-3. -/
def Solves (i : PipeLinkInstance) {u : Fin (rows i) × Fin (cols i)} (c : (Grid i).Walk u u) :
    Prop :=
  -- 1. a pipe is placed in every blank square, and the clue pieces lie on the loop
  (∀ x, x ∈ c.support) ∧
  -- 2. at a clue square the loop uses exactly the sides of the clue piece
  (∀ x w, piece i x ≠ 0 → (Grid i).Adj x w →
    (s(x, w) ∈ c.edges ↔ OpensToward (piece i x) x w)) ∧
  -- 3. where the loop turns (consecutive segments `d`, `d'`, cyclically), it passes only once;
  -- a square passed twice is an `X` pipe crossed by two straight lines
  ∀ dd ∈ c.darts.zip (c.darts.rotate 1),
    ¬ ((dd.1.fst.1 : ℕ) + (dd.2.snd.1 : ℕ) = 2 * (dd.1.snd.1 : ℕ) ∧
        (dd.1.fst.2 : ℕ) + (dd.2.snd.2 : ℕ) = 2 * (dd.1.snd.2 : ℕ)) →
      c.support.tail.count dd.1.snd ≤ 1

/-- Some closed loop of the grid graph, with no repeated segment, solves the instance. -/
def PipeLinkFeasible (i : PipeLinkInstance) : Prop :=
  ∃ u, ∃ c : (Grid i).Walk u u, c.IsCircuit ∧ Solves i c

open Classical in
/-- PIPE LINK as a decision problem over bitstrings. -/
noncomputable def pipeLinkDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PipeLinkInstance) x with
  | some i => decide (WellFormed i ∧ PipeLinkFeasible i)
  | none => false

/-- **PIPE LINK is NP-complete.** Source: Uejima, Suzuki and Okada (2017), Theorem 1. -/
public theorem_wanted pipeLink_npComplete :
    pipeLinkDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L pipeLinkDec

end MetaMathlibExt.Complexity.NPComplete.PipeLink
