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
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.PipeLinkDefs

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

/-- **PIPE LINK is NP-complete.** Source: Uejima, Suzuki and Okada (2017), Theorem 1. -/
public theorem_wanted pipeLink_npComplete :
    pipeLinkDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L pipeLinkDec

end MetaMathlibExt.Complexity.NPComplete.PipeLink
