/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PEG SOLITAIRE (GENERALIZED HI-Q) is NP-complete

Source:
R. Uehara and S. Iwata, "Generalized Hi-Q is NP-complete", Transactions of the IEICE E73(2)
(1990), 270-273 (not available to us; the result is recorded by the next reference);
E. D. Demaine and R. A. Hearn, "Playing games with algorithms: algorithmic combinatorial game
theory", in Games of No Chance 3, MSRI Publications 56, Cambridge University Press (2009),
3-56, Section 5.10, arXiv:cs/0106019.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.PegSolitaireDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PegSolitaire

/-!
# PEG SOLITAIRE (GENERALIZED HI-Q) is NP-complete

Demaine and Hearn (2009), Section 5.10, "Peg Solitaire (Hi-Q)": "Each move jumps a peg over
another peg (adjacent horizontally or vertically) to the opposite unoccupied position within the
cross, and removes the peg that was jumped over. The goal is to leave just a single peg". "A
natural generalization of peg solitaire is to consider pegs arranged in an `n × n` board and the
goal is to leave a single peg. Uehara and Iwata [UI90] proved that it is NP-complete to decide
whether such a puzzle is solvable."

INSTANCE: an `n × n` board with pegs in some of its holes.
QUESTION: is there a sequence of jumps that leaves exactly one peg?

Representation. The board is given row by row (`true` = peg), so the instance size is
proportional to its area. A position is the finset of holes `(row, column)` that carry a peg.
A jump moves a peg from `x` over a peg on the next hole `y` in a row or column to the next hole
`z` beyond it in the same direction, which must be an empty hole of the board, and removes the
peg on `y`. Unlike peg solitaire on graphs (`PegSolitaireOnGraphsWanted`), a jump cannot turn:
`x`, `y`, `z` are consecutive holes of one row or one column. Pegs stay on the board, since
every jump lands on a hole of the board.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **PEG SOLITAIRE (GENERALIZED HI-Q) is NP-complete.** Source: Uehara and Iwata (1990), as
recorded by Demaine and Hearn (2009), Section 5.10. -/
public theorem_wanted pegSolitaire_npComplete :
    pegSolitaireDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L pegSolitaireDec

end MetaMathlibExt.Complexity.NPComplete.PegSolitaire
