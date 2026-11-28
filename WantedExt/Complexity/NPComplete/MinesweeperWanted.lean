/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINESWEEPER CONSISTENCY is NP-complete

Source:
R. Kaye, "Minesweeper is NP-complete" (2000).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MinesweeperDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Minesweeper

/-!
# MINESWEEPER CONSISTENCY is NP-complete

A Minesweeper board: dimensions and a list of number clues `(row, column, number)`. The
question is whether there is a mine placement consistent with all clues: every clue cell is not
a mine and has exactly the indicated number of neighboring mines (among the eight surrounding
cells). Unrevealed cells may or may not contain mines; the clues need not come from a valid
board.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MINESWEEPER CONSISTENCY is NP-complete.** The Minesweeper consistency decision problem lies
in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Source: R. Kaye, "Minesweeper is NP-complete"
(2000). -/
public theorem_wanted minesweeper_npComplete :
    minesweeperDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minesweeperDec

end MetaMathlibExt.Complexity.NPComplete.Minesweeper
