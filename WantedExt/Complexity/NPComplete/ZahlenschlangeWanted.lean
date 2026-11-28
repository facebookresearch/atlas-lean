/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ZAHLENSCHLANGE is NP-complete

Source:
N. Kiatchaipipat and S. Ruangwises, "NP-completeness proofs of puzzles using the T-metacell
framework", arXiv:2508.11570 (2025), Section 2.3.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ZahlenschlangeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Zahlenschlange

/-!
# ZAHLENSCHLANGE is NP-complete

INSTANCE: a rectangular grid with a number in every cell.
QUESTION: is there a line from the top left cell to the bottom right cell, through orthogonally
adjacent cells and visiting no cell twice, on which every number of the grid appears exactly
once?

Kiatchaipipat and Ruangwises (Section 2.3): "In Zahlenschlange, a rectangular grid is filled
with numbers, not necessarily unique, and the goal is to draw a line from the top left corner to
the bottom right corner such that each unique number appears exactly once on the line." Their
cited rules page (A. and O. Janko, "Zahlenschlange", janko.at) adds: "The sections of the line
run horizontally or vertically between the centers of orthogonally adjacent cells. The line must
not visit a cell more than once." They prove the puzzle ASP-complete by a parsimonious
reduction, and a line is checked in polynomial time, so deciding solvability is NP-complete.

The cells of an `h × w` grid are `Fin h × Fin w`, adjacent when orthogonally neighboring (the
box product of two path graphs, as in `WantedExt.Complexity.NPComplete.EntryExitWanted`). A line
is a path of this graph (`SimpleGraph.Walk.IsPath`) from the cell `(0, 0)` to the cell
`(h - 1, w - 1)`; a number appears on the line once for each cell of the line holding it, and
the rule asks this count to be one for every number written in the grid. A one-cell grid has
the one-cell line.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **ZAHLENSCHLANGE is NP-complete.** Source: Kiatchaipipat and Ruangwises (2025),
Section 2.3. -/
public theorem_wanted zahlenschlange_npComplete :
    zahlenschlangeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L zahlenschlangeDec

end MetaMathlibExt.Complexity.NPComplete.Zahlenschlange
