/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ALL OR NOTHING is NP-complete

Source:
P. Eua-anant, P. Apinyanon, T. Jirachaisri, N. Ruangsuksriwong and S. Ruangwises,
"NP-Completeness Proofs of All or Nothing, Water Walk, and Remembered Length Using the
T-Metacell Framework", arXiv:2510.21938 (2025), Section 2.1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.AllOrNothingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.AllOrNothing

/-!
# ALL OR NOTHING is NP-complete

All or Nothing (a pencil puzzle by Inaba Naoki) is played on a rectangular grid divided into
polyominoes called regions. Eua-anant et al. (Section 2.1) state its rules: draw a non-crossing
loop passing through orthogonally adjacent cells such that
1. if the loop visits a region, it passes through all cells in that region;
2. the loop enters and exits each region at most once;
3. two unvisited regions are not orthogonally adjacent.

INSTANCE: a rectangular grid divided into regions.
QUESTION: is there a loop satisfying rules 1-3? (Eua-anant et al. prove this NP-complete.)

The grid is given row by row: entry `c` of row `r` is the region of cell `(r, c)`; regions are
`0, …, R - 1`. `WellFormed` requires at least one row and one column, rows of equal length,
region indices below `R`, and every region a nonempty connected set of cells (a polyomino), as
in `MoonOrSunWanted`.

Cells are `Fin m × Fin n`, adjacent when they share a side in Mathlib's grid graph
`pathGraph m □ pathGraph n`. The loop is a cycle `c` of the grid graph
(`SimpleGraph.Walk.IsCycle`: at least three moves, no cell visited twice). Rule 1: a cell is on
the cycle whenever another cell of its region is. Rule 2: the cycle enters each region (moves
from a cell outside it to a cell inside it) at most once, as in `MoonOrSunWanted`; on a cycle
the exits from a region equal the entries. Rule 3: given rule 1, a region is unvisited exactly
when none of its cells is on the cycle, so for any two side-adjacent cells of different regions
at least one is on the cycle.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **ALL OR NOTHING is NP-complete.** Source: Eua-anant, Apinyanon, Jirachaisri,
Ruangsuksriwong and Ruangwises (2025), Section 2.1. -/
public theorem_wanted allOrNothing_npComplete :
    allOrNothingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L allOrNothingDec

end MetaMathlibExt.Complexity.NPComplete.AllOrNothing
