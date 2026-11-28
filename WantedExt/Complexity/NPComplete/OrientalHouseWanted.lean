/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ORIENTAL HOUSE is NP-complete

Source:
H. Tang, "On the NP-Completeness of Satisfying Certain Path and Loop Puzzles",
arXiv:2004.12849 (2020), Section 1.3 (rules) and Section 3.4.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.OrientalHouseDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.OrientalHouse

/-!
# ORIENTAL HOUSE is NP-complete

Tang (2020), Section 1.3: in Oriental House the player is given a rectangular grid divided into
regions, including two one-cell regions labelled with `S` for Start and `F` for Finish. The aim
is to draw a directed orthogonal path from `S` to `F` passing through every cell exactly once.
Some orthogonal arrows have been given in some cells: if the path passes over an arrow on a
particular visit to a region, either it entered the region in that direction or will exit the
region in that direction on this visit.

INSTANCE: a rectangular grid divided into regions, with one-cell regions `S` and `F` and
orthogonal arrows in some cells.
QUESTION: is there a directed orthogonal path from `S` to `F` through every cell exactly once
satisfying the arrow rule? (Tang proves this NP-complete, Sections 2 and 3.4.)

The instance is `(S, F, grid)`: the cells `S` and `F` as `(row, column)`, and the grid row by
row, entry `j` of row `k` being `(region, arrow)` for the cell in row `k` and column `j`, with
arrow `0` (none), `1` (up), `2` (down), `3` (left) or `4` (right); row `0` is the top row.
Regions are the classes of cells with equal region index. `WellFormed` requires `m, n ≥ 1`,
rows of equal length, arrows at most `4`, `S` and `F` distinct cells of the grid, and the regions
of `S` and of `F` to contain no other cell. Tang's rules do not require regions to be
connected, and neither does this statement.

Cells are `Fin m × Fin n`, orthogonally adjacent when adjacent in Mathlib's grid graph
`pathGraph m □ pathGraph n`. The path is a walk from `S` to `F` visiting every cell exactly once
(`SimpleGraph.Walk.IsHamiltonian`); its cells in order are its support `q`. A visit to a region
is a maximal run `q[a], …, q[b]` of consecutive cells of the path in that region: the path
entered the region by the move `q[a - 1] → q[a]` (when `a > 0`) and exits it on this visit by
the move `q[b] → q[b + 1]` (when `q[b]` is not the last cell). The arrow rule asks, for each
cell `q[t]` with an arrow, that the visit containing position `t` entered or exits in the
direction of the arrow.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **ORIENTAL HOUSE is NP-complete.** Source: Tang (2020), Section 3.4. -/
public theorem_wanted orientalHouse_npComplete :
    orientalHouseDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L orientalHouseDec

end MetaMathlibExt.Complexity.NPComplete.OrientalHouse
