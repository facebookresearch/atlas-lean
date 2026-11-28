/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAISU is NP-complete

Source:
H. Tang, "On the NP-completeness of satisfying certain path and loop puzzles",
arXiv:2004.12849 (2020), Sections 1.2, 2 and 3;
puzzle rules: TheGreatEscaper, "HAISU (Room Count): An original grid-logic challenge",
Puzzling Stack Exchange, https://puzzling.stackexchange.com/q/48029/.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.HaisuDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Haisu

/-!
# HAISU is NP-complete

Tang (Section 1.2): "the player is given a rectangular grid divided into regions, including two
one-cell regions labelled with S for Start and F for Finish. The aim is to draw a directed
orthogonal path from S to F passing through every cell exactly once. Some numbers have been
given in the cells. A path may enter a region once or multiple times, if this is the `n`th time
the path enters the region, it may only pass over [blank] cells or instances of the number
`n`." (The printed "black cells" are the cells without a number; the puzzle's author states the
rule as "When your path passes over a cell with the big number `N`, it must be the `N`th time
you have entered the room.") Tang proves the puzzle NP-complete (Section 2, membership; Section
3, hardness).

INSTANCE: a rectangular grid of cells, each in a region and possibly carrying a positive number,
with a start cell `S` and a finish cell `F`, each the only cell of its region.
QUESTION: is there a path from `S` to `F` through orthogonally adjacent cells that passes
through every cell exactly once, such that whenever it passes over a cell with number `N`, the
current visit to that cell's region is the `N`th time the path has entered the region?

The grid is given row by row: entry `c` of row `r` is `(region, number, mark)` for cell
`(r, c)`, with number `0` for no number and mark `1` for `S`, `2` for `F`, `0` otherwise.
`WellFormed` requires at least one row and one column, rows of equal length, marks at most `2`,
exactly one cell marked `S` and one marked `F`, and each of them the only cell of its region.
Regions are arbitrary labels and need not be connected: this class contains the instances of
Tang's construction, so hardness transfers, and the membership argument does not use
connectivity.
Cells are `Fin m × Fin n`, adjacent in Mathlib's grid graph `pathGraph m □ pathGraph n`, and the
path is a Hamiltonian walk (`SimpleGraph.Walk.IsHamiltonian`) from `S` to `F`. Mathlib defines
`p.IsHamiltonian` as `∀ a, p.support.count a = 1`: every cell occurs exactly once in the walk, so
a walk that revisits a cell is excluded and the walk is a path
(`SimpleGraph.Walk.IsHamiltonian.isPath`). At step `t` the
path is at `c.getVert t`; the visits to a region `k` up to step `t` are the start (if `S` is in
`k`) and the moves among the first `t` that go from a cell outside `k` to a cell inside `k`. The
author's optional room-count clues (a small number giving the total number of entries into a
room) are not used in Tang's reduction and are not part of this statement.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **HAISU is NP-complete.** Source: Tang (2020). -/
public theorem_wanted haisu_npComplete :
    haisuDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L haisuDec

end MetaMathlibExt.Complexity.NPComplete.Haisu
