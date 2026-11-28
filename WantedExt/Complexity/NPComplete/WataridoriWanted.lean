/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# WATARIDORI is NP-complete

Source:
S. Ruangwises, "Wataridori is NP-complete", arXiv:2601.09345 (2026),
https://arxiv.org/abs/2601.09345.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.WataridoriDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Wataridori

/-!
# WATARIDORI is NP-complete

Ruangwises (2026), Section 1: "The puzzle consists of a rectangular grid partitioned into
polyominoes called regions. (A polyomino is a shape formed by one or more unit squares connected
orthogonally.) Some cells contain a circle, and some of these circles contain a number. The
objective of Wataridori is to connect all circles into pairs using paths that go between
horizontally or vertically adjacent cells. Paths cannot cross or share a cell with one another.
The two circles connected by a path must contain the same number, which must be equal to the
total number of regions the path passes through. A path may enter and exit a region at most
once. Circles without numbers are treated as wildcards and may represent any number. ... it is
not required for all cells in the grid to be covered by paths."

INSTANCE: a rectangular grid partitioned into regions, with circles in some cells, some of them
numbered.
QUESTION: can all circles be connected in pairs by paths satisfying these rules?

Representation. The instance lists the number `R` of regions and the grid row by row: entry `c`
of row `r` is `(region, mark)` for cell `(r, c)`, with mark `0` (no circle), `1` (circle without
a number) or `v + 2` (circle with number `v`). `WellFormed` requires at least one row and one
column, rows of equal length, region indices below `R`, and every region a nonempty connected set
of cells (a polyomino). Cells are `Fin m × Fin n`, adjacent when they share a side in Mathlib's
grid graph `pathGraph m □ pathGraph n`. A solution is a list of paths, each a walk between two
distinct circle cells that is a path (`SimpleGraph.Walk.IsPath`); no cell lies on two paths
(the supports, concatenated, have no duplicates); and every circle is an end of some path. A
circle then lies on exactly one path, as one of its ends. For each path, every numbered end
carries the number of distinct regions among the path's cells, so two numbered ends carry the
same number; and the path enters each region at most once, counting its start as an entry into
the start's region (so a path never returns to a region it has left).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **WATARIDORI is NP-complete.** Source: Ruangwises (2026). -/
public theorem_wanted wataridori_npComplete :
    wataridoriDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L wataridoriDec

end MetaMathlibExt.Complexity.NPComplete.Wataridori
