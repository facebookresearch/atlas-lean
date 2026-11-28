/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NAGENAWA is NP-complete

Source:
L. T. Bordin, A. de A. S. Braga, B. A. de Mello and S. da S. Feitosa, "Nagenawa is
NP-complete", Journal of Information Processing 34 (2026), 112-120,
doi:10.2197/ipsjjip.34.112.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.NagenawaDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Nagenawa

/-!
# NAGENAWA is NP-complete

A Nagenawa board is a rectangular grid of cells separated into outlined regions, which may or
may not be numbered. The cells are filled with any number of rectangular loops, using horizontal
or vertical segments that go across the centers of the cells, so that:
1. a number in an outlined region is the exact amount of its cells that are crossed by
   rectangular loops;
2. rectangular loops may cross each other, but cannot share a corner or an edge;
3. every segment is part of a loop, and there are no loose ends.

INSTANCE: a rectangular grid separated into regions, some of them numbered.
QUESTION: can rectangular loops be drawn so that rules 1-3 hold?

A rectangular loop is `(r₁, c₁, r₂, c₂)` with `r₁ < r₂` and `c₁ < c₂` inside the grid: the
boundary of the rectangle whose corner cells are `(r₁, c₁)`, `(r₁, c₂)`, `(r₂, c₁)`, `(r₂, c₂)`
(rows `0, …, m - 1` top to bottom, columns `0, …, n - 1`). It crosses the cells of rows `r₁`
and `r₂` between columns `c₁` and `c₂` and the cells of columns `c₁` and `c₂` between rows
`r₁` and `r₂`; it turns at its four corner cells, and its edges are the unit segments joining
the centers of consecutive crossed cells. Rule 2 says that two distinct loops of a solution
have no common corner cell and no common unit segment, so a cell crossed by both is a crossing
of a horizontal and a vertical side. Rule 3 holds because a solution is a list of rectangular
loops. A region is outlined: its cells are connected through cells of the region sharing a side,
as in Mathlib's grid graph `pathGraph m □ pathGraph n` on `Fin m × Fin n`.

The instance lists the rows of the grid, top to bottom, where entry `c` of a row is the index of
the region containing that cell, and gives for each region `k` the pair `(numbered, number)`,
entry `k` of the second component. `WellFormed` requires at least one row and one column, rows
of equal length, region indices in range, every region connected (in particular nonempty), and
the number `0` stored for every unnumbered region (no ignored payload).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **NAGENAWA is NP-complete.** Source: Bordin, Braga, de Mello and Feitosa (2026). -/
public theorem_wanted nagenawa_npComplete :
    nagenawaDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L nagenawaDec

end MetaMathlibExt.Complexity.NPComplete.Nagenawa
