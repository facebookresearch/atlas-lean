/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NURIMEIZU is NP-complete

Source:
C. Iwamoto and T. Ide, "Moon-or-Sun, Nagareru, and Nurimeizu are NP-complete", IEICE
Transactions on Fundamentals of Electronics, Communications and Computer Sciences E105-A
(2022), 1187-1194, doi:10.1587/transfun.2021DMP0006;
rules as restated by D. Miyahara, P. Lafourcade and M. Puys, "Card-based ZKP protocols for
connectivity-based puzzles: extending to tree structures with application to Nurimeizu",
FUN 2026, LIPIcs 366, 35, doi:10.4230/LIPIcs.FUN.2026.35, Section 2.1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.NurimeizuDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Nurimeizu

/-!
# NURIMEIZU is NP-complete

Nurimeizu is one of Nikoli's pencil puzzles; Iwamoto and Ide (2022) show that deciding whether a
given instance has a solution is NP-complete. Its rules, as restated by Miyahara, Lafourcade and
Puys (FUN 2026, Section 2.1, citing Iwamoto and Ide for NP-completeness): "Given an `m × n`
grid, the goal of Nurimeizu is to color certain cells based on the following rules: Create a
maze from the start (S) to the goal (G) across only white cells. Room: All cells within a room
(enclosed by bold lines) have to be either colored or left white. Tree: The set of all white
cells must form a tree structure (i.e., they must be connected and contain no cycles). Shortest
Path: There must exist a shortest path between S and G through white cells. The shortest path
include all ⃝-cells (circle) and no △-cell (triangle). In addition, rooms with S, G, ⃝, and △
are left white. Square of 2 × 2: No 2 × 2 area of cells can be entirely of the same color."
Their footnote: the word "shortest" can be omitted, because the white cells form a tree, in
which the path between two cells is unique.

The rooms are given by a grid of room labels, row by row (every row has the length of the first
row); a room is the set of cells with one label and must be connected (a region enclosed by bold
lines). S, G, the circles and the triangles are distinct cells. Cells are adjacent when they
share a side: the grid graph is the box product of two path graphs. A solution is the set `B` of
colored cells.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **NURIMEIZU is NP-complete.** Source: Iwamoto and Ide (2022); rules as restated by
Miyahara, Lafourcade and Puys (2026). -/
public theorem_wanted nurimeizu_npComplete :
    nurimeizuDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L nurimeizuDec

end MetaMathlibExt.Complexity.NPComplete.Nurimeizu
