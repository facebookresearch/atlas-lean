/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TRIANGULAR SLITHER LINK is NP-complete

Source:
J. Kölker, "Selected Slither Link variants are NP-complete", Journal of Information
Processing 20(3) (2012), 709-712, doi:10.2197/ipsjjip.20.709, Theorem 2.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.TriangularSlitherLinkDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TriangularSlitherLink

/-!
# TRIANGULAR SLITHER LINK is NP-complete

Kölker (2012), Section 1: "Let `G = (V, E)` be a plane graph and `F_c` a set of faces in `G`,
the clues, and let `v : F_c → ℕ` be a function giving the clue values. The Slither Link decision
problem is this: decide whether there is a set of edges `C ⊆ E` such that `C` is a cycle and
such that for all faces `F ∈ F_c` the number of edges in `C` incident to `F` equals `v(F)`."
Section 5 restricts `G` to a class of triangular grids: "A row of length `w` is `2w` triangles,
alternating between pointing down and up, overlapping in the non-horizontal edges. In a graph
with `h` rows, `h > 1`, each row is the horizontal mirror image of its predecessor"; the first
row starts with a down triangle (Fig. 2, `w = h = 6`). Theorem 2: "The Triangular Slither Link
decision problem is NP-complete."

INSTANCE: integers `w ≥ 1`, `h > 1` and a clue value for some of the `2wh` triangles of the
triangular grid with `h` rows of length `w`.
QUESTION: is there a cycle `C` in the grid such that every clue triangle has exactly as many of
its three sides in `C` as its clue value?

Representation. Vertex `(x, y)` is the `x`-th point (`0 ≤ x ≤ w`) on horizontal line `y`
(`0 ≤ y ≤ h`, top to bottom); line `y` is shifted half a unit to the right when `y` is odd.
Edges join consecutive points of a line, and point `(x, y)` to the two points of line `y + 1`
at distance one: `(x, y + 1)` and `(x - 1, y + 1)` if `y` is even, `(x, y + 1)` and
`(x + 1, y + 1)` if `y` is odd. Row `y` (between lines `y` and `y + 1`) consists of the
triangles `0, …, 2w - 1` from left to right; triangle `k` of row `y` points down when `y + k`
is even. The graph is a `SimpleGraph (ℕ × ℕ)` whose vertices off the grid are isolated. The
clues are given as the grid itself, row by row, `2w` entries per row: `0` for no clue and
`v + 1` for clue value `v`; so the instance size is proportional to `wh`, matching the unary
encoding of `w` and `h` in the source. Clues sit on the triangles, the bounded faces, as in the
reduction. A cycle `C ⊆ E` is the edge set of a cycle `c` of the graph
(`SimpleGraph.Walk.IsCycle`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **TRIANGULAR SLITHER LINK is NP-complete.** Source: Kölker (2012), Theorem 2. -/
public theorem_wanted triangularSlitherLink_npComplete :
    triangularSlitherLinkDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L triangularSlitherLinkDec

end MetaMathlibExt.Complexity.NPComplete.TriangularSlitherLink
