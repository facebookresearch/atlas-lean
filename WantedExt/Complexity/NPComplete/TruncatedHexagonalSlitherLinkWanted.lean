/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TRUNCATED HEXAGONAL SLITHER LINK is NP-complete

Source:
J. Kölker, "Selected Slither Link variants are NP-complete", Journal of Information
Processing 20(3) (2012), 709-712, doi:10.2197/ipsjjip.20.709, Theorem 1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.TruncatedHexagonalSlitherLinkDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TruncatedHexagonalSlitherLink

/-!
# TRUNCATED HEXAGONAL SLITHER LINK is NP-complete

Kölker (2012), Section 1: "Let `G = (V, E)` be a plane graph and `F_c` a set of faces in `G`,
the clues, and let `v : F_c → ℕ` be a function giving the clue values. The Slither Link decision
problem is this: decide whether there is a set of edges `C ⊆ E` such that `C` is a cycle and
such that for all faces `F ∈ F_c` the number of edges in `C` incident to `F` equals `v(F)`."
Section 4 restricts `G` to the "dodecahedron grid" (footnote 2: "More commonly known as the
truncated hexagonal tiling"): "draw the hex grid and replace each vertex with an equilateral
triangle, turning each hexagon into a regular dodecahedron. Equivalently, draw a row of
dodecahedrons next to one another with overlapping vertical edges; then, at each edge at
five-o'-clock, draw a dodecahedron with the same edge in the eleven-o'-clock position. If the
first row is `w` dodecahedrons wide and this row pair is repeated `h/2` times vertically
translated (plus a copy of the top row if `h` is odd), this is the dodecahedron grid graph"
(Fig. 1, `w = h = 2`; the paper's "dodecahedron" is a dodecagon). Theorem 1: "The
Dodecahedronal Slither Link decision problem is NP-complete." The reduction puts clues on
triangles, and on the single dodecagon of the `w = h = 1` grid ("the clue 12").

INSTANCE: integers `w, h ≥ 1` and a clue value for some of the faces (the `wh` dodecagons and
the triangles between them) of the truncated hexagonal grid with `h` rows of `w` dodecagons.
QUESTION: is there a cycle `C` in the grid such that every clue face has exactly as many of its
sides in `C` as its clue value?

Representation. The underlying hex grid has `h` rows of `w` hexagons with vertical left and
right sides, row `r + 1` shifted half a hexagon to the right of row `r` when `r` is even and to
the left when `r` is odd. Hexagon `c` of row `r` (both from `0`, left to right and top to
bottom) is the hexagon `(c, r)`; with `x₀ = 2c + r % 2`, its corners, clockwise from the top
left, are the points `p₀ = (x₀, r)`, `p₁ = (x₀ + 1, r)` (the top corner), `p₂ = (x₀ + 2, r)`,
`p₃ = (x₀ + 2, r + 1)`, `p₄ = (x₀ + 1, r + 1)` (the bottom corner) and `p₅ = (x₀, r + 1)` of
`ℕ × ℕ` (`y` downwards). So hexagons `(c, r)` and `(c + 1, r)` share a vertical side, and for
even `r` hexagon `(c, r + 1)` shares the five-o'clock side `p₄p₃` of `(c, r)`. Replacing each
hex vertex `p` by a triangle, the vertex of the truncated grid on the hex side from `p` to `q`
next to `p` is the pair `(p, q)`. Dodecagon `(c, r)` has the twelve sides
`(pₖ, pₖ₋₁)`-`(pₖ, pₖ₊₁)` (cutting the corner `pₖ`) and `(pₖ, pₖ₊₁)`-`(pₖ₊₁, pₖ)` (what is left
of the hex side `pₖpₖ₊₁`), indices mod 6. The grid is the `SimpleGraph` on pairs of points whose
edges are the sides of its `wh` dodecagons; other pairs are isolated vertices. The triangle at a
hex vertex `p = (x, y)` with hex neighbours `a = (x - 1, y)`, `b = (x + 1, y)` and `d`
(`(x, y + 1)` if `x + y` is even, `(x, y - 1)` if it is odd) has the sides `(p, a)`-`(p, b)`,
`(p, b)`-`(p, d)` and `(p, a)`-`(p, d)`; it is a face exactly when its three sides are edges of
the grid, that is, when the three hexagons around `p` are in the grid. The bounded faces are the
dodecagons and these triangles.

The clues are given as two grids, so the instance size is proportional to `wh`, matching the
unary encoding of `w` and `h` in the source: the dodecagon clues row by row, `w` entries per
row, and the triangle clues by hex vertex, `h + 1` rows `y = 0, …, h` of `2w + 2` entries
`x = 0, …, 2w + 1`; `0` means no clue and `v + 1` clue value `v`. A clue on a triangle that is not
a face makes the instance malformed. Clues sit on bounded faces, as in the reduction. A cycle
`C ⊆ E` is the edge set of a cycle `cyc` of the graph (`SimpleGraph.Walk.IsCycle`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **TRUNCATED HEXAGONAL SLITHER LINK is NP-complete.** Source: Kölker (2012), Theorem 1. -/
public theorem_wanted truncatedHexagonalSlitherLink_npComplete :
    truncatedHexagonalSlitherLinkDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L truncatedHexagonalSlitherLinkDec

end MetaMathlibExt.Complexity.NPComplete.TruncatedHexagonalSlitherLink
