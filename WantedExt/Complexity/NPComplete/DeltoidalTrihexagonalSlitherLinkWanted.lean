/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DELTOIDAL TRIHEXAGONAL SLITHER LINK is NP-complete

Source:
J. Kölker, "Selected Slither Link variants are NP-complete", Journal of Information
Processing 20(3) (2012), 709-712, doi:10.2197/ipsjjip.20.709, Theorem 4.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.DeltoidalTrihexagonalSlitherLinkDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DeltoidalTrihexagonalSlitherLink

/-!
# DELTOIDAL TRIHEXAGONAL SLITHER LINK is NP-complete

Kölker (2012), Section 1: "Let `G = (V, E)` be a plane graph and `F_c` a set of faces in `G`,
the clues, and let `v : F_c → ℕ` be a function giving the clue values. The Slither Link decision
problem is this: decide whether there is a set of edges `C ⊆ E` such that `C` is a cycle and
such that for all faces `F ∈ F_c` the number of edges in `C` incident to `F` equals `v(F)`."
Section 7 restricts `G` to the "dual graph class" (footnote 4: "More commonly known as the
deltoidal trihexagonal tiling"), which "arises from superimposing [the triangular and hexagonal
grids] on one another; that is, by adding vertices in the center of hexagons and connecting
them to the centers of neighbouring hexagons, also adding a vertex when the connecting line
intersects the edge between the connected hexagons. ... The particular structure we look at is
a grid of `h` rows, each containing `w` hexagons—similar to the hexagonal grid, but rotated
90°." In Fig. 10 (`w = h = 3`) the hexagons have a corner at the top, the second row starts to
the southeast of the first, and every hexagon of the grid, boundary hexagons included, is cut
into six kites by the segments from its center to the midpoints of its six sides (footnote 5
calls two hexagons of kites without clues "empty hexagons"). Theorem 4: "The Dual Slither Link
decision problem is NP-complete."

INSTANCE: integers `w, h ≥ 1` and a clue value for some of the `6wh` kites of the deltoidal
trihexagonal grid with `h` rows of `w` hexagons.
QUESTION: is there a cycle `C` in the grid such that every clue kite has exactly as many of its
four sides in `C` as its clue value?

Representation. Hexagon `c` of row `r` (both from `0`, left to right and top to bottom) is the
hexagon `(c, r)`; row `r + 1` is shifted half a hexagon to the right of row `r` when `r` is even
and to the left when `r` is odd. Vertices are labelled by pairs in `ℕ × ℕ`. The labels are
combinatorial, not a metric embedding: they follow the brick-wall model of the hexagonal grid
(each hexagon drawn as a `2 × 1` brick whose top and bottom sides each have a middle corner, the
first coordinate growing to the right and the second downwards), at doubled resolution so that
side midpoints and centers get labels too. With `x₀ = 2c + r % 2`, the six corners of hexagon
`(c, r)`, in cyclic order starting at the top left corner, are labelled `P₀ = (2x₀, 2r)`,
`P₁ = (2x₀ + 2, 2r)` (the top corner), `P₂ = (2x₀ + 4, 2r)`, `P₃ = (2x₀ + 4, 2r + 2)`,
`P₄ = (2x₀ + 2, 2r + 2)` (the bottom corner) and `P₅ = (2x₀, 2r + 2)`; the midpoint of the
side `PₖPₖ₊₁` is labelled `Mₖ` (`M₀ = (2x₀ + 1, 2r)`, `M₁ = (2x₀ + 3, 2r)`,
`M₂ = (2x₀ + 4, 2r + 1)`, `M₃ = (2x₀ + 3, 2r + 2)`, `M₄ = (2x₀ + 1, 2r + 2)`,
`M₅ = (2x₀, 2r + 1)`), and its center `Z = (2x₀ + 2, 2r + 1)`. Distinct points of the grid get
distinct labels.
So hexagons `(c, r)` and `(c + 1, r)` share the vertical side `P₂P₃` of `(c, r)`, and for even
`r` hexagon `(c, r + 1)` shares the side `P₃P₄` of `(c, r)`. Kite `k` of hexagon `(c, r)` is the
kite at the corner `Pₖ`, with the four sides `Z`-`Mₖ₋₁`, `Mₖ₋₁`-`Pₖ`, `Pₖ`-`Mₖ` and `Mₖ`-`Z`
(indices mod 6). The grid is the `SimpleGraph (ℕ × ℕ)` whose edges are the sides of the kites of
its `wh` hexagons; other points are isolated vertices. Its bounded faces are the kites. The
clues are given as the grid itself, row by row, `w` hexagons per row and `6` kite entries
`k = 0, …, 5` per hexagon: `0` for no clue and `v + 1` for clue value `v`; so the instance size
is proportional to `wh`, matching the unary encoding of `w` and `h` in the source. Clues sit on
the kites, the bounded faces, as in the reduction. A cycle `C ⊆ E` is the edge set of a cycle
`cyc` of the graph (`SimpleGraph.Walk.IsCycle`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **DELTOIDAL TRIHEXAGONAL SLITHER LINK is NP-complete.** Source: Kölker (2012),
Theorem 4. -/
public theorem_wanted deltoidalTrihexagonalSlitherLink_npComplete :
    deltoidalTrihexagonalSlitherLinkDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L deltoidalTrihexagonalSlitherLinkDec

end MetaMathlibExt.Complexity.NPComplete.DeltoidalTrihexagonalSlitherLink
