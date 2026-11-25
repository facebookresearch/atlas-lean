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
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Paths

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

/-- An instance: the dodecagon clue grid (row `r`, entry `c` for dodecagon `(c, r)`) and the
triangle clue grid (row `y`, entry `x` for the triangle at hex vertex `(x, y)`); `0` for no
clue and `v + 1` for clue value `v`. -/
abbrev TruncatedHexagonalSlitherLinkInstance := List (List ℕ) × List (List ℕ)

/-- A vertex of the truncated grid: the pair `(p, q)` is the vertex on the hex side from `p` to
`q` next to `p`. -/
abbrev Point := (ℕ × ℕ) × (ℕ × ℕ)

/-- The number of rows `h`. -/
def height (i : TruncatedHexagonalSlitherLinkInstance) : ℕ := i.1.length

/-- The number `w` of dodecagons in each row (the length of the first row). -/
def width (i : TruncatedHexagonalSlitherLinkInstance) : ℕ := (i.1.headD []).length

/-- The clue entry of dodecagon `(c, r)`. -/
def dodecagonClue (i : TruncatedHexagonalSlitherLinkInstance) (c r : ℕ) : ℕ :=
  (i.1.getD r []).getD c 0

/-- The clue entry of the triangle at hex vertex `(x, y)`. -/
def triangleClue (i : TruncatedHexagonalSlitherLinkInstance) (x y : ℕ) : ℕ :=
  (i.2.getD y []).getD x 0

/-- The twelve sides of dodecagon `(c, r)`, obtained from hexagon `(c, r)` with corners
`p₀, …, p₅`: for each `k`, the side cutting the corner `pₖ` and the rest of the hex side
`pₖpₖ₊₁`. -/
def dodecagonSides (c r : ℕ) : List (Sym2 Point) :=
  let x₀ := 2 * c + r % 2
  let p₀ := (x₀, r)
  let p₁ := (x₀ + 1, r)
  let p₂ := (x₀ + 2, r)
  let p₃ := (x₀ + 2, r + 1)
  let p₄ := (x₀ + 1, r + 1)
  let p₅ := (x₀, r + 1)
  [s((p₀, p₅), (p₀, p₁)), s((p₀, p₁), (p₁, p₀)),
    s((p₁, p₀), (p₁, p₂)), s((p₁, p₂), (p₂, p₁)),
    s((p₂, p₁), (p₂, p₃)), s((p₂, p₃), (p₃, p₂)),
    s((p₃, p₂), (p₃, p₄)), s((p₃, p₄), (p₄, p₃)),
    s((p₄, p₃), (p₄, p₅)), s((p₄, p₅), (p₅, p₄)),
    s((p₅, p₄), (p₅, p₀)), s((p₅, p₀), (p₀, p₅))]

/-- The three sides of the triangle at hex vertex `p = (x, y)`, whose hex neighbours are
`(x - 1, y)`, `(x + 1, y)` and `(x, y + 1)` or `(x, y - 1)` as `x + y` is even or odd. -/
def triangleSides (p : ℕ × ℕ) : List (Sym2 Point) :=
  let a := (p.1 - 1, p.2)
  let b := (p.1 + 1, p.2)
  let d := if (p.1 + p.2) % 2 = 0 then (p.1, p.2 + 1) else (p.1, p.2 - 1)
  [s((p, a), (p, b)), s((p, b), (p, d)), s((p, a), (p, d))]

/-- The truncated hexagonal grid with `h` rows of `w` dodecagons: two vertices are adjacent
when they are the ends of a side of one of its dodecagons. -/
def Graph (i : TruncatedHexagonalSlitherLinkInstance) : SimpleGraph Point :=
  SimpleGraph.fromRel fun u v => ∃ c < width i, ∃ r < height i, s(u, v) ∈ dodecagonSides c r

/-- Well-formedness: `h ≥ 1` rows of `w ≥ 1` dodecagon clue entries, `h + 1` rows of `2w + 2`
triangle clue entries, and clues only on triangles that are faces of the grid. -/
def WellFormed (i : TruncatedHexagonalSlitherLinkInstance) : Prop :=
  0 < height i ∧ 0 < width i ∧ (∀ row ∈ i.1, row.length = width i) ∧
    i.2.length = height i + 1 ∧ (∀ row ∈ i.2, row.length = 2 * width i + 2) ∧
    ∀ y ≤ height i, ∀ x ≤ 2 * width i + 1, 0 < triangleClue i x y →
      ∀ e ∈ triangleSides (x, y), e ∈ (Graph i).edgeSet

/-- Some cycle `cyc` of the grid has, for every clue dodecagon and every clue triangle, exactly
as many of the face's sides among its edges as the clue value. -/
def TruncatedHexagonalSlitherLinkFeasible (i : TruncatedHexagonalSlitherLinkInstance) : Prop :=
  ∃ u, ∃ cyc : (Graph i).Walk u u, cyc.IsCycle ∧
    (∀ r < height i, ∀ c < width i, 0 < dodecagonClue i c r →
      (dodecagonSides c r).countP (· ∈ cyc.edges) + 1 = dodecagonClue i c r) ∧
    ∀ y ≤ height i, ∀ x ≤ 2 * width i + 1, 0 < triangleClue i x y →
      (triangleSides (x, y)).countP (· ∈ cyc.edges) + 1 = triangleClue i x y

open Classical in
/-- TRUNCATED HEXAGONAL SLITHER LINK as a decision problem over bitstrings. -/
noncomputable def truncatedHexagonalSlitherLinkDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TruncatedHexagonalSlitherLinkInstance) x with
  | some i => decide (WellFormed i ∧ TruncatedHexagonalSlitherLinkFeasible i)
  | none => false

/-- **TRUNCATED HEXAGONAL SLITHER LINK is NP-complete.** Source: Kölker (2012), Theorem 1. -/
public theorem_wanted truncatedHexagonalSlitherLink_npComplete :
    truncatedHexagonalSlitherLinkDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L truncatedHexagonalSlitherLinkDec

end MetaMathlibExt.Complexity.NPComplete.TruncatedHexagonalSlitherLink
