/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HEXAGONAL SLITHER LINK is NP-complete

Source:
J. Kölker, "Selected Slither Link variants are NP-complete", Journal of Information
Processing 20(3) (2012), 709-712, doi:10.2197/ipsjjip.20.709, Theorem 3.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Paths

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HexagonalSlitherLink

/-!
# HEXAGONAL SLITHER LINK is NP-complete

Kölker (2012), Section 1: "Let `G = (V, E)` be a plane graph and `F_c` a set of faces in `G`,
the clues, and let `v : F_c → ℕ` be a function giving the clue values. The Slither Link decision
problem is this: decide whether there is a set of edges `C ⊆ E` such that `C` is a cycle and
such that for all faces `F ∈ F_c` the number of edges in `C` incident to `F` equals `v(F)`."
Section 6 restricts `G` to a class of hexagonal grids: "we have `w` columns of `h` hexagons,
each column's starting hexagon alternatingly to the southeast or northeast of its left hand
neighbour" (Fig. 6 and Fig. 7, `w = 6`, `h = 5`: the hexagons have horizontal top and bottom
sides, consecutive hexagons of a column share a horizontal side, and the second column starts to
the southeast of the first). Theorem 3: "The Hexagonal Slither Link decision problem is
NP-complete."

INSTANCE: integers `w, h ≥ 1` and a clue value for some of the `wh` hexagons of the hexagonal
grid with `w` columns of `h` hexagons.
QUESTION: is there a cycle `C` in the grid such that every clue hexagon has exactly as many of
its six sides in `C` as its clue value?

Representation. Hexagon `r` of column `c` (`r = 0` at the top) is the hexagon `(c, r)`. With
`y₀ = 2r + c % 2`, its corners, clockwise from the top left, are the points `(c, y₀)`,
`(c + 1, y₀)`, `(c + 1, y₀ + 1)`, `(c + 1, y₀ + 2)`, `(c, y₀ + 2)` and `(c, y₀ + 1)` of `ℕ × ℕ`
(`x` to the right, `y` downwards; `(c, y₀ + 1)` and `(c + 1, y₀ + 1)` are the left and right
corners). So hexagon `(c, r + 1)` lies below hexagon `(c, r)`, sharing the side
`(c, y₀ + 2)`-`(c + 1, y₀ + 2)`, and for even `c` hexagon `(c + 1, r)` lies to the southeast of
hexagon `(c, r)`, for odd `c` to the northeast. The grid is the `SimpleGraph (ℕ × ℕ)` whose
edges are the sides of its `wh` hexagons; other points are isolated vertices. Its bounded faces
are the hexagons. The clues are given as the grid itself, column by column, `h` entries per
column: `0` for no clue and `v + 1` for clue value `v`; so the instance size is proportional to
`wh`, matching the unary encoding of `w` and `h` in the source. Clues sit on the hexagons, the
bounded faces, as in the reduction. A cycle `C ⊆ E` is the edge set of a cycle `c` of the graph
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

/-- An instance: the clue grid, column by column from the left; entry `r` of column `c` is the
clue of hexagon `(c, r)`, `0` for no clue and `v + 1` for clue value `v`. -/
abbrev HexagonalSlitherLinkInstance := List (List ℕ)

/-- The number of columns `w`. -/
def width (i : HexagonalSlitherLinkInstance) : ℕ := i.length

/-- The number of hexagons `h` in each column (the length of the first column). -/
def height (i : HexagonalSlitherLinkInstance) : ℕ := (i.headD []).length

/-- The clue entry of hexagon `(c, r)`. -/
def clue (i : HexagonalSlitherLinkInstance) (c r : ℕ) : ℕ := (i.getD c []).getD r 0

/-- The six sides of hexagon `(c, r)`, clockwise from its top side, with `y₀ = 2r + c % 2` the
height of its top side; its corners are `(c, y₀)`, `(c + 1, y₀)`, `(c + 1, y₀ + 1)`,
`(c + 1, y₀ + 2)`, `(c, y₀ + 2)` and `(c, y₀ + 1)`. -/
def sides (c r : ℕ) : List (Sym2 (ℕ × ℕ)) :=
  let y₀ := 2 * r + c % 2
  [s((c, y₀), (c + 1, y₀)), s((c + 1, y₀), (c + 1, y₀ + 1)),
    s((c + 1, y₀ + 1), (c + 1, y₀ + 2)), s((c + 1, y₀ + 2), (c, y₀ + 2)),
    s((c, y₀ + 2), (c, y₀ + 1)), s((c, y₀ + 1), (c, y₀))]

/-- The hexagonal grid with `w` columns of `h` hexagons: two points are adjacent when they are the
ends of a side of one of its hexagons. -/
def Graph (i : HexagonalSlitherLinkInstance) : SimpleGraph (ℕ × ℕ) :=
  SimpleGraph.fromRel fun p q => ∃ c < width i, ∃ r < height i, s(p, q) ∈ sides c r

/-- Well-formedness: `w ≥ 1` columns, each of `h ≥ 1` hexagons. -/
def WellFormed (i : HexagonalSlitherLinkInstance) : Prop :=
  0 < width i ∧ 0 < height i ∧ ∀ col ∈ i, col.length = height i

/-- Some cycle `cyc` of the grid has, for every clue hexagon, exactly as many of the hexagon's
sides among its edges as the clue value. -/
def HexagonalSlitherLinkFeasible (i : HexagonalSlitherLinkInstance) : Prop :=
  ∃ u, ∃ cyc : (Graph i).Walk u u, cyc.IsCycle ∧
    ∀ c < width i, ∀ r < height i, 0 < clue i c r →
      (sides c r).countP (· ∈ cyc.edges) + 1 = clue i c r

open Classical in
/-- HEXAGONAL SLITHER LINK as a decision problem over bitstrings. -/
noncomputable def hexagonalSlitherLinkDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HexagonalSlitherLinkInstance) x with
  | some i => decide (WellFormed i ∧ HexagonalSlitherLinkFeasible i)
  | none => false

/-- **HEXAGONAL SLITHER LINK is NP-complete.** Source: Kölker (2012), Theorem 3. -/
public theorem_wanted hexagonalSlitherLink_npComplete :
    hexagonalSlitherLinkDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L hexagonalSlitherLinkDec

end MetaMathlibExt.Complexity.NPComplete.HexagonalSlitherLink
