/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# YAGIT is NP-complete

Source:
N. Kiatchaipipat and S. Ruangwises, "NP-completeness proofs of puzzles using the T-metacell
framework", arXiv:2508.11570 (2025), Section 2.4;
puzzle rules: A. Janko and O. Janko, "Yagit", https://www.janko.at/Raetsel/Yagit/index.htm.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.YagitDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Yagit

/-!
# YAGIT is NP-complete

Kiatchaipipat and Ruangwises (2025), Section 2.4: "In Yagit, we have a grid in which some cells
are filled with either a sheep or a wolf. Each grid intersection point may have a black dot.
The goal is to partition the grid into regions using any number of lines such that each region
must contain at least one sheep or at least one wolf, but not both. Each partition lines must
start and end at unique points on the border of the grid and may only turn 90 degrees at a
black dot, but they are not required to do so. The partition lines can intersect, but only
where there are no black dots. Not all of the black dots must be used." Janko's English rules:
"Divide the grid along the grid lines in regions. A region must contain either sheep or wolves
(but not both) and must not be empty. The border lines of the regions start and end on the
edges of the grid; may turn by 90° in black grid dots (but nowhere else) and may cross
themselves in any grid dot except the black ones." The paper proves Yagit NP-complete.

INSTANCE: an `m × n` grid whose squares are empty or hold a sheep or a wolf, and a set of black
dots on the grid points.
QUESTION: can the grid be divided into regions by lines along the grid lines as above?

Representation. The squares are given row by row (`0` empty, `1` sheep, `2` wolf), the black
dots as the `(m + 1) × (n + 1)` grid of points `(a, b)`, `a ≤ m`, `b ≤ n`, row by row; the
instance size is proportional to the area. Square `(r, c)` has corners `(r, c)` and
`(r + 1, c + 1)`. A unit segment `(true, a, b)` joins points `(a, b)` and `(a, b + 1)`, and
`(false, a, b)` joins `(a, b)` and `(a + 1, b)`; it is inner when it lies inside the grid
rather than on its border, i.e. it separates two squares (`wall`). The lines are given by the
set of inner segments they cover, a predicate `F` (segments on the border separate nothing).
A region is a connected component (`SimpleGraph.ConnectedComponent`) of Mathlib's grid graph
`pathGraph m □ pathGraph n` on the squares after deleting the edges between squares whose
common side is drawn. At an inner point the drawn segments are, as `PointRule` requires:
none; two collinear ones (a line passing); two perpendicular ones only at a black dot (a line
turning); all four only at a point without a black dot (two lines crossing). One or three
segments would make a line end inside the grid or branch, and four at a black dot would make
lines meet there. Lines are then the maximal chains of drawn segments in which consecutive
segments meet at an inner point and are collinear or meet at a black dot (`Linked`); such a
chain either reaches the border at both ends or closes up inside the grid, and the rules
require the former: every drawn segment is linked through a chain to a segment with an end on
the border (`LinesReachBorder`). A point on the border lies on at most one inner segment, so
different lines end at different points.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **YAGIT is NP-complete.** Source: Kiatchaipipat and Ruangwises (2025), Section 2.4. -/
public theorem_wanted yagit_npComplete :
    yagitDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L yagitDec

end MetaMathlibExt.Complexity.NPComplete.Yagit
