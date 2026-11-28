/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# JIGSAW PUZZLE is NP-complete

Source:
E. D. Demaine and M. L. Demaine, "Jigsaw puzzles, edge matching, and polyomino packing:
connections and complexity", Graphs and Combinatorics 23 (2007), suppl. 1, 195-208,
doi:10.1007/s00373-007-0713-4 (Section 6, Theorem 5 and Corollary 2).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.JigsawPuzzleDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.JigsawPuzzle

/-!
# JIGSAW PUZZLE is NP-complete

INSTANCE: `n` square jigsaw pieces, each edge of which carries a tab, a pocket, or nothing,
and a rectangular box. QUESTION: do the pieces fit together to fill the box?

Demaine and Demaine (Section 6) consider "one of the simplest kinds: each piece is a square
augmented on each edge with a tab, with a pocket, or not at all. Tabs and pockets can have
arbitrary shapes (of sufficiently small size to not cause overlap), and only matching tabs and
pockets fit together. Unaugmented edges can fit against each other or against the boundary of a
rectangular box." Corollary 2: "It is NP-complete to decide whether `n` given jigsaw pieces fit
together to form a `√n × √n` square box." Square boxes are rectangles, so the rectangle version
stated here is NP-hard too, and it is in NP.

An edge is a pair `(k, c)`: `k = 0` is an unaugmented (flat) edge, `k = 1` a tab of shape `c`,
`k = 2` a pocket of shape `c` (the shape of a flat edge is ignored). A piece is
`(top, right, bottom, left)`. Pieces may be turned by quarter turns (`rotate` turns a piece a
quarter turn clockwise, moving its top edge to the right side) and are not reflected, as for
the tiles of the edge-matching puzzles in the same paper. The box has `h` rows and `w` columns;
position `(y, x)` is row `y` (top to bottom) and column `x` (left to right). A solution places
every piece exactly once (a bijection from positions to pieces) with a rotation, such that
the two edges along every common side of horizontally or vertically adjacent pieces fit (both
flat, or a tab and a pocket of the same shape), and every edge along the boundary of the box is
flat. A bijection exists only when `n = h w`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **JIGSAW PUZZLE is NP-complete.** Source: Demaine and Demaine (2007), Corollary 2. -/
public theorem_wanted jigsawPuzzle_npComplete :
    jigsawPuzzleDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L jigsawPuzzleDec

end MetaMathlibExt.Complexity.NPComplete.JigsawPuzzle
