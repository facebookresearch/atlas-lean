/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TANTRIX ROTATION PUZZLE is NP-complete

Source:
M. Holzer and W. Holzer, "Tantrix rotation puzzles are intractable", Discrete Applied
Mathematics 144 (2004), 345-358, doi:10.1016/j.dam.2003.11.011;
D. Baumeister and J. Rothe, "The three-color and two-color Tantrix rotation puzzle problems
are NP-complete via parsimonious reductions", Information and Computation 207 (2009),
1119-1139, doi:10.1016/j.ic.2009.03.001 (arXiv:0711.1827), Section 2.2 (the formal definition
of the problem, following Holzer and Holzer).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.TantrixRotationPuzzleDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TantrixRotationPuzzle

/-!
# TANTRIX ROTATION PUZZLE is NP-complete

INSTANCE: a finite set of Tantrix tiles firmly placed at distinct positions of the
two-dimensional hexagonal coordinate system (the occupied region may have holes).
QUESTION: is there a rotation of the given tiles such that the colors of the lines of any two
adjacent tiles match at their joint edge?

Hexagonal coordinates (Holzer and Holzer; Baumeister and Rothe, Figure 3): two distinct points
`(a, b)` and `(c, d)` of `ℤ²` are neighbors iff `a = c` and `|b - d| = 1`, or `|a - c| = 1` and
`b = d`, or `a - c = b - d = 1`, or `a - c = b - d = -1`. The hexagons have a horizontal top
edge; going clockwise from the top, the six edges of the hexagon at `x` face the neighbors
`x + (1, 1)`, `x + (1, 0)`, `x + (0, -1)`, `x + (-1, -1)`, `x + (-1, 0)` and `x + (0, 1)`.
Edge `e` and edge `e + 3 (mod 6)` are opposite, so the joint edge of `x` and `x + d` is edge
`e` of `x` and edge `e + 3` of `x + d`, where `d` is the direction of edge `e`.

Tiles: a Tantrix tile carries three lines of three distinct colors, chosen among red, yellow,
blue and green (encoded `0`, `1`, `2`, `3`); each line joins two of the six edges, and the four
tile kinds (Sint, Brid, Chin, Rond) give 56 different tiles. As in Baumeister and Rothe, a tile
is given by its color sequence: the colors at its six edges, read clockwise. Each color then
occurs on exactly two edges (the ends of its line), and the color sequence determines the
lines. The color sequences of the 56 tiles are exactly the sequences in which three distinct
colors each occur twice, except those whose three lines are all straight (each edge colored
like the opposite edge), a pattern no Tantrix tile has. Rotating a tile shifts its color
sequence cyclically. Positions are translated so that both coordinates are nonnegative, which
changes neither adjacency nor the answer.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **TANTRIX ROTATION PUZZLE is NP-complete.** Source: Holzer and Holzer (2004); definitions
as recalled by Baumeister and Rothe (2009). -/
public theorem_wanted tantrixRotationPuzzle_npComplete :
    tantrixRotationPuzzleDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L tantrixRotationPuzzleDec

end MetaMathlibExt.Complexity.NPComplete.TantrixRotationPuzzle
