/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRID INTERSECTION GRAPH RECOGNITION is NP-complete

Source:
J. Kratochvíl, "A special planar satisfiability problem and a consequence of its
NP-completeness", Discrete Applied Mathematics 52(3) (1994), 233-252,
doi:10.1016/0166-218X(94)90143-0 (abstract: NP-completeness "of recognizing several classes of
intersection graphs of geometric objects in the plane, including grid intersection graphs");
definition of grid intersection graphs as in I. Ben-Arroyo Hartman, I. Newman and R. Ziv, "On grid
intersection graphs", Discrete Mathematics 87 (1991), 41-52, doi:10.1016/0012-365X(91)90069-E,
and S. Chaplick, S. Felsner, U. Hoffmann and V. Wiechert, "Grid intersection graphs and order
dimension", Order 35 (2018), 363-391, doi:10.1007/s11083-017-9437-0, Section 1.1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.GridIntersectionGraphRecognitionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GridIntersectionGraphRecognition

/-!
# GRID INTERSECTION GRAPH RECOGNITION is NP-complete

A grid intersection graph is "an intersection graph of horizontal and vertical segments in the
plane where parallel segments do not intersect" (Chaplick, Felsner, Hoffmann and Wiechert): a
bipartite graph with sides `U` and `W` whose `U`-vertices are represented by horizontal segments
and `W`-vertices by vertical segments, two segments meeting exactly when the vertices are
adjacent.

INSTANCE: a bipartite graph `G = (U, W, E)`.
QUESTION: is `G` a grid intersection graph, i.e. are there horizontal segments for the vertices of
`U` and vertical segments for the vertices of `W`, pairwise disjoint within each side, such that
`u ∈ U` and `w ∈ W` are adjacent exactly when their segments intersect?

The sides are `U = {0, ..., a - 1}` and `W = {0, ..., b - 1}`, and `E` is a list of pairs
`(u, w)` with `u < a`, `w < b`. A horizontal segment is `{(x, y) : x₁ ≤ x ≤ x₂}` at height `y`,
given as `(y, x₁, x₂)` with `x₁ ≤ x₂`; a vertical segment is `(x, y₁, y₂)` with `y₁ ≤ y₂`.
Coordinates are natural numbers: whether axis-parallel segments meet depends only on the order of
their coordinates, so any real representation can be replaced by the ranks of its coordinates.
Degenerate (one-point) segments are allowed. The bipartition is part of the instance; a reflection
in the diagonal exchanges horizontal and vertical segments and connected components can be placed
far apart, so this is equivalent to asking whether some bipartition admits a representation.

Membership in NP: a vertex in no edge can be represented by a short segment far from all others,
so the certificate lists segments, with coordinates bounded by a polynomial in `|E|`, only for
the at most `2|E|` vertices that lie on edges, even though `a` and `b` are written in binary.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **GRID INTERSECTION GRAPH RECOGNITION is NP-complete.** Source: Kratochvíl (1994). -/
public theorem_wanted gridIntersectionGraphRecognition_npComplete :
    gridIntersectionGraphRecognitionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L gridIntersectionGraphRecognitionDec

end MetaMathlibExt.Complexity.NPComplete.GridIntersectionGraphRecognition
