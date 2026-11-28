/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RECOGNITION OF POLYGON-CIRCLE GRAPHS is NP-complete

Source:
M. Pergel, "Recognition of polygon-circle graphs and graphs of interval filaments is
NP-complete", Graph-Theoretic Concepts in Computer Science (WG 2007), LNCS 4769 (2007), 238-247,
doi:10.1007/978-3-540-74839-7_23;
M. Koebe, "On a new class of intersection graphs", Fourth Czechoslovakian Symposium on
Combinatorics, Graphs and Complexity, Annals of Discrete Mathematics 51 (1992), 141-143,
doi:10.1016/S0167-5060(08)70618-6 (the class, as spider graphs).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.PolygonCircleGraphRecognitionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PolygonCircleGraphRecognition

/-!
# RECOGNITION OF POLYGON-CIRCLE GRAPHS is NP-complete

INSTANCE: a graph `G = (V, E)`. QUESTION: is `G` a polygon-circle graph (ISGCI `gc_111`,
"circle-polygon"), i.e. "the intersection graph of convex polygons inscribed in a circle"? Pergel
(2007) proved recognition of this class NP-complete.

The graph is given by an edge list on `Fin n`. The circle is the unit circle
`x ^ 2 + y ^ 2 = 1` in `ℝ × ℝ` (a similarity maps any circle onto it and preserves
intersections). A convex polygon inscribed in the circle is the convex hull (Mathlib's
`convexHull ℝ`) of a finite set `C v` of at least three points of the circle, its corners: distinct
points of a circle are in convex position, so this hull is a convex polygon whose corners are
exactly `C v`. Two vertices are adjacent when their polygons, as closed regions, intersect; for
inscribed polygons this is the same as their boundaries intersecting, since a polygon meets the
circle only in its corners. Polygons with one or two corners (points, chords) would not enlarge
the class: such a polygon can be replaced by a thin triangle near it without changing the
intersections.

Membership in NP: two inscribed polygons with no common corner intersect exactly when their
corners alternate around the circle, i.e. exactly when some two corners of each alternate, so
keeping at most `max 3 (2 · deg v)` corners of each polygon keeps every intersection (removing
corners never creates one), and a representation is described by the cyclic order of its corners.
Isolated vertices do not change the answer (each is a small triangle in an arc free of corners), so
the certificate covers the subgraph on the vertices that occur in edges, and the binary vertex
count does not make the problem succinct.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **RECOGNITION OF POLYGON-CIRCLE GRAPHS is NP-complete.** Source: Pergel (2007). -/
public theorem_wanted polygonCircleGraphRecognition_npComplete :
    polygonCircleGraphRecognitionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L polygonCircleGraphRecognitionDec

end MetaMathlibExt.Complexity.NPComplete.PolygonCircleGraphRecognition
