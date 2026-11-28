/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RECOGNITION OF TRIANGLE GRAPHS (PI* GRAPHS) is NP-complete

Source:
G. B. Mertzios, "The recognition of triangle graphs", Theoretical Computer Science 438 (2012),
34-47, doi:10.1016/j.tcs.2012.02.042; conference version in STACS 2011, LIPIcs 9, 591-602,
doi:10.4230/LIPIcs.STACS.2011.591;
ISGCI, class "PI*" (gc_290), problem Recognition.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.TriangleGraphRecognitionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TriangleGraphRecognition

/-!
# RECOGNITION OF TRIANGLE GRAPHS (PI* GRAPHS) is NP-complete

INSTANCE: a graph `G = (V, E)`. QUESTION: is `G` a triangle graph (a PI* graph), i.e. does it
have an intersection model consisting of triangles between two parallel lines?

Mertzios (STACS 2011 version, Section 1): a trapezoid graph is the intersection graph of
trapezoids between two parallel lines `L₁` and `L₂`, each with one side on each line; "G is a
triangle graph if it admits a trapezoid representation, in which every trapezoid is a triangle,
but now there is no restriction on which line between L₁ and L₂ contains one point of the
triangle and which one contains the other two points (i.e. the interval) of the triangle"; in
his notation, "if R is a triangle representation of G, then L(u) = R(u) or l(u) = r(u) for every
u ∈ V" (the upper or the lower side of each trapezoid is a single point). He proves the
recognition problem NP-complete. ISGCI: "A graph is a PI* graph if it has an intersection model
consisting of triangles between two lines."

The trapezoids are those of `DominatingSetCoTrapezoidGraphs.trapezoid`: between the lines
`y = 1` and `y = 0` of `ℝ × ℝ`, vertex `v` gets the convex hull of `(a v, 1)`, `(b v, 1)`,
`(c v, 0)`, `(d v, 0)` with `a v ≤ b v` and `c v ≤ d v`, and two distinct vertices are adjacent
exactly when their trapezoids meet (`DominatingSetCoTrapezoidGraphs.IsTrapezoidGraph`). A
triangle representation adds `a v = b v ∨ c v = d v` for every vertex. As in Mertzios's
condition, both sides may be single points (the triangle degenerates to a segment between the
lines); this does not change the class, since in a finite model each such segment can be widened
to a thin triangle without creating new intersections (disjoint compact sets are at positive
distance).

The graph is given by an edge list on `Fin n`. Isolated vertices do not change the answer (a
triangle far from all others), so the binary vertex count does not make the problem succinct.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **RECOGNITION OF TRIANGLE GRAPHS (PI* GRAPHS) is NP-complete.** Source: Mertzios (2012);
ISGCI gc_290. -/
public theorem_wanted triangleGraphRecognition_npComplete :
    triangleGraphRecognitionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L triangleGraphRecognitionDec

end MetaMathlibExt.Complexity.NPComplete.TriangleGraphRecognition
