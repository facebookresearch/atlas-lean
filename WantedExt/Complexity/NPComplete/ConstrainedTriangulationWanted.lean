/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CONSTRAINED TRIANGULATION is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND45] CONSTRAINED TRIANGULATION;
E. L. Lloyd, "On triangulations of a set of points in the plane", Proc. 18th Annual Symposium
on Foundations of Computer Science (FOCS 1977), 228-240, doi:10.1109/SFCS.1977.21.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ConstrainedTriangulationDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ConstrainedTriangulation

/-!
# CONSTRAINED TRIANGULATION is NP-complete

INSTANCE: a graph `G = (V, E)` and, for each `v ∈ V`, a pair `(x_v, y_v)` of integer
coordinates. QUESTION: is there a subset `E' ⊆ E` such that the set of line segments
`{[(x_u, y_u), (x_v, y_v)] : {u, v} ∈ E'}` is a triangulation of the point set
`{(x_v, y_v) : v ∈ V}` in the plane?

Triangulation follows Lloyd's definition: "A set, V, of points in the plane is triangulated by
a subset T, of the straight-line segments whose endpoints are in V, if T is a maximal subset
such that the line segments in T intersect only at their endpoints." The vertices carry
pairwise distinct points (the instance lists the points of a set), so the straight-line
segments with endpoints in the point set are the pairs of distinct vertices, i.e. the edges of
a `SimpleGraph (Fin n)`. Segments are MathlibExt's closed real segments `SimpleGraph.Segment`,
and two distinct segments intersect only at their endpoints when their intersection lies in
the set of their common endpoints, the condition of MathlibExt's `SimpleGraph.IsPlanar` for a
fixed drawing. Maximality is Mathlib's `Maximal`, taken over all segment sets with endpoints in
the point set, not only over subsets of `E`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances. An integer coordinate is a pair
`(p, q)` of naturals standing for `p - q`.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **CONSTRAINED TRIANGULATION is NP-complete.** Source: Garey and Johnson (1979), [ND45];
Lloyd (1977). -/
public theorem_wanted constrainedTriangulation_npComplete :
    constrainedTriangulationDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L constrainedTriangulationDec

end MetaMathlibExt.Complexity.NPComplete.ConstrainedTriangulation
