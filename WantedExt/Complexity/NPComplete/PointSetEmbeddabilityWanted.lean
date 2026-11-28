/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PLANAR POINT-SET EMBEDDABILITY is NP-complete

Source:
S. Cabello, "Planar embeddability of the vertices of a graph using a fixed point set is
NP-hard", Journal of Graph Algorithms and Applications 10 (2006), 353-363,
doi:10.7155/jgaa.00132 (Theorem 1).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.PointSetEmbeddabilityDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PointSetEmbeddability

open GeometricTravelingSalesman (point)

/-!
# PLANAR POINT-SET EMBEDDABILITY is NP-complete

INSTANCE: a graph `G` with `n` vertices and a set `P` of `n` points in the plane. QUESTION: is
there a planar straight-line embedding of `G` whose vertices are mapped onto `P`, that is, a
bijection from the vertices to `P` such that the straight-line segments drawn for the edges
intersect only at common endpoints?

This is Cabello's Theorem 1 (a geometric planar embedding `H` of `G` with `V(H) = P`). The points
have integer coordinates in the encoding of `GeometricTravelingSalesmanWanted` (each coordinate a
pair `(a, b)` of naturals standing for `a - b`, `GeometricTravelingSalesman.point`); Cabello's
reduction outputs integer points with polynomially bounded coordinates, and rational points
reduce to integer ones by scaling, which preserves straight-line drawings. The vertices of `G` are
`0, ..., n - 1`, where `n` is the number of points, and `G` is `edgeGraph n E` for an edge list `E`.
Segments are the repository's `SimpleGraph.Segment`. For the drawing that puts vertex `v` at the
point `σ v`, the conditions are those of `RectilinearPlanarity.IsRectilinearDrawing` without
its axis-parallel clause: the crossing condition of `SimpleGraph.IsPlanar`, and no vertex
(isolated ones included) lies on an edge except at its endpoints.

Cabello proves the problem NP-complete, even for 2-connected 2-outerplanar `G` (Theorem 1, by a
reduction from 3-PARTITION); membership in NP: the bijection is a certificate, checked by
polynomially many segment intersection tests.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **PLANAR POINT-SET EMBEDDABILITY is NP-complete.** Source: Cabello (2006), Theorem 1. -/
public theorem_wanted pointSetEmbeddability_npComplete :
    pointSetEmbeddabilityDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L pointSetEmbeddabilityDec

end MetaMathlibExt.Complexity.NPComplete.PointSetEmbeddability
