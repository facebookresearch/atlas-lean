/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GEOMETRIC STEINER TREE is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND13] GEOMETRIC
STEINER TREE;
M. R. Garey, R. L. Graham, and D. S. Johnson, "The complexity of computing
Steiner minimal trees", SIAM Journal on Applied Mathematics 32 (1977), 835-859,
doi:10.1137/0132072.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.GeometricSteinerTreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GeometricSteinerTree

/-!
# GEOMETRIC STEINER TREE is NP-complete

INSTANCE: a set `P ⊆ Z × Z` of points in the plane, and a positive integer `B`. QUESTION: is
there a finite set `Q ⊆ Z × Z` such that there is a spanning tree of total weight `B` or less
for the vertex set `P ∪ Q`, where the weight of an edge `{(x₁, y₁), (x₂, y₂)}` is the
discretized Euclidean length `⌈√((x₁ - x₂)² + (y₁ - y₂)²)⌉`?

The instance encoding, the point decoding `point` and the distance `discreteDist` are those of
`GeometricTravelingSalesmanWanted` (GJ [ND23]), which uses the same discretized Euclidean
metric. `P` is given as a list of points (repetitions do not change the set `points`), each
integer as a pair of naturals `(positive part, negative part)`. A spanning tree for `P ∪ Q` is a
`SimpleGraph` on the points of `P ∪ Q` that is a tree (Mathlib's `SimpleGraph.IsTree`), and its
weight is the sum of `edgeLength` over its edges. Coordinates and `B` use the canonical binary
encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

open GeometricTravelingSalesman (point discreteDist)

/-- **GEOMETRIC STEINER TREE is NP-complete.** Source: Garey and Johnson (1979), [ND13];
Garey, Graham, and Johnson (1977). -/
public theorem_wanted geometricSteinerTree_npComplete :
    geometricSteinerTreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L geometricSteinerTreeDec

end MetaMathlibExt.Complexity.NPComplete.GeometricSteinerTree
