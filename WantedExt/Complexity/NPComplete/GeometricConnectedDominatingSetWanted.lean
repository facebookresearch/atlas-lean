/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GEOMETRIC CONNECTED DOMINATING SET is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND48] GEOMETRIC CONNECTED
DOMINATING SET;
D. Lichtenstein, "Planar formulae and their uses", SIAM Journal on Computing 11 (1982),
329-343, doi:10.1137/0211025.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.GeometricConnectedDominatingSetDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GeometricConnectedDominatingSet

open GeometricTravelingSalesman (point)

/-!
# GEOMETRIC CONNECTED DOMINATING SET is NP-complete

INSTANCE: a set `P ⊆ Z × Z` of points in the plane, and positive integers `B` and `K`.
QUESTION: is there a subset `P' ⊆ P` with `|P'| ≤ K` such that all points in `P - P'` are within
Euclidean distance `B` of some point in `P'`, and such that the graph `G = (P', E)`, with an edge
between two points in `P'` if and only if they are within distance `B` of each other, is
connected?

`P` is given as a list of distinct points, each integer coordinate as a pair of naturals
`(positive part, negative part)`, decoded by `point` of `GeometricTravelingSalesmanWanted` (GJ
[ND23], the same point encoding). The points are the vertices `Fin |P|` of the distance-`B`
graph `Graph i`, in which two distinct points are adjacent when their Euclidean distance is at
most `B`. For integer points that is `(x₁ - x₂)² + (y₁ - y₂)² ≤ B²`, since both sides of
`√((x₁ - x₂)² + (y₁ - y₂)²) ≤ B` are nonnegative. The first condition says that `P'` dominates
this graph (`SimpleGraph.IsDominating` from `MathlibExt.Combinatorics.SimpleGraph.Domination`:
every point is in `P'` or adjacent to a point of `P'`), and the second that the subgraph induced
on `P'`, which is the graph `(P', E)` of the question, is `SimpleGraph.Connected`. A connected
graph is nonempty in Mathlib, so the empty point set is a no-instance. Coordinates, `B` and `K`
use the canonical binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **GEOMETRIC CONNECTED DOMINATING SET is NP-complete.** Source: Garey and Johnson (1979),
[ND48]; Lichtenstein (1982). -/
public theorem_wanted geometricConnectedDominatingSet_npComplete :
    geometricConnectedDominatingSetDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L geometricConnectedDominatingSetDec

end MetaMathlibExt.Complexity.NPComplete.GeometricConnectedDominatingSet
