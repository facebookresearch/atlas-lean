/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DISTANCE-d PARTITION OF POINTS IN THE PLANE is NP-complete

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 3 (1982), 182-195,
doi:10.1016/0196-6774(82)90018-9, problem [3] DISTANCE-d PARTITION OF POINTS IN THE PLANE
(reference: S. Burr, private communication; transformation from PLANAR GRAPH 3-COLORABILITY;
the original was not available);
D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 5 (1984), 147-160,
doi:10.1016/0196-6774(84)90045-2, Section 2 (the result "should also be attributed to J. Orlin",
private communication).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.DistanceDPartitionPointsPlaneDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DistanceDPartitionPointsPlane

open GeometricTravelingSalesman (point)

/-!
# DISTANCE-d PARTITION OF POINTS IN THE PLANE is NP-complete

Johnson's column, problem [3]: INSTANCE: finite set `P ⊂ Z × Z` of integer-coordinate points in
the plane, positive integers `d` and `K`. QUESTION: is there a partition `P = P₁ ∪ ⋯ ∪ P_K` such
that if `u` and `v` are distinct points in some set `Pᵢ` of the partition, then the Euclidean
distance `d(u, v) > d`?

Comment there: NP-complete for fixed `K = 3`, also for the rectilinear metric; as a special case
of CHROMATIC NUMBER the problem is solvable in polynomial time for `K ≤ 2`.

The points are a list of distinct points; each point is a pair of integer coordinates, each given
as a pair `(p, q)` of naturals standing for `p - q`, decoded by `GeometricTravelingSalesman.point`
as in `GeometricTravelingSalesmanWanted`. Numbers are in binary. The partition is a surjective
map `c : Fin |P| → Fin K` on the positions of the list, with the nonempty blocks
`Pᵢ = c⁻¹ {i}` (so an instance with `K > |P|` is a no-instance). As the points are distinct,
distinct positions are distinct points. For `d ≥ 0` the
condition `d(u, v) > d` is `d² < (u₁ - v₁)² + (u₂ - v₂)²`, which is how it is written, over `ℤ`.

Membership in NP: the map `c` is a certificate of polynomial size.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **DISTANCE-d PARTITION OF POINTS IN THE PLANE is NP-complete.** Source: Johnson (1982),
problem [3] (Burr); Johnson (1984), Section 2 (Orlin). -/
public theorem_wanted distanceDPartitionPointsPlane_npComplete :
    distanceDPartitionPointsPlaneDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L distanceDPartitionPointsPlaneDec

end MetaMathlibExt.Complexity.NPComplete.DistanceDPartitionPointsPlane
