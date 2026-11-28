/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GEOMETRIC TRAVELING SALESMAN in the L∞ metric is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND23] GEOMETRIC TRAVELING SALESMAN,
comment;
M. R. Garey, R. L. Graham and D. S. Johnson, "Some NP-complete geometric problems",
Proceedings of the 8th Annual ACM Symposium on Theory of Computing (STOC 1976), 10-22,
doi:10.1145/800113.803626 (the `L₁` case).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.GeometricTravelingSalesmanLInfinityDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GeometricTravelingSalesmanLInfinity

/-!
# GEOMETRIC TRAVELING SALESMAN in the L∞ metric is NP-complete

Given a set `P ⊆ Z × Z` of points in the plane and a positive integer `B`, is there a tour of
length `B` or less for the TRAVELING SALESMAN instance with `C = P` and
`d((x₁, y₁), (x₂, y₂))` equal to the `L∞` distance `max(|x₁ - x₂|, |y₁ - y₂|)`?

This is GEOMETRIC TRAVELING SALESMAN
(`WantedExt.Complexity.NPComplete.GeometricTravelingSalesmanWanted`, Garey and Johnson [ND23])
with the discretized Euclidean distance replaced by the `L∞` distance, recorded in the [ND23]
comment: "Remains NP-complete in the strong sense if the distance measure is replaced by the
`L₁` 'rectilinear' metric [Garey, Graham, and Johnson, 1976] or the `L∞` metric, which is
equivalent to `L₁` under a 45° rotation." Concretely, `(x, y) ↦ (x + y, x - y)` maps integer
points to integer points and turns `L₁` distances into `L∞` distances
(`|a| + |b| = max(|a + b|, |a - b|)`), so the rectilinear instances of Garey, Graham and Johnson
become `L∞` instances with the same tour lengths.

The instance format (a nonempty list of distinct integer points, each coordinate a pair
`(p, q)` of naturals standing for `p - q`, and `B`) and its well-formedness are those of
GEOMETRIC TRAVELING SALESMAN; the question is TRAVELING SALESMAN
(`WantedExt.Complexity.NPComplete.TspWanted`) on the matrix of pairwise `L∞` distances, as in
`RectilinearTravelingSalesmanWanted` for `L₁`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **GEOMETRIC TRAVELING SALESMAN is NP-complete in the `L∞` metric.** Source: Garey and
Johnson (1979), [ND23], comment; Garey, Graham, and Johnson (1976). -/
public theorem_wanted geometricTravelingSalesmanLInfinity_npComplete :
    geometricTravelingSalesmanLInfinityDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L geometricTravelingSalesmanLInfinityDec

end MetaMathlibExt.Complexity.NPComplete.GeometricTravelingSalesmanLInfinity
