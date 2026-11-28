/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.GeometricTravelingSalesmanDefs
public import CSLibExt.Complexity.NPComplete.TspDefs

/-!
# GEOMETRIC TRAVELING SALESMAN in the L∞ metric: definitions

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
`RectilinearTravelingSalesmanDefs` for `L₁`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND23] GEOMETRIC TRAVELING SALESMAN,
comment;
M. R. Garey, R. L. Graham and D. S. Johnson, "Some NP-complete geometric problems",
Proceedings of the 8th Annual ACM Symposium on Theory of Computing (STOC 1976), 10-22,
doi:10.1145/800113.803626 (the `L₁` case).
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GeometricTravelingSalesmanLInfinity

/-- The `L∞` distance `max(|x₁ - x₂|, |y₁ - y₂|)` between two integer points. -/
def chebyshevDist (p q : ℤ × ℤ) : ℕ :=
  max (p.1 - q.1).natAbs (p.2 - q.2).natAbs

/-- The TRAVELING SALESMAN instance with `C = P`, the `L∞` distance, and the bound `B`: the
number of points, the matrix of pairwise `L∞` distances (row `j`, column `k` holds
`d(pⱼ, pₖ)`), and `B`. -/
def toTspInstance (i : GeometricTravelingSalesman.GeometricTravelingSalesmanInstance) :
    Tsp.TspInstance :=
  (i.1.length,
    (i.1.map GeometricTravelingSalesman.point).map fun p =>
      (i.1.map GeometricTravelingSalesman.point).map fun q => chebyshevDist p q,
    i.2)

/-- Some tour of the points has `L∞` length at most `B`. -/
def GeometricTravelingSalesmanLInfinityFeasible
    (i : GeometricTravelingSalesman.GeometricTravelingSalesmanInstance) : Prop :=
  Tsp.TspFeasible (toTspInstance i)

open Classical in
/-- GEOMETRIC TRAVELING SALESMAN in the `L∞` metric as a decision problem over bitstrings. -/
noncomputable def geometricTravelingSalesmanLInfinityDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GeometricTravelingSalesman.GeometricTravelingSalesmanInstance) x with
  | some i =>
      decide (GeometricTravelingSalesman.WellFormed i ∧
        GeometricTravelingSalesmanLInfinityFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.GeometricTravelingSalesmanLInfinity
