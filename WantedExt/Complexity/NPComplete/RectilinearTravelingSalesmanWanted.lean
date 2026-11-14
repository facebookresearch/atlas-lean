/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RECTILINEAR TRAVELING SALESMAN is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND23] GEOMETRIC TRAVELING
SALESMAN, p. 212, comment: "Remains NP-complete in the strong sense if the distance measure
is replaced by the L₁ "rectilinear" metric";
M. R. Garey, R. L. Graham, and D. S. Johnson, "Some NP-complete geometric problems", Proc. 8th
Annual ACM Symposium on Theory of Computing (1976), 10-22, doi:10.1145/800113.803626.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.GeometricTravelingSalesmanWanted
public import WantedExt.Complexity.NPComplete.TspWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RectilinearTravelingSalesman

/-!
# RECTILINEAR TRAVELING SALESMAN is NP-complete

Given a set `P ⊆ Z × Z` of points in the plane and a positive integer `B`, is there a tour of
length `B` or less for the TRAVELING SALESMAN instance with `C = P` and
`d((x₁, y₁), (x₂, y₂))` equal to the `L₁` ("rectilinear") distance `|x₁ - x₂| + |y₁ - y₂|`?

This is GEOMETRIC TRAVELING SALESMAN
(`MetaMathlibExt.Complexity.NPComplete.GeometricTravelingSalesman`) with the discretized
Euclidean distance replaced by the `L₁` distance. The instance format (a nonempty list of
distinct integer points, each coordinate a pair `(p, q)` of naturals standing for `p - q`, and
`B`) and its well-formedness are those of GEOMETRIC TRAVELING SALESMAN. The question is
TRAVELING SALESMAN (`MetaMathlibExt.Complexity.NPComplete.Tsp`) on the matrix of pairwise
`L₁` distances: a tour visits every point exactly once, and its length is the sum of the
distances between consecutive points, including the return from the last point to the first.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- The `L₁` ("rectilinear") distance `|x₁ - x₂| + |y₁ - y₂|` between two integer points. -/
def rectilinearDist (p q : ℤ × ℤ) : ℕ :=
  (p.1 - q.1).natAbs + (p.2 - q.2).natAbs

/-- The TRAVELING SALESMAN instance with `C = P`, the `L₁` distance, and the bound `B`: the
number of points, the matrix of pairwise `L₁` distances (row `j`, column `k` holds
`d(pⱼ, pₖ)`), and `B`. -/
def toTspInstance (i : GeometricTravelingSalesman.GeometricTravelingSalesmanInstance) :
    Tsp.TspInstance :=
  (i.1.length,
    (i.1.map GeometricTravelingSalesman.point).map fun p =>
      (i.1.map GeometricTravelingSalesman.point).map fun q => rectilinearDist p q,
    i.2)

/-- Some tour of the points has `L₁` length at most `B`. -/
def RectilinearTravelingSalesmanFeasible
    (i : GeometricTravelingSalesman.GeometricTravelingSalesmanInstance) : Prop :=
  Tsp.TspFeasible (toTspInstance i)

open Classical in
/-- RECTILINEAR TRAVELING SALESMAN as a decision problem over bitstrings. -/
noncomputable def rectilinearTravelingSalesmanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GeometricTravelingSalesman.GeometricTravelingSalesmanInstance) x with
  | some i =>
      decide (GeometricTravelingSalesman.WellFormed i ∧ RectilinearTravelingSalesmanFeasible i)
  | none => false

/-- **RECTILINEAR TRAVELING SALESMAN is NP-complete.** Source: Garey and Johnson (1979),
[ND23], comment; Garey, Graham, and Johnson (1976). -/
public theorem_wanted rectilinearTravelingSalesman_npComplete :
    rectilinearTravelingSalesmanDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L rectilinearTravelingSalesmanDec

end MetaMathlibExt.Complexity.NPComplete.RectilinearTravelingSalesman
