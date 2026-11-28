/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RECTILINEAR TRAVELING SALESMAN: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND23] GEOMETRIC TRAVELING
SALESMAN, p. 212, comment: "Remains NP-complete in the strong sense if the distance measure
is replaced by the L₁ "rectilinear" metric";
M. R. Garey, R. L. Graham, and D. S. Johnson, "Some NP-complete geometric problems", Proc. 8th
Annual ACM Symposium on Theory of Computing (1976), 10-22, doi:10.1145/800113.803626.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.GeometricTravelingSalesmanDefs
public import CSLibExt.Complexity.NPComplete.TspDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RectilinearTravelingSalesman

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

end MetaMathlibExt.Complexity.NPComplete.RectilinearTravelingSalesman
