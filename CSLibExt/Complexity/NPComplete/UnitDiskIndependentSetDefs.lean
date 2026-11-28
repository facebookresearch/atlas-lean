/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INDEPENDENT SET IN UNIT DISK GRAPHS: definitions

Source:
B. N. Clark, C. J. Colbourn and D. S. Johnson, "Unit disk graphs", Discrete Mathematics
86(1-3) (1990), 165-177, doi:10.1016/0012-365X(90)90358-O;
A. Tkachenko and H. Wang, "Dominating set, independent set, discrete k-center, dispersion, and
related problems for planar points in convex position", arXiv:2501.00207 (2024), Section 1
(definition of the unit-disk graph of a point set; NP-hardness of independent set on unit-disk
graphs, credited to Clark, Colbourn and Johnson);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT20] INDEPENDENT SET.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.UnitDiskDominatingSetDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnitDiskIndependentSet

open MetaMathlibExt.Complexity.NPComplete.PlanarKMeans (RatCode)
open MetaMathlibExt.Complexity.NPComplete.UnitDiskDominatingSet (unitDiskGraph)

/-- An instance: the points of `P` (pairs of rational coordinates) and the bound `K`. -/
abbrev UnitDiskIndependentSetInstance := List (RatCode × RatCode) × ℕ

/-- Well-formedness of an instance: all denominators are positive, the points are distinct (as
points of the plane), and `1 ≤ K ≤ |P|`. -/
def WellFormed (i : UnitDiskIndependentSetInstance) : Prop :=
  (∀ p ∈ i.1, 0 < p.1.2 ∧ 0 < p.2.2) ∧ (i.1.map fun p => (p.1.val, p.2.val)).Nodup ∧
    1 ≤ i.2 ∧ i.2 ≤ i.1.length

/-- The unit disk graph of `P` has an independent set of at least `K` points. -/
def UnitDiskIndependentSetFeasible (i : UnitDiskIndependentSetInstance) : Prop :=
  ∃ S : Finset (Fin i.1.length), i.2 ≤ S.card ∧ (unitDiskGraph i.1).IsIndepSet ↑S

open Classical in
/-- INDEPENDENT SET IN UNIT DISK GRAPHS as a decision problem over bitstrings. -/
noncomputable def unitDiskIndependentSetDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UnitDiskIndependentSetInstance) x with
  | some i => decide (WellFormed i ∧ UnitDiskIndependentSetFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.UnitDiskIndependentSet
