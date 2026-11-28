/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ORIENTED DIAMETER with `K = 2`: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT64] ORIENTED DIAMETER, p. 205
(comment: "Both problems remain NP-complete for `K = 2`.");
V. Chvátal and C. Thomassen, "Distances in orientations of graphs", Journal of
Combinatorial Theory, Series B 24 (1978), 61-75,
doi:10.1016/0095-8956(78)90078-3 (also Stanford report STAN-CS-75-517, 1975: deciding whether
a graph admits an orientation of diameter two is NP-hard).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.OrientedDiameterDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.OrientedDiameterTwo

/-- Well-formedness of an instance: the parent's (a simple edge list on `Fin n` and
`0 < K ≤ |V|`) and `K = 2`. -/
def WellFormed (i : OrientedDiameter.OrientedDiameterInstance) : Prop :=
  OrientedDiameter.WellFormed i ∧ i.2.2 = 2

open Classical in
/-- ORIENTED DIAMETER with `K = 2` as a decision problem over bitstrings. -/
noncomputable def orientedDiameterTwoDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := OrientedDiameter.OrientedDiameterInstance) x with
  | some i => decide (WellFormed i ∧ OrientedDiameter.OrientedDiameterFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.OrientedDiameterTwo
