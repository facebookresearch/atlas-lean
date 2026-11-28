/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ORIENTED RADIUS: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT64] ORIENTED DIAMETER, p. 205
(comment: "The variation in which 'diameter' is replaced by 'radius' is also NP-complete.");
V. Chvátal and C. Thomassen, "Distances in orientations of graphs", Journal of
Combinatorial Theory, Series B 24 (1978), 61-75,
doi:10.1016/0095-8956(78)90078-3 (also Stanford report STAN-CS-75-517, 1975: deciding whether
a graph admits an orientation of radius two is NP-hard).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.OrientedDiameterDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.OrientedRadius

/-- Some orientation of the graph has radius at most `K`: some centre `c` reaches every vertex,
and is reached from every vertex, along at most `K` arcs (hence the orientation is strongly
connected). -/
def OrientedRadiusFeasible (i : OrientedDiameter.OrientedDiameterInstance) : Prop :=
  ∃ D : Digraph (Fin i.1), (OrientedDiameter.Graph i).IsOrientation D.Adj ∧
    ∃ c, ∀ v, OrientedDiameter.ReachWithin D i.2.2 c v ∧ OrientedDiameter.ReachWithin D i.2.2 v c

open Classical in
/-- ORIENTED RADIUS as a decision problem over bitstrings. -/
noncomputable def orientedRadiusDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := OrientedDiameter.OrientedDiameterInstance) x with
  | some i => decide (OrientedDiameter.WellFormed i ∧ OrientedRadiusFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.OrientedRadius
