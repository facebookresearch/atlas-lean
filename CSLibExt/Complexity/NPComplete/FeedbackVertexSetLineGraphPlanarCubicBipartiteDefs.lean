/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FEEDBACK VERTEX SET on line graphs of planar cubic bipartite graphs: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT7] FEEDBACK VERTEX SET, the problem
restricted here;
A. Munaro, "On line graphs of subcubic triangle-free graphs", Discrete Mathematics 340(6)
(2017), 1210-1226, doi:10.1016/j.disc.2017.01.006, Theorem 24.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.FeedbackVertexSetDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetLineGraphPlanarCubicBipartite

open MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSet

open Classical in
/-- `G` is the line graph of a planar cubic bipartite graph: some planar, bipartite, 3-regular
graph `H` on `Fin m` has a line graph isomorphic to `G`. -/
def IsLineGraphOfPlanarCubicBipartite {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ (m : ℕ) (H : SimpleGraph (Fin m)),
    H.IsPlanar ∧ H.IsBipartite ∧ H.IsRegularOfDegree 3 ∧ Nonempty (G ≃g H.lineGraph)

/-- Well-formedness of an instance: a well-formed FEEDBACK VERTEX SET instance whose graph is the
line graph of a planar cubic bipartite graph. -/
def WellFormed (i : FeedbackVertexSetInstance) : Prop :=
  FeedbackVertexSet.WellFormed i ∧ IsLineGraphOfPlanarCubicBipartite (Graph i)

open Classical in
/-- FEEDBACK VERTEX SET on line graphs of planar cubic bipartite graphs as a decision problem
over bitstrings. -/
noncomputable def feedbackVertexSetLineGraphPlanarCubicBipartiteDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := FeedbackVertexSetInstance) x with
  | some i => decide (WellFormed i ∧ FeedbackVertexSetFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetLineGraphPlanarCubicBipartite
