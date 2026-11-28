/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TOTAL DOMINATING SET for undirected path graphs: definitions

Source:
R. Laskar, J. Pfaff, S. M. Hedetniemi and S. T. Hedetniemi, "On the algorithmic complexity of
total domination", SIAM Journal on Algebraic and Discrete Methods 5(3) (1984), 420-425,
doi:10.1137/0605040.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.DominatingSetUndirectedPathGraphsDefs
public import CSLibExt.Complexity.NPComplete.TotalDominatingSetDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TotalDominatingSetUndirectedPathGraphs

open MetaMathlibExt.Complexity.NPComplete.TotalDominatingSet
  (TotalDominatingSetInstance Graph TotalDominatingSetFeasible)

/-- Well-formedness of an instance: the parent's (a simple edge list on `Fin n`), `0 < K`, no
isolated vertex, and the graph is an undirected path graph. -/
def WellFormed (i : TotalDominatingSetInstance) : Prop :=
  TotalDominatingSet.WellFormed i ∧ 0 < i.2.2 ∧ (∀ v : Fin i.1, ∃ u, (Graph i).Adj v u) ∧
    DominatingSetUndirectedPathGraphs.IsUndirectedPathGraph (Graph i)

open Classical in
/-- TOTAL DOMINATING SET for undirected path graphs as a decision problem over bitstrings. -/
noncomputable def totalDominatingSetUndirectedPathGraphsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := TotalDominatingSetInstance) x with
  | some i => decide (WellFormed i ∧ TotalDominatingSetFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TotalDominatingSetUndirectedPathGraphs
