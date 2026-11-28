/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DOMINATING SET for split graphs: definitions

Source:
A. A. Bertossi, "Dominating sets for split and bipartite graphs", Information Processing
Letters 19(1) (1984), 37-40, doi:10.1016/0020-0190(84)90126-1;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT2] DOMINATING SET.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import CSLibExt.Complexity.NPComplete.DominatingSetDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DominatingSetSplitGraphs

/-- `G` is a split graph: some set `C` of vertices is a clique and the remaining vertices form an
independent set. -/
def IsSplitGraph {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ C : Finset (Fin n), G.IsClique (C : Set (Fin n)) ∧
    G.IsIndepSet ((Cᶜ : Finset (Fin n)) : Set (Fin n))

/-- Well-formedness of an instance: the parent's (a simple edge list on `Fin n`), the graph is
a split graph, and `0 < K ≤ n`. -/
def WellFormed (i : DominatingSet.DominatingSetInstance) : Prop :=
  DominatingSet.WellFormed i ∧ IsSplitGraph (DominatingSet.Graph i) ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.1

open Classical in
/-- DOMINATING SET for split graphs as a decision problem over bitstrings. -/
noncomputable def dominatingSetSplitGraphsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DominatingSet.DominatingSetInstance) x with
  | some i => decide (WellFormed i ∧ DominatingSet.DominatingSetFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.DominatingSetSplitGraphs
