/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM MAX-FLOW SPANNING TREE: definitions

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide" (fourteenth edition), Journal of
Algorithms 6 (1985), 145-159, problem [1] MINIMUM MAX-FLOW SPANNING TREE;
P. M. Camerini, G. Galbiati and F. Maffioli, "Complexity of spanning tree problems: Part I",
European Journal of Operational Research 5(5) (1980), 346-352,
doi:10.1016/0377-2217(80)90164-2.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import CSLibExt.Complexity.NPComplete.ShortestTotalPathLengthSpanningTreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumMaxFlowSpanningTree

open ShortestTotalPathLengthSpanningTree (ShortestTotalPathLengthSpanningTreeInstance Graph
  WellFormed)

open Classical in
/-- The number of unordered pairs `{x, y}` of vertices (each counted once, as `x < y`) that are
not connected in `T` after the edge `{u, v}` is removed, including pairs already disconnected.
When `T` is a spanning tree and `{u, v}` is one of its edges, this is the flow on that edge. -/
noncomputable def edgeFlow {n : ℕ} (T : SimpleGraph (Fin n)) (u v : Fin n) : ℕ :=
  (Finset.univ.filter fun p : Fin n × Fin n =>
    p.1 < p.2 ∧ ¬ (T.deleteEdges {s(u, v)}).Reachable p.1 p.2).card

/-- A spanning tree `T ≤ G` in which the flow on every edge is at most `B`. -/
def MinimumMaxFlowSpanningTreeFeasible (i : ShortestTotalPathLengthSpanningTreeInstance) :
    Prop :=
  ∃ T : SimpleGraph (Fin i.1), T ≤ Graph i ∧ T.IsTree ∧
    ∀ u v, T.Adj u v → edgeFlow T u v ≤ i.2.2

open Classical in
/-- MINIMUM MAX-FLOW SPANNING TREE as a decision problem over bitstrings. -/
noncomputable def minimumMaxFlowSpanningTreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ShortestTotalPathLengthSpanningTreeInstance) x with
  | some i => decide (WellFormed i ∧ MinimumMaxFlowSpanningTreeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MinimumMaxFlowSpanningTree
