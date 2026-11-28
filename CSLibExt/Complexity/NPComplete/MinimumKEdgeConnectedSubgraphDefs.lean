/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM K-EDGE-CONNECTED SUBGRAPH: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT31] MINIMUM K-CONNECTED SUBGRAPH,
comment ("Corresponding edge-connectivity problem is also NP-complete"), credited to F. R. K. Chung
and R. L. Graham (1977, private communication);
S. Khuller and U. Vishkin, "Biconnectivity approximations and graph carvings", Journal of the ACM
41 (1994), 214-235, doi:10.1145/174652.174654.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.EdgeConnectivity
public import CSLibExt.Complexity.NPComplete.MinimumKConnectedSubgraphDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumKEdgeConnectedSubgraph

open MinimumKConnectedSubgraph (MinimumKConnectedSubgraphInstance Graph WellFormed)

/-- Some spanning subgraph `H ≤ G` has at most `B` edges and is `K`-edge-connected: any two
vertices stay reachable after deleting any set of fewer than `K` edges. -/
def MinimumKEdgeConnectedSubgraphFeasible (i : MinimumKConnectedSubgraphInstance) : Prop :=
  ∃ H : SimpleGraph (Fin i.1), H ≤ Graph i ∧ H.edgeSet.ncard ≤ i.2.2.2 ∧
    H.IsEdgeConnected (i.2.2.1 : ℕ∞)

open Classical in
/-- MINIMUM K-EDGE-CONNECTED SUBGRAPH as a decision problem over bitstrings. -/
noncomputable def minimumKEdgeConnectedSubgraphDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumKConnectedSubgraphInstance) x with
  | some i => decide (WellFormed i ∧ MinimumKEdgeConnectedSubgraphFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MinimumKEdgeConnectedSubgraph
