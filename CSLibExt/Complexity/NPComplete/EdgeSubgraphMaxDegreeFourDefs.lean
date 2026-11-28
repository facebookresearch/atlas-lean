/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EDGE-SUBGRAPH on graphs of maximum degree 4: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT28] EDGE-SUBGRAPH, comment:
"Remains NP-complete even if `G` has no vertex with degree exceeding 4";
M. Yannakakis, "Node- and edge-deletion NP-complete problems", Proceedings of
the 10th Annual ACM Symposium on Theory of Computing (STOC 1978), 253-264,
doi:10.1145/800133.804355 (Theorem 12).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Set.Card
public import CSLibExt.Complexity.NPComplete.EdgeSubgraphDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EdgeSubgraphMaxDegreeFour



open EdgeSubgraph (EdgeSubgraphInstance Graph EdgeSubgraphFeasible)

/-- Well-formedness of an instance: EDGE-SUBGRAPH well-formedness (a simple edge list and
`0 < K ≤ |E|`), and every vertex has at most 4 neighbours. -/
def WellFormed (i : EdgeSubgraphInstance) : Prop :=
  EdgeSubgraph.WellFormed i ∧ ∀ v, ((Graph i).neighborSet v).ncard ≤ 4

open Classical in
/-- EDGE-SUBGRAPH on graphs of maximum degree 4 as a decision problem over bitstrings. -/
noncomputable def edgeSubgraphMaxDegreeFourDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := EdgeSubgraphInstance) x with
  | some i => decide (WellFormed i ∧ EdgeSubgraphFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.EdgeSubgraphMaxDegreeFour
