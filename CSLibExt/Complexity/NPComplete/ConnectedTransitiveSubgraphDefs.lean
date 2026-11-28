/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CONNECTED TRANSITIVE SUBGRAPH: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT29] TRANSITIVE SUBGRAPH, comment;
M. Yannakakis, "Node- and edge-deletion NP-complete problems", Proceedings of
the 10th Annual ACM Symposium on Theory of Computing (STOC 1978), 253-264,
doi:10.1145/800133.804355 (Theorem 15 and the closing remark of Section 4).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Combinatorics.Digraph.Orientation
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Set.Card
public import CSLibExt.Complexity.NPComplete.TransitiveSubgraphDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ConnectedTransitiveSubgraph

/-- Some subdigraph `H ≤ G` on the same vertices has at least `K` arcs, a transitive arc
relation, and a connected underlying undirected graph. -/
def ConnectedTransitiveSubgraphFeasible (i : TransitiveSubgraph.TransitiveSubgraphInstance) :
    Prop :=
  ∃ H : Digraph (Fin i.1), H ≤ TransitiveSubgraph.Graph i ∧
    i.2.2 ≤ {a : Fin i.1 × Fin i.1 | H.Adj a.1 a.2}.ncard ∧ IsTrans (Fin i.1) H.Adj ∧
      H.toSimpleGraphInclusive.Connected

open Classical in
/-- CONNECTED TRANSITIVE SUBGRAPH as a decision problem over bitstrings. -/
noncomputable def connectedTransitiveSubgraphDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TransitiveSubgraph.TransitiveSubgraphInstance) x with
  | some i => decide (TransitiveSubgraph.WellFormed i ∧ ConnectedTransitiveSubgraphFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ConnectedTransitiveSubgraph
