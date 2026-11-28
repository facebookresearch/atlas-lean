/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CONNECTED BIPARTITE SUBGRAPH: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT25] BIPARTITE SUBGRAPH, comment:
"Remains NP-complete … if we require that the subgraph be connected";
M. Yannakakis, "Node- and edge-deletion NP-complete problems", Proceedings of
the 10th Annual ACM Symposium on Theory of Computing (STOC 1978), 253-264,
doi:10.1145/800133.804355 (Theorem 13 and the closing remark of Section 4).
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ConnectedBipartiteSubgraph

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, bound `K`. -/
abbrev ConnectedBipartiteSubgraphInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), and
`0 < K ≤ |E|`, the length of the edge list. -/
def WellFormed (i : ConnectedBipartiteSubgraphInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    0 < i.2.2 ∧ i.2.2 ≤ i.2.1.length

/-- Some sublist `E'` of the edge list with at least `K` entries spans a connected bipartite
subgraph `(V, E')`. -/
def ConnectedBipartiteSubgraphFeasible (i : ConnectedBipartiteSubgraphInstance) : Prop :=
  ∃ es : List (ℕ × ℕ), es.Sublist i.2.1 ∧ i.2.2 ≤ es.length ∧
    (Cslib.Complexity.Karp.edgeGraph i.1 es).Connected ∧
      (Cslib.Complexity.Karp.edgeGraph i.1 es).IsBipartite

open Classical in
/-- CONNECTED BIPARTITE SUBGRAPH as a decision problem over bitstrings. -/
noncomputable def connectedBipartiteSubgraphDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ConnectedBipartiteSubgraphInstance) x with
  | some i => decide (WellFormed i ∧ ConnectedBipartiteSubgraphFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ConnectedBipartiteSubgraph
