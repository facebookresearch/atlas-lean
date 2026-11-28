/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CONNECTED OUTERPLANAR SUBGRAPH: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT27] PLANAR SUBGRAPH, comment:
"The related problem in which we ask if `G` contains a connected "outerplanar" subgraph with
`K` or more edges is also NP-complete";
M. Yannakakis, "Node- and edge-deletion NP-complete problems", Proceedings of
the 10th Annual ACM Symposium on Theory of Computing (STOC 1978), 253-264,
doi:10.1145/800133.804355 (Theorem 10 and the closing remark of Section 4).
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import MathlibExt.GraphTheory.BookThicknessOfSubdivisionsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ConnectedOuterplanarSubgraph

open MathlibExt.GraphTheory.BookThicknessOfSubdivisionsWanted (HasBookEmbedding)

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, bound `K`. -/
abbrev ConnectedOuterplanarSubgraphInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), and
`0 < K ≤ |E|`, the length of the edge list. -/
def WellFormed (i : ConnectedOuterplanarSubgraphInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    0 < i.2.2 ∧ i.2.2 ≤ i.2.1.length

/-- Some sublist `E'` of the edge list with at least `K` entries forms, on the endpoints of its
edges, a connected outerplanar graph. -/
def ConnectedOuterplanarSubgraphFeasible (i : ConnectedOuterplanarSubgraphInstance) : Prop :=
  ∃ es : List (ℕ × ℕ), es.Sublist i.2.1 ∧ i.2.2 ≤ es.length ∧
    ((Cslib.Complexity.Karp.edgeGraph i.1 es).induce
        (Cslib.Complexity.Karp.edgeGraph i.1 es).support).Connected ∧
      HasBookEmbedding ((Cslib.Complexity.Karp.edgeGraph i.1 es).induce
        (Cslib.Complexity.Karp.edgeGraph i.1 es).support) 1

open Classical in
/-- CONNECTED OUTERPLANAR SUBGRAPH as a decision problem over bitstrings. -/
noncomputable def connectedOuterplanarSubgraphDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ConnectedOuterplanarSubgraphInstance) x with
  | some i => decide (WellFormed i ∧ ConnectedOuterplanarSubgraphFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ConnectedOuterplanarSubgraph
