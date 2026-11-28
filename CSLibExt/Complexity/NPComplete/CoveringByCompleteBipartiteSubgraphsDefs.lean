/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# COVERING BY COMPLETE BIPARTITE SUBGRAPHS: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT18] COVERING BY
COMPLETE BIPARTITE SUBGRAPHS;
J. Orlin, "Contentment in graph theory: covering graphs with cliques",
Indagationes Mathematicae (Proceedings) 80 (1977), 406-424,
doi:10.1016/1385-7258(77)90055-5 (NP-complete already for bipartite graphs).
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CoveringByCompleteBipartiteSubgraphs

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, bound `K`. -/
abbrev CoveringByCompleteBipartiteSubgraphsInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : CoveringByCompleteBipartiteSubgraphsInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), and
`0 < K ≤ |E|`, the length of the edge list. -/
def WellFormed (i : CoveringByCompleteBipartiteSubgraphsInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    0 < i.2.2 ∧ i.2.2 ≤ i.2.1.length

/-- The edges are covered by at most `K` complete bipartite subgraphs: for some `k ≤ K` there
are vertex sets `A j` and `B j`, `j : Fin k`, with `A j` complete to `B j` in the graph, such
that every edge has one endpoint in `A j` and the other in `B j` for some `j`. -/
def CoveringByCompleteBipartiteSubgraphsFeasible
    (i : CoveringByCompleteBipartiteSubgraphsInstance) : Prop :=
  ∃ k ≤ i.2.2, ∃ A B : Fin k → Set (Fin i.1),
    (∀ j, (Graph i).IsCompleteBetween (A j) (B j)) ∧
      ∀ u v, (Graph i).Adj u v → ∃ j, (u ∈ A j ∧ v ∈ B j) ∨ (v ∈ A j ∧ u ∈ B j)

open Classical in
/-- COVERING BY COMPLETE BIPARTITE SUBGRAPHS as a decision problem over bitstrings. -/
noncomputable def coveringByCompleteBipartiteSubgraphsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CoveringByCompleteBipartiteSubgraphsInstance) x with
  | some i => decide (WellFormed i ∧ CoveringByCompleteBipartiteSubgraphsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.CoveringByCompleteBipartiteSubgraphs
