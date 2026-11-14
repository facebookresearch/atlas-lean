/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# COVERING BY COMPLETE BIPARTITE SUBGRAPHS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT18] COVERING BY
COMPLETE BIPARTITE SUBGRAPHS;
J. Orlin, "Contentment in graph theory: covering graphs with cliques",
Indagationes Mathematicae (Proceedings) 80 (1977), 406-424,
doi:10.1016/1385-7258(77)90055-5 (NP-complete already for bipartite graphs).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CoveringByCompleteBipartiteSubgraphs

/-!
# COVERING BY COMPLETE BIPARTITE SUBGRAPHS is NP-complete

INSTANCE: a graph `G = (V, E)` and a positive integer `K ≤ |E|`. QUESTION: are there `k ≤ K`
subsets `E₁, ..., Eₖ` of `E` with union `E` such that each `Eᵢ` is the edge set of a complete
bipartite subgraph of `G`? The least such `k` is the bipartite dimension (biclique cover number)
of `G`. The input graph is arbitrary; its restriction to bipartite input graphs, given with
their two sides, is `MetaMathlibExt.Complexity.NPComplete.BicliqueEdgeCover`.

A complete bipartite subgraph is given by its two sides `A j` and `B j`, with every vertex of
`A j` adjacent in `G` to every vertex of `B j` (Mathlib's `SimpleGraph.IsCompleteBetween`, which
forces the sides to be disjoint); its edge set `Eⱼ` is the set of edges `{a, b}` with `a ∈ A j`
and `b ∈ B j`, a subset of `E`. The union of the `Eⱼ` is `E` when every edge of `G` has one
endpoint in `A j` and the other in `B j` for some `j`. Empty sets `Eⱼ` are harmless because
the bound is `k ≤ K`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **COVERING BY COMPLETE BIPARTITE SUBGRAPHS is NP-complete.** Source: Garey and Johnson
(1979), [GT18]; Orlin (1977). -/
public theorem_wanted coveringByCompleteBipartiteSubgraphs_npComplete :
    coveringByCompleteBipartiteSubgraphsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L coveringByCompleteBipartiteSubgraphsDec

end MetaMathlibExt.Complexity.NPComplete.CoveringByCompleteBipartiteSubgraphs
