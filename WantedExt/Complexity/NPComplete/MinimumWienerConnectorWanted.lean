/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM WIENER CONNECTOR is NP-complete

Source:
N. Ruchansky, F. Bonchi, D. García-Soriano, F. Gullo and N. Kourtellis, "The minimum Wiener
connector problem", in *Proceedings of the 2015 ACM SIGMOD International Conference on
Management of Data* (2015), 1587-1602, doi:10.1145/2723372.2749449 (Problem 1 and Theorem 2;
arXiv:1504.00513).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Combinatorics.SimpleGraph.Metric

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumWienerConnector

/-!
# MINIMUM WIENER CONNECTOR is NP-complete

INSTANCE: a connected graph `G = (V, E)`, a set `Q ⊆ V` of query vertices, and a positive
integer `K`.
QUESTION: is there a set `S ⊆ V` with `Q ⊆ S` such that the induced subgraph `G[S]` is
connected and its Wiener index, the sum of the shortest-path distances `d_{G[S]}(u, v)` over all
unordered pairs `{u, v} ⊆ S`, is at most `K`?

This is the decision version of Problem 1 (Min Wiener Connector) of Ruchansky, Bonchi,
García-Soriano, Gullo and Kourtellis: "Given a graph G = (V, E) and a query set Q ⊆ V, find a
connector H* for Q in G with the smallest Wiener index", where a connector for `Q` is a
connected subgraph of `G` containing `Q`, the input graph is connected, and `W(H)` is the sum
of `d_H(u, v)` over unordered pairs `{u, v} ⊆ V(H)`. As they note, "we may restrict the search
to vertex sets and their corresponding induced subgraphs" (adding edges between chosen vertices
never increases a distance), so a connector is given by its vertex set `S` and is the induced
subgraph `G[S]`. Their Theorem 2 (a gap-preserving reduction from VERTEX COVER in bounded-degree
graphs) shows the problem NP-hard; a certificate is `S`, whose Wiener index is computed by
breadth-first search.

Distances are Mathlib's `SimpleGraph.dist` in `G.induce S`; unordered pairs are the pairs
`u < v` of `S`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `Fin n`), the edge list, the query vertices `Q`, and
the bound `K`. -/
abbrev MinimumWienerConnectorInstance := ℕ × List (ℕ × ℕ) × List ℕ × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : MinimumWienerConnectorInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- The Wiener index of the subgraph of `G` induced by `S`: the sum, over the unordered pairs
`{u, v} ⊆ S` (listed as `u < v`), of the distance between `u` and `v` in `G.induce S`. -/
noncomputable def wienerIndex {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : ℕ :=
  ∑ u ∈ S.attach, ∑ v ∈ S.attach,
    if u.1 < v.1 then
      (G.induce (S : Set (Fin n))).dist ⟨u.1, Finset.mem_coe.2 u.2⟩ ⟨v.1, Finset.mem_coe.2 v.2⟩
    else 0

/-- Well-formedness of an instance: the edge list is a simple undirected edge list on `Fin n`,
the graph is connected, the query vertices are distinct vertices, and `0 < K`. -/
def WellFormed (i : MinimumWienerConnectorInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    (Graph i).Connected ∧ i.2.2.1.Nodup ∧ (∀ q ∈ i.2.2.1, q < i.1) ∧ 0 < i.2.2.2

/-- Some vertex set `S` containing every query vertex induces a connected subgraph of Wiener
index at most `K`. -/
def MinimumWienerConnectorFeasible (i : MinimumWienerConnectorInstance) : Prop :=
  ∃ S : Finset (Fin i.1), (∀ q ∈ i.2.2.1, ∃ v ∈ S, (v : ℕ) = q) ∧
    ((Graph i).induce (S : Set (Fin i.1))).Connected ∧ wienerIndex (Graph i) S ≤ i.2.2.2

open Classical in
/-- MINIMUM WIENER CONNECTOR as a decision problem over bitstrings. -/
noncomputable def minimumWienerConnectorDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumWienerConnectorInstance) x with
  | some i => decide (WellFormed i ∧ MinimumWienerConnectorFeasible i)
  | none => false

/-- **MINIMUM WIENER CONNECTOR is NP-complete.** Source: Ruchansky, Bonchi, García-Soriano,
Gullo and Kourtellis (2015), Problem 1 and Theorem 2. -/
public theorem_wanted minimumWienerConnector_npComplete :
    minimumWienerConnectorDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumWienerConnectorDec

end MetaMathlibExt.Complexity.NPComplete.MinimumWienerConnector
