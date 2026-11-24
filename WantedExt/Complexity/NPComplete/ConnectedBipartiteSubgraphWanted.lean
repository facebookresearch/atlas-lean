/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CONNECTED BIPARTITE SUBGRAPH is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT25] BIPARTITE SUBGRAPH, comment:
"Remains NP-complete … if we require that the subgraph be connected";
M. Yannakakis, "Node- and edge-deletion NP-complete problems", Proceedings of
the 10th Annual ACM Symposium on Theory of Computing (STOC 1978), 253-264,
doi:10.1145/800133.804355 (Theorem 13 and the closing remark of Section 4).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ConnectedBipartiteSubgraph

/-!
# CONNECTED BIPARTITE SUBGRAPH is NP-complete

INSTANCE: a graph `G = (V, E)` and a positive integer `K ≤ |E|`. QUESTION: is there a subset
`E' ⊆ E` with `|E'| ≥ K` such that `G' = (V, E')` is connected and bipartite?

This is BIPARTITE SUBGRAPH (Garey and Johnson [GT25], on `main` as the equivalent
`MaxCutWanted`) with the connectivity requirement of the [GT25] comment, credited to
[Yannakakis, 1978b]. Yannakakis (1978) proves the edge-deletion "bipartite" (simple max cut)
problem NP-complete (Theorem 13) and closes Section 4 with "for all the above properties the
edge deletion problem remains NP-complete if we include a connectivity requirement"; the
remaining graph of an edge-deletion problem is `(V, E')`, so the connectivity requirement is on
the spanning subgraph. It is in NP: `E'` is a certificate (a connected `(V, E')` needs
`|V| ≤ |E| + 1`, so instances with more vertices are rejected at once although `|V|` is binary).

`E'` is a sublist of the edge list; under `WellFormed` the edge list has no duplicate edges in
either orientation, so the sublist's length is `|E'|` and the edge list's length is `|E|`.
`G' = (V, E')` is `edgeGraph n E'` on all `n` vertices; "connected" is Mathlib's
`SimpleGraph.Connected` and "bipartite" Mathlib's `SimpleGraph.IsBipartite` (2-colorable).

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

/-- **CONNECTED BIPARTITE SUBGRAPH is NP-complete.** Source: Garey and Johnson (1979), [GT25],
comment; Yannakakis (1978). -/
public theorem_wanted connectedBipartiteSubgraph_npComplete :
    connectedBipartiteSubgraphDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L connectedBipartiteSubgraphDec

end MetaMathlibExt.Complexity.NPComplete.ConnectedBipartiteSubgraph
