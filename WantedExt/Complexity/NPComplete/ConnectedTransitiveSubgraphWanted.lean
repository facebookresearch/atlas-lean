/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CONNECTED TRANSITIVE SUBGRAPH is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT29] TRANSITIVE SUBGRAPH, comment;
M. Yannakakis, "Node- and edge-deletion NP-complete problems", Proceedings of
the 10th Annual ACM Symposium on Theory of Computing (STOC 1978), 253-264,
doi:10.1145/800133.804355 (Theorem 15 and the closing remark of Section 4).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ConnectedTransitiveSubgraphDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ConnectedTransitiveSubgraph

/-!
# CONNECTED TRANSITIVE SUBGRAPH is NP-complete

INSTANCE: a directed graph `G = (V, A)` (no loops, no multiple arcs) and a positive integer
`K ≤ |A|`. QUESTION: is there a subset `A' ⊆ A` with `|A'| ≥ K` such that `G' = (V, A')` is
transitive, i.e., `(u, w), (w, v) ∈ A'` imply `(u, v) ∈ A'`, and connected?

This is the variant of TRANSITIVE SUBGRAPH
(`WantedExt.Complexity.NPComplete.TransitiveSubgraphWanted`, Garey and Johnson [GT29]) recorded
in the [GT29] comment: "For both problems, the variant in
which we require the subgraph to be connected is also NP-complete." Yannakakis (1978),
Theorem 15: "The edge-deletion 'transitive-digraph' problem is NP-complete", and at the end of
his Section 4: "for all the above properties the edge deletion problem remains NP-complete if
we [include] a connectivity requirement".

The instance type, the digraph, `TransitiveSubgraph.WellFormed` (a loopless, duplicate-free arc
list on `Fin n` and `0 < K ≤ |A|`), the subdigraph `H ≤ G`, its arc count and transitivity are
as in TRANSITIVE SUBGRAPH. `G' = (V, A')` keeps every vertex, as in Garey and Johnson's question
and in Yannakakis's edge-deletion problems. Connectivity of the digraph is weak connectivity:
the underlying undirected graph `H.toSimpleGraphInclusive` (Mathlib's orientation-forgetting
map: an edge `{u, v}` whenever `u ≠ v` and `u → v` or `v → u` is an arc) is connected (Mathlib's
`SimpleGraph.Connected`). Strong connectivity
cannot be meant: in a transitive digraph every directed path `u → ⋯ → v` gives an arc `u → v`,
so a strongly connected transitive `G'` with two vertices would contain arcs `u → v` and
`v → u`, hence the loop `u → u`, which `A` does not contain. A connected `(V, A')` has
`|V| ≤ |A'| + 1`, so yes-instances have `n ≤ |A| + 1` and the binary vertex count does not
affect membership in NP.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **CONNECTED TRANSITIVE SUBGRAPH is NP-complete.** Source: Garey and Johnson (1979), [GT29],
comment; Yannakakis (1978), Theorem 15 and the end of Section 4. -/
public theorem_wanted connectedTransitiveSubgraph_npComplete :
    connectedTransitiveSubgraphDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L connectedTransitiveSubgraphDec

end MetaMathlibExt.Complexity.NPComplete.ConnectedTransitiveSubgraph
