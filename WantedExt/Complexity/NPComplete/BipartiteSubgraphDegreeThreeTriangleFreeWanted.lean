/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BIPARTITE SUBGRAPH on triangle-free graphs of maximum degree 3 is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT25] BIPARTITE SUBGRAPH, comment:
"Remains NP-complete for graphs with no vertex degree exceeding 3 and no triangles";
M. Yannakakis, "Node- and edge-deletion NP-complete problems", Proceedings of
the 10th Annual ACM Symposium on Theory of Computing (STOC 1978), 253-264,
doi:10.1145/800133.804355 (Theorem 13).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BipartiteSubgraphDegreeThreeTriangleFree

/-!
# BIPARTITE SUBGRAPH on triangle-free graphs of maximum degree 3 is NP-complete

INSTANCE: a graph `G = (V, E)` with no vertex degree exceeding 3 and no triangles, and a
positive integer `K ≤ |E|`. QUESTION: is there a subset `E' ⊆ E` with `|E'| ≥ K` such that
`G' = (V, E')` is bipartite?

This is BIPARTITE SUBGRAPH (Garey and Johnson [GT25]; on `main` as the equivalent `MaxCutWanted`)
restricted as in the [GT25] comment, which credits the restriction to [Yannakakis, 1978b].
Yannakakis (1978), Theorem 13: "The edge-deletion 'bipartite' (simple max-cut) problem on cubic
graphs is NP-complete". Triangles are then removed by replacing every edge `uv` of a cubic graph by
a path `u a b v` through two new vertices: degrees stay at most 3, the new graph has no triangles,
and for every bipartition of the old vertices each such path has at most 3 crossing edges if `u` and
`v` are separated and at most 2 otherwise, both bounds attained by placing `a` and `b`
(independently for each path), so the old graph has a cut of `K` or more edges iff the new one has a
cut of `K + 2 |E|` or more edges. A cut is a bipartite spanning subgraph and the edges between the
two colour classes of a 2-colouring of a bipartite `(V, E')` form a cut containing `E'`, so the cut
question is the question above. It is in NP: `E'` is a certificate.

`E'` is a sublist of the edge list; under `WellFormed` the edge list has no duplicate edges in
either orientation, so the sublist's length is `|E'|` and the edge list's length is `|E|`.
`G' = (V, E')` is `edgeGraph n E'` on all `n` vertices, and "bipartite" is Mathlib's
`SimpleGraph.IsBipartite` (2-colorable), as in
`WantedExt.Complexity.NPComplete.ConnectedBipartiteSubgraphWanted`. The degree bound is
Mathlib's `SimpleGraph.degree` and "no triangles" is Mathlib's `SimpleGraph.CliqueFree 3`, both
on the instance graph `edgeGraph n E`.

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
abbrev BipartiteSubgraphDegreeThreeTriangleFreeInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : BipartiteSubgraphDegreeThreeTriangleFreeInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

open Classical in
/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), no vertex has degree
exceeding 3, the graph has no triangles, and `0 < K ≤ |E|`, the length of the edge list. -/
def WellFormed (i : BipartiteSubgraphDegreeThreeTriangleFreeInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    (∀ v, (Graph i).degree v ≤ 3) ∧ (Graph i).CliqueFree 3 ∧
    0 < i.2.2 ∧ i.2.2 ≤ i.2.1.length

/-- Some sublist `E'` of the edge list with at least `K` entries spans a bipartite subgraph
`(V, E')`. -/
def BipartiteSubgraphDegreeThreeTriangleFreeFeasible
    (i : BipartiteSubgraphDegreeThreeTriangleFreeInstance) : Prop :=
  ∃ es : List (ℕ × ℕ), es.Sublist i.2.1 ∧ i.2.2 ≤ es.length ∧
    (Cslib.Complexity.Karp.edgeGraph i.1 es).IsBipartite

open Classical in
/-- BIPARTITE SUBGRAPH on triangle-free graphs of maximum degree 3 as a decision problem over
bitstrings. -/
noncomputable def bipartiteSubgraphDegreeThreeTriangleFreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := BipartiteSubgraphDegreeThreeTriangleFreeInstance) x with
  | some i => decide (WellFormed i ∧ BipartiteSubgraphDegreeThreeTriangleFreeFeasible i)
  | none => false

/-- **BIPARTITE SUBGRAPH on triangle-free graphs of maximum degree 3 is NP-complete.**
Source: Garey and Johnson (1979), [GT25], comment; Yannakakis (1978), Theorem 13. -/
public theorem_wanted bipartiteSubgraphDegreeThreeTriangleFree_npComplete :
    bipartiteSubgraphDegreeThreeTriangleFreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L bipartiteSubgraphDegreeThreeTriangleFreeDec

end MetaMathlibExt.Complexity.NPComplete.BipartiteSubgraphDegreeThreeTriangleFree
