/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INDEPENDENT SET on total graphs of bipartite graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT20] INDEPENDENT SET, comment:
"Remains NP-complete … for total graphs of bipartite graphs [Yannakakis and Gavril, 1978]";
M. Yannakakis and F. Gavril, "Edge dominating sets in graphs", SIAM Journal on Applied
Mathematics 38(3) (1980), 364-372, doi:10.1137/0138030.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Combinatorics.SimpleGraph.Sum
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IndependentSetTotalGraphBipartite

/-!
# INDEPENDENT SET on total graphs of bipartite graphs is NP-complete

INSTANCE: a graph `G = (V, E)` that is the total graph of some bipartite graph, and a positive
integer `K ≤ |V|`. QUESTION: does `G` contain an independent set of size `K` or more, that is,
a subset `V' ⊆ V` with `|V'| ≥ K` such that no two vertices of `V'` are joined by an edge in
`E`?

The total graph `T(H)` of a graph `H` has the vertices and the edges of `H` as its vertices; two
of them are adjacent when they are adjacent or incident in `H`: two vertices joined by an edge
of `H`, two distinct edges of `H` with a common endpoint, or a vertex and an edge containing it
(M. Behzad, "A criterion for the planarity of the total graph of a graph", Mathematical
Proceedings of the Cambridge Philosophical Society 63(3) (1967), 679-681,
doi:10.1017/S0305004100041657). `WellFormed` writes it with Mathlib constructions on
`V(H) ⊕ E(H)`: the disjoint sum `H ⊕g H.lineGraph` (vertex-vertex adjacency in `H`, edge-edge
adjacency in Mathlib's `SimpleGraph.lineGraph`), joined (`⊔`) with the incidence edges between a
vertex `a` and an edge `e ∋ a` (`SimpleGraph.fromRel`).
"Bipartite" is Mathlib's `SimpleGraph.IsBipartite` (2-colorable), and "is the total graph of"
means isomorphic to it (Mathlib's `SimpleGraph.Iso`).

Hardness: Yannakakis and Gavril prove EDGE DOMINATING SET NP-complete on bipartite graphs of maximum
degree 3 and derive, as a corollary, that MINIMUM MAXIMAL MATCHING is NP-complete
(`MinimumMaximalMatchingBipartiteDegreeThreeWanted`); their abstract records "an observed
relationship between edge dominating sets and independent sets in total graphs". The relationship is
`α(T(H)) = |V(H)| - μ(H)`, with `μ(H)` the minimum size of a maximal matching of `H`. If `M` is a
maximal matching, the vertices it leaves uncovered are pairwise non-adjacent, so they form, together
with `M`, an independent set of `T(H)` of size `|V(H)| - |M|`. Conversely, an independent set of
`T(H)` is a set `S` of vertices and a matching `M` with no vertex of `S` covered by `M` and no edge
of `H` inside `S`; extend `M` to a maximal matching `M'`; the edges of `M'` outside `M` are
disjoint, avoid the vertices covered by `M`, and each has an endpoint outside `S`, so
`|S| ≤ |V(H)| - 2 |M| - |M' - M|`, that is, `|S| + |M| ≤ |V(H)| - |M'|`. So `H` has a maximal
matching of size at most `J` iff `T(H)` has an independent set of size `|V(H)| - J` or more, and
`T(H)` is computed in polynomial time. Membership in NP: `n` is binary, so the certificate covers
only the non-isolated vertices of `G`, at most `2 |E|` of them. An edge of `H` is adjacent in `T(H)`
to its two endpoints, so the isolated vertices of `T(H)` are exactly the isolated vertices of `H`,
and the subgraph of `T(H)` induced by its non-isolated vertices is `T` of `H` without its isolated
vertices; adding isolated vertices to `H` adds them to `T(H)` and keeps `H` bipartite. Hence `G` is
the total graph of a bipartite graph iff the subgraph induced by its non-isolated vertices is. The
certificate is a bipartite `H` for that subgraph, a 2-colouring, the isomorphism, and the part `S`
of `V'` among the non-isolated vertices, checked against `|S| + (n - c) ≥ K` with `c` the number of
non-isolated vertices (isolated vertices can always join an independent set).

The instance, the graph and the question follow
`WantedExt.Complexity.NPComplete.TriangleFreeIndependentSetWanted`: a vertex count `n`
(vertices `Fin n`), an edge list and the bound `K`; the independent set is a `Finset` whose
coercion is Mathlib's `SimpleGraph.IsIndepSet`.

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
abbrev IndependentSetTotalGraphBipartiteInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : IndependentSetTotalGraphBipartiteInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n`, the graph
is isomorphic to the total graph of a bipartite graph `H` (on vertices `Fin m`): the disjoint sum
of `H` and its line graph, together with the edges joining each vertex `a` of `H` to each edge
`e` of `H` containing it; and `0 < K ≤ |V|`. -/
def WellFormed (i : IndependentSetTotalGraphBipartiteInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    (∃ (m : ℕ) (H : SimpleGraph (Fin m)), H.IsBipartite ∧
      Nonempty (Graph i ≃g (H ⊕g H.lineGraph) ⊔ SimpleGraph.fromRel fun x y =>
        ∃ (a : Fin m) (e : H.edgeSet), x = Sum.inl a ∧ y = Sum.inr e ∧ a ∈ (e : Sym2 (Fin m)))) ∧
    0 < i.2.2 ∧ i.2.2 ≤ i.1

/-- Some set of at least `K` vertices contains no two adjacent vertices. -/
def IndependentSetTotalGraphBipartiteFeasible
    (i : IndependentSetTotalGraphBipartiteInstance) : Prop :=
  ∃ s : Finset (Fin i.1), i.2.2 ≤ s.card ∧ (Graph i).IsIndepSet (s : Set (Fin i.1))

open Classical in
/-- INDEPENDENT SET on total graphs of bipartite graphs as a decision problem over
bitstrings. -/
noncomputable def independentSetTotalGraphBipartiteDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := IndependentSetTotalGraphBipartiteInstance) x with
  | some i => decide (WellFormed i ∧ IndependentSetTotalGraphBipartiteFeasible i)
  | none => false

/-- **INDEPENDENT SET on total graphs of bipartite graphs is NP-complete.**
Source: Garey and Johnson (1979), [GT20], comment; Yannakakis and Gavril (1980). -/
public theorem_wanted independentSetTotalGraphBipartite_npComplete :
    independentSetTotalGraphBipartiteDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L independentSetTotalGraphBipartiteDec

end MetaMathlibExt.Complexity.NPComplete.IndependentSetTotalGraphBipartite
