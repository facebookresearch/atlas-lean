/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STEINER TREE IN GRAPHS (unit weights) for undirected path graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND12] STEINER TREE IN GRAPHS (the
parent problem);
C. M. H. de Figueiredo, A. A. de Melo, D. Sasaki and A. Silva, "Revising Johnson's table for the
21st century", Discrete Applied Mathematics 323 (2022), 184-200, doi:10.1016/j.dam.2021.05.021
(arXiv:2104.14395), Section 4, Corollary 5 ("STEINER TREE is NP-complete when restricted to
undirected path graphs of diameter at most 3"), and Table 1 (STEINER TREE on UNDIRECTED PATH
graphs: N Thm. 4).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.SteinerTreeUndirectedPathGraphsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SteinerTreeUndirectedPathGraphs

open SteinerTree (SteinerTreeInstance SteinerTreeFeasible)

/-!
# STEINER TREE IN GRAPHS (unit weights) for undirected path graphs is NP-complete

INSTANCE: an undirected path graph `G = (V, E)`, that is, the vertex intersection graph of a
family of paths in an undirected tree, a set `R ⊆ V` of terminals and a positive integer `K`.
QUESTION: is there a subtree of `G` containing every vertex of `R` and having at most `K` edges?

This is STEINER TREE IN GRAPHS ([ND12], `SteinerTreeWanted`) with unit edge weights, restricted
to undirected path graphs. De Figueiredo, de Melo, Sasaki and Silva prove the unweighted problem
NP-complete for undirected path graphs (Corollary 5, from CONNECTED DOMINATING SET on undirected
path graphs, their Theorem 4, by the transformation of White, Farber and Pulleyblank, which keeps
the graph). Their question bounds the number of Steiner vertices `|S|` by `k`; a tree spanning
`S ∪ R` has `|S| + |R| - 1` edges, so their instance `(G, R, k)` is equivalent to ours with
`K = k + |R| - 1`. The instance (vertex count, weighted edge list, terminals, budget), the parent's
well-formedness and the question (a sub-list of the edges of total weight at most `K` connecting
all terminals; a minimal such edge set is a tree) are the parent's, as in
`SteinerTreeSplitGraphsWanted`; the restriction adds to `WellFormed` that every edge has weight
`1`, that the graph `SteinerTree.Graph i i.2.1` is an undirected path graph, that it has at least
one vertex (`0 < n`: the empty graph has no subtree, as in `SteinerTreeChordalBipartiteWanted`), and
`0 < K` (the source's "positive integer").

"Undirected path graph" is the repository's predicate
`DominatingSetUndirectedPathGraphs.IsUndirectedPathGraph` (also used by
`UndirectedPathGraphHamiltonianCircuitWanted`): for some finite tree `T` (Mathlib's
`SimpleGraph.IsTree`) each vertex `v` has the vertex set `P v` of a path in `T` (a
`SimpleGraph.Walk` with `IsPath`), and distinct vertices are adjacent exactly when their paths
share a vertex of `T`.

Membership in NP holds for STEINER TREE IN GRAPHS, and undirected path graphs are recognized in
polynomial time (Gavril, "A recognition algorithm for the intersection graphs of paths in
trees", Discrete Mathematics 23 (1978), 211-227, doi:10.1016/0012-365X(78)90070-5). Vertices
outside the edge list are isolated; they do not affect membership in the class (an isolated
vertex takes a path consisting of a new leaf of `T`), and an isolated terminal makes the instance
a no-instance unless it is the only terminal, so the check runs on the non-isolated vertices and
the binary vertex count does not make the problem succinct.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **STEINER TREE IN GRAPHS (unit weights) for undirected path graphs is NP-complete.**
Source: de Figueiredo, de Melo, Sasaki and Silva (2022), Corollary 5. -/
public theorem_wanted steinerTreeUndirectedPathGraphs_npComplete :
    steinerTreeUndirectedPathGraphsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L steinerTreeUndirectedPathGraphsDec

end MetaMathlibExt.Complexity.NPComplete.SteinerTreeUndirectedPathGraphs
