/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TOTAL DOMINATING SET for undirected path graphs is NP-complete

Source:
R. Laskar, J. Pfaff, S. M. Hedetniemi and S. T. Hedetniemi, "On the algorithmic complexity of
total domination", SIAM Journal on Algebraic and Discrete Methods 5(3) (1984), 420-425,
doi:10.1137/0605040.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.TotalDominatingSetUndirectedPathGraphsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TotalDominatingSetUndirectedPathGraphs

open MetaMathlibExt.Complexity.NPComplete.TotalDominatingSet
  (TotalDominatingSetInstance Graph TotalDominatingSetFeasible)

/-!
# TOTAL DOMINATING SET for undirected path graphs is NP-complete

INSTANCE: an undirected path graph `G = (V, E)` with no isolated vertices, that is, the vertex
intersection graph of a family of paths in an undirected tree, and a positive integer `K`.
QUESTION: does `G` have a total dominating set of size at most `K`, i.e. a set `D ⊆ V` with
`|D| ≤ K` such that every vertex of `V` (including those in `D`) is adjacent to a vertex of `D`?

Laskar, Pfaff, Hedetniemi and Hedetniemi (abstract): "A set of vertices is a total dominating
set if every vertex in V is adjacent to a vertex in D. [...] This paper presents a linear time
algorithm to determine minimum total dominating sets of a tree and shows that for undirected path
graphs the problem remains NP-complete."

This is the restriction of TOTAL DOMINATING SET (`TotalDominatingSetWanted`) to undirected path
graphs. The instance type, the graph, the well-formedness (a simple edge list on `Fin n`) and the
question are the parent's (`TotalDominatingSet.TotalDominatingSetInstance`,
`TotalDominatingSet.Graph`, `TotalDominatingSet.WellFormed`,
`TotalDominatingSet.TotalDominatingSetFeasible`); `WellFormed` adds the usual instance conditions of
total domination, `0 < K` and no isolated vertex (every vertex has a neighbor; a graph with an
isolated vertex has no total dominating set), and the class restriction
`DominatingSetUndirectedPathGraphs.IsUndirectedPathGraph` of
`WantedExt.Complexity.NPComplete.DominatingSetUndirectedPathGraphsWanted`, reused unchanged: a
finite tree `T` (Mathlib's `SimpleGraph.IsTree`) and, for each vertex `v`, the vertex set `P v` of
a path in `T` (a `SimpleGraph.Walk` with `IsPath`), such that two distinct vertices are adjacent
exactly when their paths share a vertex of `T`. Without isolated vertices `n ≤ 2|E|`, although `n`
is written in binary, and a model whose host tree has at most `max 1 n` nodes (a clique tree;
`IsTree` needs at least one node, also when `n = 0`) plus the set `D` is a polynomial certificate.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **TOTAL DOMINATING SET for undirected path graphs is NP-complete.** Source: Laskar, Pfaff,
Hedetniemi and Hedetniemi (1984). -/
public theorem_wanted totalDominatingSetUndirectedPathGraphs_npComplete :
    totalDominatingSetUndirectedPathGraphsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L totalDominatingSetUndirectedPathGraphsDec

end MetaMathlibExt.Complexity.NPComplete.TotalDominatingSetUndirectedPathGraphs
