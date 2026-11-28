/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STEINER TREE IN GRAPHS with unit weights on chordal graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND12] STEINER TREE IN GRAPHS;
K. White, M. Farber and W. Pulleyblank, "Steiner trees, connected domination and strongly chordal
graphs", Networks 15 (1985), 109-124, doi:10.1002/net.3230150109;
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 6 (1985),
434-451, doi:10.1016/0196-6774(85)90012-4, Table 1;
C. M. H. de Figueiredo, A. A. de Melo, D. Sasaki and A. Silva, "Revising Johnson's table for the
21st century", Discrete Applied Mathematics 323 (2022), 184-200,
doi:10.1016/j.dam.2021.05.021, Table 1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.SteinerTreeChordalGraphsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SteinerTreeChordalGraphs

open MetaMathlibExt.Complexity.NPComplete.SteinerTree (SteinerTreeInstance SteinerTreeFeasible)

/-!
# STEINER TREE IN GRAPHS with unit weights on chordal graphs is NP-complete

INSTANCE: a chordal graph `G = (V, E)` (every cycle of length at least `4` has a chord), a subset
`R ⊆ V` of terminals, and a positive integer `K`.
QUESTION: is there a subtree of `G` that includes all the vertices of `R` and has at most `K`
edges?

This is STEINER TREE IN GRAPHS (Garey and Johnson [ND12], `SteinerTreeWanted`) with all edge
weights equal, restricted to chordal graphs. White, Farber and Pulleyblank prove it NP-complete
on split graphs (abstract: "establish related NP-completeness results"; the split-graph result is
recorded by `SteinerTreeSplitGraphsWanted`, which quotes Illuri, Renjith and Sadagopan,
arXiv:1511.01668: "K. White et. al has established that Steiner tree in split graphs is
NP-complete"). Every split graph is chordal, so the chordal case follows. de Figueiredo,
de Melo, Sasaki and Silva (Table 1, row CHORDAL, column ST TREE) list the problem as
NP-complete, citing the entry of Johnson's Table 1 (the 1985 column itself was not available).

The instance type and the question are those of `WantedExt.Complexity.NPComplete.SteinerTreeWanted`
(`SteinerTree.SteinerTreeInstance`: a vertex count, weighted edges `(u, v, w)`, the terminals `R`
and the bound `K`; `SteinerTree.SteinerTreeFeasible`: some sublist of the edges of total weight at
most `K` connects all terminals). The restriction is added to `WellFormed`: the parent's
well-formedness, every edge weight equal to `1`, the graph of all edges
(`SteinerTree.Graph i i.2.1`) is chordal, at least one vertex (a tree is nonempty, so the empty
graph has no subtree), and `0 < K` (Garey and Johnson's positive integer bound). Chordality is
stated as in `PathwidthChordalGraphsWanted` and `DominatingSetChordalGraphsWanted`: no cycle graph
`Cₖ` with `k ≥ 4` is an induced subgraph (Mathlib's `SimpleGraph.cycleGraph` and
`SimpleGraph.IsIndContained`; a cycle has a chord exactly when its vertices do not induce a cycle
graph). With unit weights the total weight of an edge set is its number of edges, and a
connecting edge set contains a tree on the terminals with no more edges (a single vertex when `R`
is empty), so the question asks for a subtree of `G` containing `R` with at most `K` edges.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **STEINER TREE IN GRAPHS with unit weights on chordal graphs is NP-complete.** Source:
White, Farber and Pulleyblank (1985); de Figueiredo et al. (2022), Table 1. -/
public theorem_wanted steinerTreeChordalGraphs_npComplete :
    steinerTreeChordalGraphsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L steinerTreeChordalGraphsDec

end MetaMathlibExt.Complexity.NPComplete.SteinerTreeChordalGraphs
