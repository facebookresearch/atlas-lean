/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TREEWIDTH is NP-complete

Source:
S. Arnborg, D. G. Corneil and A. Proskurowski, "Complexity of finding embeddings in a k-tree",
SIAM Journal on Algebraic and Discrete Methods 8 (1987), 277-284, doi:10.1137/0608024;
H. L. Bodlaender, É. Bonnet, L. Jaffke, D. Knop, P. T. Lima, M. Milanič, S. Ordyniak, S. Pandey
and O. Suchý, "Treewidth is NP-complete on cubic graphs (and related results)", arXiv:2301.10031
(Section 2: the definitions of tree decompositions, width and treewidth used below, the decision
problem TREEWIDTH, and the attribution of its NP-completeness to Arnborg, Corneil and
Proskurowski; journal version: Electronic Journal of Combinatorics 32(3) (2025), #P3.36,
doi:10.37236/13205).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.TreewidthDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Treewidth

/-!
# TREEWIDTH is NP-complete

INSTANCE: a graph `G = (V, E)` and an integer `K`. QUESTION: is the treewidth of `G` at most
`K`?

Following Bodlaender et al. (Section 2): a tree decomposition of `G` is a pair `(T, β)` such
that `T` is a tree and `β` assigns each node `x` of `T` a bag `β(x) ⊆ V(G)`, satisfying: every
vertex of `G` belongs to some bag, for every edge of `G` there exists a bag containing both
endpoints of the edge, and for every vertex `v` of `G` the set of nodes `x` of `T` such that
`v ∈ β(x)` induces a connected subtree of `T`. The width of `(T, β)` is the maximum over the
nodes `x` of `|β(x)| - 1`, and the treewidth `tw(G)` is the minimum width of a tree
decomposition of `G`. So `tw(G) ≤ K` exactly when some tree decomposition has all bags of size
at most `K + 1`. Arnborg, Corneil and Proskurowski state the problem for partial `k`-trees
(subgraphs of `k`-trees), the graphs of treewidth at most `k`.

The graph is given by an edge list on `Fin n`. The tree is a Mathlib `SimpleGraph` on `Fin N`
nodes for some `N` (`SimpleGraph.IsTree`), the bags are `Finset`s of vertices, and "induces a
connected subtree" is Mathlib's `Connected` for the subgraph of `T` induced on
`{x | v ∈ β x}`. `K` ranges over `ℕ` (Bodlaender et al.: "an integer `k`"; a negative `k`
admits only the graph with no vertices, at `k = -1`). Isolated vertices do not
change the answer (each can be put in a new one-vertex bag attached to any node), so the binary
vertex count does not make the problem succinct.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **TREEWIDTH is NP-complete.** Source: Arnborg, Corneil and Proskurowski (1987); Bodlaender et
al. (2025), Section 2. -/
public theorem_wanted treewidth_npComplete :
    treewidthDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L treewidthDec

end MetaMathlibExt.Complexity.NPComplete.Treewidth
