/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PATHWIDTH OF COCOMPARABILITY GRAPHS is NP-complete

Source:
M. Habib and R. H. Möhring, "Treewidth of cocomparability graphs and a new order-theoretic
parameter", Order 11 (1994), 47-60, doi:10.1007/BF01462229 (treewidth and pathwidth coincide on
cocomparability graphs);
S. Arnborg, D. G. Corneil, and A. Proskurowski, "Complexity of finding embeddings in a k-tree",
SIAM Journal on Algebraic and Discrete Methods 8 (1987), 277-284, doi:10.1137/0608024 (NP-complete
on complements of bipartite graphs);
T. Kloks, D. Kratsch, and J. Spinrad, "Treewidth and pathwidth of cocomparability graphs of
bounded dimension", Computing Science Notes 93/46, Eindhoven University of Technology (1993)
(records both results).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.PathwidthCocomparabilityGraphsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PathwidthCocomparabilityGraphs

open MetaMathlibExt.Complexity.NPComplete.PathwidthChordalGraphs
  (PathwidthChordalGraphsInstance Graph PathwidthChordalGraphsFeasible)

/-!
# PATHWIDTH OF COCOMPARABILITY GRAPHS is NP-complete

INSTANCE: a cocomparability graph `G = (V, E)` (its complement is a comparability graph) and a
positive integer `K`.
QUESTION: does `G` have pathwidth at most `K`?

Habib and Möhring show that treewidth and pathwidth coincide on cocomparability graphs and that
computing them is NP-complete there: Arnborg, Corneil, and Proskurowski prove the problem
NP-complete on complements of bipartite graphs, which are cocomparability graphs (bipartite graphs
are comparability graphs); Kloks, Kratsch, and Spinrad record both facts. Membership in NP: a path
decomposition (and a transitive orientation of the complement) is a polynomial certificate.

The complement is Mathlib's `Gᶜ`, and comparability graphs are
`ComparabilityGraphSandwich.IsComparabilityGraph` (some strict partial order makes two vertices
adjacent exactly when they are comparable), as in `FeedbackVertexSetComparabilityWanted`.

A path decomposition of `G` is a sequence of bags `X 0, …, X (r - 1)` of vertices such that every
vertex lies in some bag, both ends of every edge lie in a common bag, and the bags containing any
one vertex are consecutive; the pathwidth of `G` is at most `K` exactly when some path decomposition
has all bags of size at most `K + 1`. The instance type, the graph, the path decompositions and the
question are reused from `PathwidthChordalGraphsWanted`
(`PathwidthChordalGraphs.PathwidthChordalGraphsInstance`, `PathwidthChordalGraphs.Graph`,
`PathwidthChordalGraphs.IsPathDecomposition`,
`PathwidthChordalGraphs.PathwidthChordalGraphsFeasible`, which says only that the pathwidth is at
most `K`); this module replaces chordality by its own graph class.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **PATHWIDTH OF COCOMPARABILITY GRAPHS is NP-complete.** Source: Habib and Möhring (1994);
Arnborg, Corneil, and Proskurowski (1987); Kloks, Kratsch, and Spinrad (1993). -/
public theorem_wanted pathwidthCocomparabilityGraphs_npComplete :
    pathwidthCocomparabilityGraphsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L pathwidthCocomparabilityGraphsDec

end MetaMathlibExt.Complexity.NPComplete.PathwidthCocomparabilityGraphs
