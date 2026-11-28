/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SPANNING TREE WITH AT MOST K BRANCH VERTICES is NP-complete

Source:
L. Gargano, M. Hammar, P. Hell, L. Stacho and U. Vaccaro, "Spanning spiders and
light-splitting switches", Discrete Mathematics 285 (2004), 83-95,
doi:10.1016/j.disc.2004.04.005 (Section 2).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.SpanningTreeFewBranchVerticesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SpanningTreeFewBranchVertices

/-!
# SPANNING TREE WITH AT MOST K BRANCH VERTICES is NP-complete

INSTANCE: a graph `G = (V, E)` and a nonnegative integer `K`. QUESTION: does `G` have a spanning
tree with at most `K` branch vertices, that is, vertices of degree greater than two in the tree?

Gargano, Hammar, Hell, Stacho and Vaccaro write `s(G)` for the least number of branch vertices
of a spanning tree of a connected graph `G`; `s(G) = 0` exactly when `G` has a Hamiltonian path,
and a spanning tree with at most one branch vertex is a spanning spider. They prove that
recognizing graphs with a spanning spider (`s(G) ≤ 1`) is NP-complete (Proposition 1); with `K`
part of the instance the problem contains this case (`K = 1`), and also HAMILTONIAN PATH at
`K = 0`. Membership in NP: a spanning tree is a certificate.

The graph is `edgeGraph n E` on `Fin n` for an edge list `E`. A spanning tree is a subgraph
`T ≤ G` on all of `Fin n` that is a tree (Mathlib's `SimpleGraph.IsTree`), and its branch
vertices are those with `2 < T.degree v`. A graph with no vertices has no spanning tree here,
since Mathlib's trees are nonempty.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **SPANNING TREE WITH AT MOST K BRANCH VERTICES is NP-complete.** Source: Gargano, Hammar,
Hell, Stacho and Vaccaro (2004). -/
public theorem_wanted spanningTreeFewBranchVertices_npComplete :
    spanningTreeFewBranchVerticesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L spanningTreeFewBranchVerticesDec

end MetaMathlibExt.Complexity.NPComplete.SpanningTreeFewBranchVertices
