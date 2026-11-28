/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DIRECTED SUBGRAPH ISOMORPHISM (G acyclic, H a directed tree) is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT48] SUBGRAPH ISOMORPHISM, comment:
"Variant for directed graphs is also NP-complete, even if G is acyclic and H is a directed tree
[Aho and Sethi, 1977]" (A. V. Aho and R. Sethi, 1977, as cited there; the original was not
available).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.DirectedSubgraphIsomorphismAcyclicTreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DirectedSubgraphIsomorphismAcyclicTree

/-!
# DIRECTED SUBGRAPH ISOMORPHISM (G acyclic, H a directed tree) is NP-complete

INSTANCE: directed graphs `G = (V₁, A₁)` and `H = (V₂, A₂)`, where `G` is acyclic and `H` is a
directed tree.
QUESTION: does `G` contain a subgraph isomorphic to `H`, i.e., a subset `V ⊆ V₁` and a subset
`A ⊆ A₁` with `|V| = |V₂|`, `|A| = |A₂|`, and a one-to-one function `f : V₂ → V` with
`(u, v) ∈ A₂` if and only if `(f(u), f(v)) ∈ A`?

This is the directed variant of SUBGRAPH ISOMORPHISM ([GT48], `SubgraphIsomorphismWanted`) under
the restriction printed in Garey and Johnson's comment, attributed to Aho and Sethi. Taking `A`
to be the image of `A₂`, the question is equivalent to: there is a one-to-one `f : V₂ → V₁` such
that `(f(u), f(v)) ∈ A₁` for every arc `(u, v) ∈ A₂`.

The vertices of `G` are `0, …, n₁ - 1` and those of `H` are `0, …, n₂ - 1`; arcs are lists of
ordered pairs without repetitions or loops. "Acyclic" (no directed cycle) is stated as the
existence of a topological order: a permutation of the vertices of `G` along which every arc of
`G` goes forward. "Directed tree" is read as in Garey and Johnson, who say "rooted directed
tree" when they mean one ([GT41]): a directed graph whose underlying undirected graph is a tree
(Mathlib's `SimpleGraph.IsTree` of `Cslib.Complexity.Karp.edgeGraph` on the arcs, with no pair
of antiparallel arcs, so that each tree edge carries exactly one arc).

Membership in NP: the map `f` is a certificate; acyclicity and the tree condition are checked in
polynomial time. `H` has `n₂ ≥ 1` vertices (a tree is nonempty), so `n₂` is at most the length of
its arc list plus one; vertices of `G` outside its arc list are isolated and cannot carry an arc
of `H`, so a certificate uses only the vertices of `G` on arcs, apart from the single vertex of a
one-vertex `H`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **DIRECTED SUBGRAPH ISOMORPHISM (G acyclic, H a directed tree) is NP-complete.** Source:
Garey and Johnson (1979), [GT48]; Aho and Sethi (1977). -/
public theorem_wanted directedSubgraphIsomorphismAcyclicTree_npComplete :
    directedSubgraphIsomorphismAcyclicTreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L directedSubgraphIsomorphismAcyclicTreeDec

end MetaMathlibExt.Complexity.NPComplete.DirectedSubgraphIsomorphismAcyclicTree
