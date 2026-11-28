/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# WEAK BISPLIT GRAPH RECOGNITION is NP-complete

Source:
A. Brandstädt, P. L. Hammer, V. B. Le and V. V. Lozin, "Bisplit graphs", Discrete Mathematics
299 (2005), 11-32, doi:10.1016/j.disc.2004.08.046 (Section 4: the definitions of `k`-bisplit and
weak bisplit graphs; Theorem 15: "Recognizing weak bisplit graphs is NP-complete, even for
3-colorable comparability graphs"; earlier version: Rutcor Research Report RRR 28-2002).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.WeakBisplitRecognitionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.WeakBisplitRecognition

/-!
# WEAK BISPLIT GRAPH RECOGNITION is NP-complete

INSTANCE: a graph `G = (V, E)`.
QUESTION: is `G` a weak bisplit graph, that is, does `G` have a stable set `X` such that every
connected component of `G[V \ X]` is a bi-clique?

Brandstädt, Hammer, Le and Lozin (Section 4): "a graph `G` is `k`-bisplit if it has a stable set
`X` such that the induced subgraph `G[V \ X]` has at most `k` connected components, and all these
are bi-cliques. Note that the set of all isolated vertices in `G[V \ X]` is considered as a
single bi-clique. Recall also that a graph `G` is a weak bisplit graph if it is `k`-bisplit for
some `k`." A bi-clique is a complete bipartite graph; as the set of isolated vertices counts as
one bi-clique, a component that is a single vertex is allowed. ISGCI (class `gc_457`) states the
same class: "`G` is weak bisplit iff it has an independent set `X` such that every connected
component of `G - X` is a biclique", and records its recognition as NP-complete, citing this
paper.

The graph is given by an edge list on `Fin n`. The stable set `X` is a `Finset` with Mathlib's
`SimpleGraph.IsIndepSet`, and `G[V \ X]` is Mathlib's `G.induce` on the complement of `X`. A
connected component `C` of `G[V \ X]` is a bi-clique exactly when its vertices split into two
sides with two vertices of `C` adjacent if and only if they lie on different sides (both sides
are then independent, every cross pair is an edge, and a single vertex is the case of an empty
side). The sides of all components are given at once by `s : Fin n → Bool`: two vertices of
`G[V \ X]` joined by a path in `G[V \ X]` (Mathlib's `Reachable`, that is, in the same connected
component) are adjacent exactly when `s` differs on them (`IsWeakBisplit`). Membership in NP,
although the vertex count `n` is written in binary: an isolated vertex of `G` can always be put
in `X`, so `X` and `s` restricted to the at most `2|E|` endpoints of edges are a certificate of
size polynomial in the length of the edge list.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **WEAK BISPLIT GRAPH RECOGNITION is NP-complete.** Source: Brandstädt, Hammer, Le and Lozin
(2005), Theorem 15. -/
public theorem_wanted weakBisplitRecognition_npComplete :
    weakBisplitRecognitionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L weakBisplitRecognitionDec

end MetaMathlibExt.Complexity.NPComplete.WeakBisplitRecognition
