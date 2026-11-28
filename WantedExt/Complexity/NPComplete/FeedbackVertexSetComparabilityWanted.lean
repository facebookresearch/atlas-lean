/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FEEDBACK VERTEX SET on comparability graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT7] FEEDBACK VERTEX SET, the problem
restricted here;
A. Brandstädt, S. Brito, S. Klein, L. T. Nogueira and F. Protti, "Cycle transversals in perfect
graphs and cographs", Theoretical Computer Science 469 (2013), 15-23,
doi:10.1016/j.tcs.2012.10.030.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.FeedbackVertexSetComparabilityDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetComparability

open MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSet

/-!
# FEEDBACK VERTEX SET on comparability graphs is NP-complete

INSTANCE: a comparability graph `G = (V, E)` (finite, simple, undirected) and a nonnegative
integer `K`.
QUESTION: is there a set `V' ⊆ V` with `|V'| ≤ K` such that `G - V'` is a forest, that is,
`V'` meets every cycle of `G`?

A comparability graph is a graph with a transitive orientation, i.e. the comparability graph of a
partial order; this is `ComparabilityGraphSandwich.IsComparabilityGraph` from
`WantedExt.Complexity.NPComplete.ComparabilityGraphSandwichWanted` (some strict partial order `r`
on the vertices, Mathlib's `IsStrictOrder`, makes two vertices adjacent exactly when they are
comparable under `r`). The instance, its well-formedness and the question are those of the
undirected FEEDBACK VERTEX SET (`WantedExt.Complexity.NPComplete.FeedbackVertexSetWanted`: a
simple graph on `Fin n` given by an edge list and the bound `K`; the question asks for at most
`K` vertices whose removal leaves an acyclic induced subgraph, Mathlib's
`SimpleGraph.IsAcyclic`). The restriction adds that the graph is a comparability graph (ISGCI
class `gc_72`).

Every bipartite graph is a comparability graph: ordering each vertex of one side below its
neighbors on the other side is a strict partial order (there are no chains of length 2, so
transitivity holds vacuously) whose comparable pairs are exactly the edges. Brandstädt, Brito,
Klein, Nogueira and Protti prove that finding a minimum cycle transversal (a feedback vertex set)
is NP-hard even for bipartite graphs with maximum degree four; the graphs their reduction outputs
are bipartite, hence comparability graphs, so it is a reduction to this problem. Membership in
NP: the certificate is `V'` together with a transitive orientation of `G` (one direction for each
edge); the verifier checks that the orientation is transitive and that `G - V'` is acyclic, both
in polynomial time.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **FEEDBACK VERTEX SET on comparability graphs is NP-complete.** Source: Garey and Johnson
(1979), [GT7]; Brandstädt, Brito, Klein, Nogueira and Protti (2013). -/
public theorem_wanted feedbackVertexSetComparability_npComplete :
    feedbackVertexSetComparabilityDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L feedbackVertexSetComparabilityDec

end MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetComparability
