/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FEEDBACK VERTEX SET on bipartite graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT7] FEEDBACK VERTEX SET;
A. Brandstädt, S. Brito, S. Klein, L. T. Nogueira and F. Protti, "Cycle transversals in perfect
graphs and cographs", Theoretical Computer Science 469 (2013), 15-23,
doi:10.1016/j.tcs.2012.10.030.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.FeedbackVertexSetBipartiteDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetBipartite

open MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSet

/-!
# FEEDBACK VERTEX SET on bipartite graphs is NP-complete

INSTANCE: a bipartite graph `G = (V, E)` and a nonnegative integer `K`.
QUESTION: is there a set `V' ⊆ V` with `|V'| ≤ K` such that `G - V'` is a forest, that is,
`V'` meets every cycle of `G`?

The instance, its well-formedness and the question are those of the undirected
`WantedExt.Complexity.NPComplete.FeedbackVertexSetWanted` (a simple graph on `Fin n` given by an
edge list, and the bound `K`; the question asks for at most `K` vertices whose removal leaves an
acyclic induced subgraph). The restriction adds that the graph is bipartite, as Mathlib's
`SimpleGraph.IsBipartite` (`Colorable 2`). Brandstädt, Brito, Klein, Nogueira and Protti (2013)
prove that a minimum cycle transversal (feedback vertex set) is NP-hard to find even for
bipartite graphs of maximum degree four.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **FEEDBACK VERTEX SET on bipartite graphs is NP-complete.** Source: Garey and Johnson
(1979), [GT7]; Brandstädt, Brito, Klein, Nogueira and Protti (2013). -/
public theorem_wanted feedbackVertexSetBipartite_npComplete :
    feedbackVertexSetBipartiteDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L feedbackVertexSetBipartiteDec

end MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetBipartite
