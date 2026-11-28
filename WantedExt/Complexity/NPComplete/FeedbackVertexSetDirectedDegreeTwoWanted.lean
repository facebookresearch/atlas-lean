/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FEEDBACK VERTEX SET (digraphs with in- and out-degree at most 2) is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT7] FEEDBACK VERTEX SET,
pp. 191-192 (comment: "Remains NP-complete for digraphs having no in- or out-degree exceeding
2, [...]", attributed to [Garey and Johnson, ——], unpublished);
T. Bai, Y. Cao and M. Xiao, "Feedback set problems on bounded-degree (planar) graphs",
arXiv:2605.11407 (2026), Corollary 3.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.FeedbackVertexSetDirectedDegreeTwoDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetDirectedDegreeTwo

/-!
# FEEDBACK VERTEX SET (digraphs with in- and out-degree at most 2) is NP-complete

INSTANCE: a directed graph `G = (V, A)` in which no vertex has in-degree or out-degree
exceeding 2, and a positive integer `K ≤ |V|`.
QUESTION: is there a subset `V' ⊆ V` with `|V'| ≤ K` such that `V'` contains at least one vertex
from every directed cycle in `G`?

The digraph has vertices `0, ..., n - 1` and is given by its arc list (`(u, v)` is the arc
`u → v`), without loops or multiple arcs; opposite arcs `u → v` and `v → u` may both be
present, and then form a directed cycle of length 2. Since no arc is repeated, the in-degree of
`v` is the number of listed arcs ending at `v` and its out-degree the number starting at `v`.
The subset `V'` is a `Finset` of vertices. Directed cycles are those of the shared MathlibExt
predicate `SimpleGraph.IsDirectedCycle` (`MathlibExt.Combinatorics.SimpleGraph.Dichromatic`):
closed directed walks `f 0 → f 1 → ⋯ → f (m + 1) = f 0` of positive length along arcs. A set of
vertices meets every closed directed walk exactly when it meets every directed cycle with
distinct vertices: such a cycle is a closed directed walk, and every closed directed walk
contains such a cycle among its vertices.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **FEEDBACK VERTEX SET is NP-complete on digraphs with in- and out-degree at most 2.**
Source: Garey and Johnson (1979), [GT7], comment; Bai, Cao and Xiao (2026), Corollary 3. -/
public theorem_wanted feedbackVertexSetDirectedDegreeTwo_npComplete :
    feedbackVertexSetDirectedDegreeTwoDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L feedbackVertexSetDirectedDegreeTwoDec

end MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetDirectedDegreeTwo
