/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTIAL FEEDBACK EDGE SET is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT9] PARTIAL
FEEDBACK EDGE SET;
M. Yannakakis, "Node- and edge-deletion NP-complete problems", Proc. 10th
Annual ACM Symposium on Theory of Computing (1978), 253-264,
doi:10.1145/800133.804355.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.PartialFeedbackEdgeSetDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartialFeedbackEdgeSet

/-!
# PARTIAL FEEDBACK EDGE SET is NP-complete

INSTANCE: a graph `G = (V, E)` and positive integers `K ≤ |E|` and `L ≤ |V|`. QUESTION: is
there a subset `E' ⊆ E` with `|E'| ≤ K` such that `E'` contains at least one edge from every
circuit of length `L` or less in `G`?

A circuit is a cycle of the graph, Mathlib's `SimpleGraph.Walk.IsCycle`, and its length is the
number of its edges (`SimpleGraph.Walk.length`). Under `WellFormed` the edge list has one entry
per edge, so its length is `|E|`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **PARTIAL FEEDBACK EDGE SET is NP-complete.** Source: Garey and Johnson (1979), [GT9];
Yannakakis (1978). -/
public theorem_wanted partialFeedbackEdgeSet_npComplete :
    partialFeedbackEdgeSetDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L partialFeedbackEdgeSetDec

end MetaMathlibExt.Complexity.NPComplete.PartialFeedbackEdgeSet
