/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FEEDBACK VERTEX SET is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), FEEDBACK VERTEX SET.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.FeedbackVertexSetDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSet

/-!
# FEEDBACK VERTEX SET is NP-complete

An undirected graph and a bound `K`. The question is whether at most `K` vertices can be
removed to make the graph acyclic, stated with the canonical `SimpleGraph.IsAcyclic` predicate
on the remaining induced subgraph.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **FEEDBACK VERTEX SET is NP-complete.** The decision problem FEEDBACK VERTEX SET belongs to
NP, and every decision problem in NP reduces to FEEDBACK VERTEX SET by a polynomial-time
many-one reduction.

Source: M. R. Garey and D. S. Johnson, *Computers
and Intractability* (1979), FEEDBACK VERTEX SET. -/
public theorem_wanted feedbackVertexSet_npComplete :
    feedbackVertexSetDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L feedbackVertexSetDec

end MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSet
