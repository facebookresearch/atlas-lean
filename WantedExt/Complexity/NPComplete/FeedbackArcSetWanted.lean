/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FEEDBACK ARC SET is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), FEEDBACK ARC SET; R. M.
Karp, "Reducibility among combinatorial problems" (1972).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.FeedbackArcSetDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FeedbackArcSet

/-!
# FEEDBACK ARC SET is NP-complete

A directed graph and a bound `K`. The question is whether at most `K` arcs can be removed to
make the digraph acyclic, equivalently whether some vertex ordering has at most `K` backward
arcs.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **FEEDBACK ARC SET is NP-complete.** The decision problem FEEDBACK ARC SET belongs to NP, and
every decision problem in NP reduces to FEEDBACK ARC SET by a polynomial-time many-one
reduction.

Source: M. R. Garey and D. S. Johnson, *Computers and
Intractability* (1979), FEEDBACK ARC SET; R. M. Karp, "Reducibility among combinatorial
problems" (1972). -/
public theorem_wanted feedbackArcSet_npComplete :
    feedbackArcSetDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L feedbackArcSetDec

end MetaMathlibExt.Complexity.NPComplete.FeedbackArcSet
