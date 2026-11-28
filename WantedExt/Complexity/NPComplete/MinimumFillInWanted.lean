/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM FILL-IN (CHORDAL COMPLETION) is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), MINIMUM FILL-IN; M.
Yannakakis, "Computing the minimum fill-in is NP-complete" (1981).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MinimumFillInDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumFillIn

/-!
# MINIMUM FILL-IN (CHORDAL COMPLETION) is NP-complete

An undirected graph and a bound `K`. The question is whether at most `K` edges can be added so
that the resulting graph is chordal, witnessed by a perfect elimination ordering: a vertex
ordering in which, for every vertex, its later neighbors form a clique in the augmented graph.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MINIMUM FILL-IN (CHORDAL COMPLETION) is NP-complete.** The decision problem
MINIMUM FILL-IN lies in NP, and every decision problem in NP has a polynomial-time many-one
reduction to MINIMUM FILL-IN.

Source: M. R. Garey and D. S.
Johnson, *Computers and Intractability* (1979), MINIMUM FILL-IN; M. Yannakakis, "Computing
the minimum fill-in is NP-complete" (1981). -/
public theorem_wanted minimumFillIn_npComplete :
    minimumFillInDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumFillInDec

end MetaMathlibExt.Complexity.NPComplete.MinimumFillIn
