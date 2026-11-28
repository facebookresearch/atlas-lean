/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BETWEENNESS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), BETWEENNESS; M. Opatrny,
"Total ordering problem" (1979).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.BetweennessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Betweenness

/-!
# BETWEENNESS is NP-complete

A list of triples of distinct elements. The question is whether there is a total ordering in
which the middle element of every triple lies strictly between the other two.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **BETWEENNESS is NP-complete.** The BETWEENNESS decision problem belongs to NP, and every
decision problem in NP has a polynomial-time many-one reduction to it.

Source: M. R. Garey and D. S. Johnson, *Computers and
Intractability* (1979), BETWEENNESS; M. Opatrny, "Total ordering problem" (1979). -/
public theorem_wanted betweenness_npComplete :
    betweennessDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L betweennessDec

end MetaMathlibExt.Complexity.NPComplete.Betweenness
