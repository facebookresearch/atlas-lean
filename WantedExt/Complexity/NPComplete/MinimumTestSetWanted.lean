/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM TEST SET is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), MINIMUM TEST COLLECTION;
A. De Bonis, L. Gargano, and U. Vaccaro, "Generalized framework for test set problems" (1997).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MinimumTestSetDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumTestSet

/-!
# MINIMUM TEST SET is NP-complete

A universe of size `n`, a list of subsets (tests), and a bound `K`. The question is whether at
most `K` tests distinguish every pair of universe elements: for distinct elements `a, b`, some
chosen test contains exactly one of them.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MINIMUM TEST SET is NP-complete.** The MINIMUM TEST SET decision problem lies in NP, and
every decision problem in NP has a polynomial-time many-one reduction to it.

Source: M. R. Garey and D. S. Johnson, *Computers and
Intractability* (1979), MINIMUM TEST COLLECTION; A. De Bonis, L. Gargano, and U. Vaccaro,
"Generalized framework for test set problems" (1997). -/
public theorem_wanted minimumTestSet_npComplete :
    minimumTestSetDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumTestSetDec

end MetaMathlibExt.Complexity.NPComplete.MinimumTestSet
