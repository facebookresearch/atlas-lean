/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INDEPENDENT DOMINATING SET is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), INDEPENDENT DOMINATING
SET (a small maximal independent set).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.IndependentDominatingSetDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IndependentDominatingSet

/-!
# INDEPENDENT DOMINATING SET is NP-complete

An undirected graph and a bound `K`. The question is whether some set of at most `K` vertices
is both independent (no edge inside the set) and dominating.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **INDEPENDENT DOMINATING SET is NP-complete.** The decision problem INDEPENDENT DOMINATING
SET belongs to NP, and every decision problem in NP has a polynomial-time many-one reduction to
it.

Source: M. R. Garey and D. S. Johnson,
*Computers and Intractability* (1979), INDEPENDENT DOMINATING SET (a small maximal
independent set). -/
public theorem_wanted independentDominatingSet_npComplete :
    independentDominatingSetDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L independentDominatingSetDec

end MetaMathlibExt.Complexity.NPComplete.IndependentDominatingSet
