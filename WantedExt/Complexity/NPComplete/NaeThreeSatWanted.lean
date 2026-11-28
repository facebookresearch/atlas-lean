/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NOT-ALL-EQUAL 3-SAT is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-
Completeness* (1979), NOT-ALL-EQUAL 3-SAT; T. J. Schaefer, "The complexity of satisfiability
problems" (1978).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.NaeThreeSatDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.NaeThreeSat

/-!
# NOT-ALL-EQUAL 3-SAT is NP-complete

A 3-CNF formula: every clause has exactly three literals. The question is whether some
assignment makes every clause not-all-equal, that is, each clause has both a true and a false
literal.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **NOT-ALL-EQUAL 3-SAT is NP-complete.** The decision problem NOT-ALL-EQUAL 3-SAT over
bitstrings belongs to NP, and every decision problem in NP has a polynomial-time many-one
reduction to it.

Source: M. R. Garey and D. S. Johnson, *Computers
and Intractability: A Guide to the Theory of NP-Completeness* (1979), NOT-ALL-EQUAL 3-SAT;
T. J. Schaefer, "The complexity of satisfiability problems" (1978). -/
public theorem_wanted naeThreeSat_npComplete :
    naeThreeSatDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L naeThreeSatDec

end MetaMathlibExt.Complexity.NPComplete.NaeThreeSat
