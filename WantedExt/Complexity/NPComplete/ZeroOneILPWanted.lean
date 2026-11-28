/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 0-1 INTEGER PROGRAMMING FEASIBILITY is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), 0-1 INTEGER PROGRAMMING;
R. M. Karp, "Reducibility among combinatorial problems" (1972).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ZeroOneILPDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ZeroOneILP

/-!
# 0-1 INTEGER PROGRAMMING FEASIBILITY is NP-complete

A system of integer linear inequalities in `n` binary variables and a right-hand side. Each
coefficient and each right-hand side entry is encoded as a pair of naturals `(positive part,
negative part)` representing their difference. The question is whether some assignment in `{0,
1}^n` satisfies all inequalities.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **0-1 INTEGER PROGRAMMING FEASIBILITY is NP-complete.** The decision problem 0-1 INTEGER
PROGRAMMING FEASIBILITY belongs to NP, and every decision problem in NP has a polynomial-time
many-one reduction to it.

Source: M. R. Garey and D. S.
Johnson, *Computers and Intractability* (1979), 0-1 INTEGER PROGRAMMING; R. M. Karp,
"Reducibility among combinatorial problems" (1972). -/
public theorem_wanted zeroOneILP_npComplete :
    zeroOneILPDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L zeroOneILPDec

end MetaMathlibExt.Complexity.NPComplete.ZeroOneILP
