/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TRUTH-FUNCTIONALLY COMPLETE CONNECTIVES with two expressions is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [LO10] TRUTH-FUNCTIONALLY COMPLETE
CONNECTIVES, p. 261, comment: remains NP-complete even if `|C| = 2` (reference: R. Statman
(1976), private communication).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.TruthFunctionallyCompleteConnectivesTwoExpressionsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TruthFunctionallyCompleteConnectivesTwoExpressions

open MetaMathlibExt.Complexity.NPComplete.TruthFunctionallyCompleteConnectives

/-!
# TRUTH-FUNCTIONALLY COMPLETE CONNECTIVES with two expressions is NP-complete

INSTANCE: a set `U` of variables and a collection `C` of two well-formed Boolean expressions
over `U` (the comment's restriction `|C| = 2`). QUESTION: is `C` truth-functionally complete,
i.e., is there a truth-functionally complete set of logical connectives (unary and binary
operators) `D = {θ₁, …, θₖ}` such that for each `θᵢ ∈ D` there is an expression `E ∈ C` and a
substitution `s : U → {a, b}` for which `s(E) ≡ a θᵢ b` or `s(E) ≡ θᵢ a`?

This is the restriction of `TruthFunctionallyCompleteConnectivesWanted` to collections of two
expressions: the instance, the expressions, the substitutions and the question are that
module's, and `WellFormed` adds that `C` consists of two distinct expressions: a list of two
token lists whose parsed expressions differ. Distinct token lists are not enough, because the
reader ignores the second component of operator tokens: two encodings of one expression that
differ only there (for example two spellings of NAND whose negation tokens differ) are one
expression, and such a pair is malformed.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **TRUTH-FUNCTIONALLY COMPLETE CONNECTIVES with `|C| = 2` is NP-complete:** `C` consists of
two distinct expressions. Source: Garey and Johnson (1979), [LO10], comment (Statman, 1976). -/
public theorem_wanted twoExpressions_npComplete :
    twoExpressionsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoExpressionsDec

end MetaMathlibExt.Complexity.NPComplete.TruthFunctionallyCompleteConnectivesTwoExpressions
