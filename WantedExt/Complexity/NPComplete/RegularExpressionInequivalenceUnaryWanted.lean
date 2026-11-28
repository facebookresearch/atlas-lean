/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# REGULAR EXPRESSION INEQUIVALENCE over a one-letter alphabet is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), p. 267, comment to problem
[AL9] REGULAR EXPRESSION INEQUIVALENCE ("or if |Σ| = 1");
L. J. Stockmeyer and A. R. Meyer, "Word problems requiring exponential time
(preliminary report)", Proceedings of the 5th Annual ACM Symposium on Theory of
Computing (1973), 1-9, doi:10.1145/800125.804029.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.RegularExpressionInequivalenceUnaryDefs

@[expose] public section

open scoped Computability

namespace MetaMathlibExt.Complexity.NPComplete.RegularExpressionInequivalenceUnary

/-!
# REGULAR EXPRESSION INEQUIVALENCE over a one-letter alphabet is NP-complete

INSTANCE: regular expressions `E₁` and `E₂` over the operators `{∪, ·, *}` and an
alphabet `Σ` with `|Σ| = 1`. QUESTION: do `E₁` and `E₂` represent different languages?

Regular expressions are those of Garey and Johnson's Section 7.4 (p. 174): `∅`, `ε`, each
letter `a ∈ Σ`, and `α + β`, `αβ`, `α*` for regular expressions `α`, `β`; these are Mathlib's
`RegularExpression`, and the language of `E` is `E.matches'`. The alphabet is `Σ = {0, ..., m - 1}`
with `m = 1`, that is `Σ = {0}`. An expression is written in postfix (reverse Polish) notation as a
list of tokens: `(0, 0)` is `∅`, `(1, 0)` is `ε`, `(2, a)` is the letter `a`, and `(3, 0)`,
`(4, 0)`, `(5, 0)` are `+`, concatenation and `*` applied to the expressions before them. A token
list that does not spell exactly one expression is malformed. Postfix spelling keeps the input
length proportional to the length of the expression; `Cslib.Language.EncodedRegex` is not used
because its node lists may share subexpressions, which can make an expression exponentially shorter
than its written form.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **REGULAR EXPRESSION INEQUIVALENCE over a one-letter alphabet is NP-complete.** Source: Garey
and Johnson (1979), [AL9] comment; Stockmeyer and Meyer (1973). -/
public theorem_wanted regularExpressionInequivalenceUnary_npComplete :
    regularExpressionInequivalenceUnaryDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L regularExpressionInequivalenceUnaryDec

end MetaMathlibExt.Complexity.NPComplete.RegularExpressionInequivalenceUnary
