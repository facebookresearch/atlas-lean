/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# REGULAR EXPRESSION SUBSTITUTION is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [SR24] REGULAR EXPRESSION SUBSTITUTION
(attributed to A. V. Aho and J. D. Ullman [1977], private communication).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.RegularExpressionSubstitutionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RegularExpressionSubstitution

open MetaMathlibExt.Complexity.NPComplete.RegularExpressionInequivalenceBounded (parse ExprOver)

/-!
# REGULAR EXPRESSION SUBSTITUTION is NP-complete

INSTANCE: two finite alphabets `X = {x₁, x₂, ..., xₙ}` and `Y = {y₁, y₂, ..., y_m}`, a regular
expression `R` over `X ∪ Y`, regular expressions `R₁, R₂, ..., Rₙ` over `Y`, and a string
`w ∈ Y*`. QUESTION: is there a string `z` in the language determined by `R` and for each `i`,
`1 ≤ i ≤ n`, a string `wᵢ` in the language determined by `Rᵢ` such that, if each string `wᵢ` is
substituted for every occurrence of the symbol `xᵢ` in `z`, then the resulting string is
identical to `w`?

This is Garey and Johnson's [SR24] (pp. 231-232), with reference [Aho and Ullman, 1977] (a
private communication, per their bibliography), transformation from X3C; the original was not
available. Membership in NP: guess, for each `i`, either a factor of `w` as `wᵢ` or that `xᵢ`
does not occur in `z` (then any `wᵢ ∈ L(Rᵢ)` will do, and only `L(Rᵢ) ≠ ∅` needs checking);
whether some `z ∈ L(R)` then yields `w` is decidable in polynomial time with an automaton
for `R`.

Regular expressions, their postfix token lists and the parser are those of
`RegularExpressionInequivalenceBounded` (Mathlib's `RegularExpression`, with language
`E.matches'`; `ExprOver k toks E` says that `toks` spells `E` with all letters below `k`). The
symbols are natural numbers: `y_j` is `j - 1` (so `Y = {0, ..., m - 1}`) and `xᵢ` is
`m + i - 1` (so `X = {m, ..., m + n - 1}`), where `n` is the number of expressions `Rᵢ`. The
substitution maps a symbol `a ≥ m` to `w_{a - m + 1}` and keeps a symbol `a < m`. As printed by
Garey and Johnson, `R` is "a regular expression `R` over `X ∪ Y`" (not over `X` alone), so `z`
may contain symbols of `Y`, which the substitution keeps.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **REGULAR EXPRESSION SUBSTITUTION is NP-complete.** Source: Garey and Johnson (1979),
[SR24]; Aho and Ullman (1977, private communication). -/
public theorem_wanted regularExpressionSubstitution_npComplete :
    regularExpressionSubstitutionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L regularExpressionSubstitutionDec

end MetaMathlibExt.Complexity.NPComplete.RegularExpressionSubstitution
