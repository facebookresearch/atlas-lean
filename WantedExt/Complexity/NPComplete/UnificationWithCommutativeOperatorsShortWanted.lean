/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UNIFICATION WITH COMMUTATIVE OPERATORS with short expressions is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [AN16] UNIFICATION
WITH COMMUTATIVE OPERATORS, p. 252, comment: "Remains NP-complete even if no `eᵢ` or `fᵢ`
contains more than 7 occurrences of constants and variables" (the entry credits the problem
to R. Sethi, private communication, 1977; the original was not available).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.UnificationWithCommutativeOperatorsShortDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnificationWithCommutativeOperatorsShort

open MetaMathlibExt.Complexity.NPComplete.UnificationWithCommutativeOperators

/-!
# UNIFICATION WITH COMMUTATIVE OPERATORS with short expressions is NP-complete

INSTANCE: a set `V` of variables, a set `C` of constants, and ordered pairs `(eᵢ, fᵢ)`,
`1 ≤ i ≤ n`, of expressions, where an expression is either a variable from `V`, a constant
from `C`, or `(e + f)` where `e` and `f` are expressions, and no `eᵢ` or `fᵢ` contains more
than 7 occurrences of constants and variables (the comment's restriction). QUESTION: is there
an assignment to each `v ∈ V` of a variable-free expression `I(v)` such that `I(eᵢ) ≡ I(fᵢ)`
for `1 ≤ i ≤ n`, where `e ≡ f` if and only if `e = f`, or `e = (a + b)`, `f = (c + d)` and
either `a ≡ c` and `b ≡ d`, or `a ≡ d` and `b ≡ c`?

The instance, its token encoding and the question are those of
`UnificationWithCommutativeOperatorsWanted`
(`UnificationWithCommutativeOperators.UnificationWithCommutativeOperatorsInstance`,
`UnificationWithCommutativeOperators.WellFormed` and
`UnificationWithCommutativeOperators.UnificationWithCommutativeOperatorsFeasible`). In the
prefix token list of an expression, the occurrences of variables and constants are exactly
the tokens `(0, v)` and `(1, c)` (every other token is `(2, 0)`, the operator `+`), so
`WellFormed` adds that each of the two token lists of each pair has at most 7 tokens whose
first component is not `2` (`leafCount`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **UNIFICATION WITH COMMUTATIVE OPERATORS with at most 7 occurrences of constants and
variables per expression is NP-complete.** Source: Garey and Johnson (1979), [AN16],
comment. -/
public theorem_wanted unificationWithCommutativeOperatorsShort_npComplete :
    unificationWithCommutativeOperatorsShortDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L unificationWithCommutativeOperatorsShortDec

end MetaMathlibExt.Complexity.NPComplete.UnificationWithCommutativeOperatorsShort
