/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INEQUIVALENCE OF SIMPLE FUNCTIONS solely in terms of `minus` is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [PO15] INEQUIVALENCE OF
SIMPLE FUNCTIONS, p. 276 (comment: the variant in which `f` and `g` are defined solely in terms
of `minus(x, y) = max {0, x - y}`, where `x, y ∈ X ∪ Z⁺`, is also NP-complete
[Constable, Hunt, and Sahni, 1974]);
R. L. Constable, H. B. Hunt III and S. Sahni, "On the computational complexity of scheme
equivalence", Report No. 74-201, Department of Computer Science, Cornell University (1974),
as cited by Garey and Johnson (the report itself was not available); journal version:
R. L. Constable, H. B. Hunt III and S. Sahni, "On the computational complexity of program
scheme equivalence", SIAM Journal on Computing 9 (1980), 396-416, doi:10.1137/0209031.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.InequivalenceOfSimpleFunctionsMinusDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.InequivalenceOfSimpleFunctionsMinus

/-!
# INEQUIVALENCE OF SIMPLE FUNCTIONS solely in terms of `minus` is NP-complete

INSTANCE: a finite set `X` of variables, and two expressions `f` and `g`, each a composition
of the function `minus(x, y) = max {0, x - y}` only, where the leaves `x, y` are variables of
`X` or positive integers (`x, y ∈ X ∪ Z⁺`).
QUESTION: is there an assignment of non-negative integer values to the variables in `X` for
which the values of `f` and `g` differ?

This is the variant of [PO15] INEQUIVALENCE OF SIMPLE FUNCTIONS
(`WantedExt.Complexity.NPComplete.InequivalenceOfSimpleFunctionsWanted`) in which the
expressions use only `minus`, with leaves in `X ∪ Z⁺`. The parent's expressions have no constant
leaves, and its collection of functions has no `minus`, so the expressions are the separate
trees `MinusExpr`, evaluated by `MinusExpr.eval`; `minus` is truncated subtraction `x - y` on
`ℕ`. The variables are `x₀, …, x_{|X|-1}`. A bare leaf is also an expression (the composition of
no functions). The instance gives each expression as its prefix (Polish) token list
`MinusExpr.tokens`, as in the parent: `(0, k)` is the variable `xₖ`, `(1, c)` is the constant
`c`, and `(2, 0)` is `minus`, followed by the tokens of its two operands in order. Every token
fixes its operator's arity, so a token list determines its tree.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **INEQUIVALENCE OF SIMPLE FUNCTIONS solely in terms of `minus` is NP-complete.** Source:
Garey and Johnson (1979), [PO15]; Constable, Hunt and Sahni (1974). -/
public theorem_wanted inequivalenceOfSimpleFunctionsMinus_npComplete :
    inequivalenceOfSimpleFunctionsMinusDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L inequivalenceOfSimpleFunctionsMinusDec

end MetaMathlibExt.Complexity.NPComplete.InequivalenceOfSimpleFunctionsMinus
