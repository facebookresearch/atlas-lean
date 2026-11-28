/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INEQUIVALENCE OF SIMPLE FUNCTIONS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [PO15] INEQUIVALENCE OF
SIMPLE FUNCTIONS, p. 276 (reference [Tsichritzis, 1970]; transformation from INEQUIVALENCE
OF LOOP PROGRAMS WITHOUT NESTING);
D. Tsichritzis, "The equivalence problem of simple programs", Journal of the ACM 17 (1970),
729-738, doi:10.1145/321607.321621 (the simple functions are the functions of the loop
programs without nesting, `L₁`);
R. L. Constable, H. B. Hunt III and S. Sahni, "On the computational complexity of program
scheme equivalence", SIAM Journal on Computing 9 (1980), 396-416, doi:10.1137/0209031 (the
equivalence problem for `L₁` programs is NP-complete).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.InequivalenceOfSimpleFunctionsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.InequivalenceOfSimpleFunctions

/-!
# INEQUIVALENCE OF SIMPLE FUNCTIONS is NP-complete

INSTANCE: a finite set `X` of variables, and two expressions `f` and `g` over `X`, each a
composition of functions from the collection `s(x) = x + 1`, `p(x) = max {x - 1, 0}`,
`plus(x, y) = x + y`, `div(x, t) = ⌊x / t⌋`, `mod(x, t) = x - t · ⌊x / t⌋`,
`w(x, y) = if y = 0 then x else 0`, and `selectᵢⁿ(x₁, x₂, …, xₙ) = xᵢ`, where the leaves
`x, y, xᵢ` are variables of `X` and `i, n, t` are positive integers with `i ≤ n`.
QUESTION: is there an assignment of non-negative integer values to the variables in `X` for
which the values of `f` and `g` differ?

The variables are `x₀, …, x_{|X|-1}`. Expressions are the trees `SimpleExpr` (no sharing of
subexpressions), evaluated by `SimpleExpr.eval`; `p` is truncated subtraction on `ℕ`, and
`div` and `mod` are `ℕ`'s `/` and `%`. A bare variable is also an expression; this adds no
functions, since `x = select₁¹(x)`. The instance gives each expression as its prefix (Polish)
token list `SimpleExpr.tokens`: `(0, k, 0)` is the variable `xₖ`, `(1, 0, 0)` is `s`,
`(2, 0, 0)` is `p`, `(3, 0, 0)` is `plus`, `(4, t, 0)` is `div(·, t)`, `(5, t, 0)` is
`mod(·, t)`, `(6, 0, 0)` is `w`, and `(7, i, n)` is `selectᵢⁿ`, each operator followed by the
tokens of its operands in order. Every token fixes its operator's arity, so a token list
determines its tree.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **INEQUIVALENCE OF SIMPLE FUNCTIONS is NP-complete.** Source: Garey and Johnson (1979),
[PO15]; Tsichritzis (1970); Constable, Hunt and Sahni (1980). -/
public theorem_wanted inequivalenceOfSimpleFunctions_npComplete :
    inequivalenceOfSimpleFunctionsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L inequivalenceOfSimpleFunctionsDec

end MetaMathlibExt.Complexity.NPComplete.InequivalenceOfSimpleFunctions
