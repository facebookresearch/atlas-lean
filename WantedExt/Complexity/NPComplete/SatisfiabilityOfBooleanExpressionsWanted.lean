/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SATISFIABILITY OF BOOLEAN EXPRESSIONS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [LO7] SATISFIABILITY OF BOOLEAN EXPRESSIONS,
p. 260, crediting S. A. Cook, "The complexity of theorem-proving procedures", Proceedings of the
3rd Annual ACM Symposium on Theory of Computing (1971), 151-158, doi:10.1145/800157.805047
(generic transformation).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.SatisfiabilityOfBooleanExpressionsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SatisfiabilityOfBooleanExpressions

/-!
# SATISFIABILITY OF BOOLEAN EXPRESSIONS is NP-complete

INSTANCE: a variable set `U`, a subset `B` of the set of 16 possible binary Boolean connectives,
and a well-formed Boolean expression `E` over `U` and `B`.
QUESTION: is there a truth assignment for `U` that satisfies `E`?

A binary connective is a truth function `Bool → Bool → Bool`; the code `c < 16` names the
connective whose value at `(p, q)` is bit `2p + q` of `c` (`false = 0`, `true = 1`), so the codes
`0, …, 15` are exactly the 16 binary connectives (for example `8` is `∧`, `14` is `∨`, `11` is
`→`, `7` is NAND). An expression is a variable or a connective applied to two expressions.

Encoding: `U = {u₀, …, u_{n-1}}`, `B` is a list of codes, and `E` is written in postfix (reverse
Polish) notation as a list of tokens `(code, x)`: `(0, x)` is the variable `uₓ`, and `(1, c)`
applies the connective `c` to the two most recent subexpressions in their written order. `parse`
reads the tokens with a stack; a token list is an expression exactly when the stack never
underflows, every token kind is `0` or `1`, and one expression remains at the end. Every
expression has exactly one postfix spelling. The instance is decoded from a bitstring with the
repository's canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **SATISFIABILITY OF BOOLEAN EXPRESSIONS is NP-complete.** Source: Garey and Johnson (1979),
[LO7]; Cook (1971). -/
public theorem_wanted satisfiabilityOfBooleanExpressions_npComplete :
    satisfiabilityOfBooleanExpressionsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L satisfiabilityOfBooleanExpressionsDec

end MetaMathlibExt.Complexity.NPComplete.SatisfiabilityOfBooleanExpressions
