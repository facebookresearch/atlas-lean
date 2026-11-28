/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NON-TAUTOLOGY is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [LO8] NON-TAUTOLOGY;
S. A. Cook, "The complexity of theorem-proving procedures", Proceedings of the
3rd Annual ACM Symposium on Theory of Computing (STOC 1971), 151-158,
doi:10.1145/800157.805047.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.NonTautologyDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.NonTautology

open Cslib.Logic.LegacyPL

/-!
# NON-TAUTOLOGY is NP-complete

INSTANCE: a Boolean expression `E` over a set `U` of variables, using the connectives `¬`
(not), `∨` (or), `∧` (and), and `→` (implies). QUESTION: is `E` not a tautology, i.e., is
there a truth assignment for `U` that makes `E` false?

The expression is a proposition of CSLib v4.35, restored as `Cslib.Logic.LegacyPL.Proposition`, over
the atoms `WithBot ℕ`: the atom `(x : ℕ)` is the variable `uₓ`, and negation is that logic's
`Proposition.neg A = A → ⊥`, where `⊥` is the atom `⊥`. Truth values are CSLibExt's
`Proposition.evalBool`, under the valuation that sends `⊥` to `false` and `uₓ` to `σ x`; with `⊥`
false, `¬A` evaluates to `!A` (`Proposition.evalBool_neg`).

Encoding: `U = {u₀, …, u_{n-1}}`, and `E` is written in postfix (reverse Polish) notation as a
list of tokens `(code, x)`: `(0, x)` is the variable `uₓ`, `(1, _)` is `¬`, and `(2, _)`,
`(3, _)`, `(4, _)` are `∧`, `∨`, `→`, applied to the two most recent subexpressions in their
written order. `parse` reads the tokens with a stack; a token list is an expression exactly when
the stack never underflows, every code is at most `4`, and one expression remains at the end.
Every expression has exactly one postfix spelling up to the ignored second component of operator
tokens. The instance is decoded from a bitstring with the repository's canonical
`MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and bitstrings decoding to malformed
instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **NON-TAUTOLOGY is NP-complete.** Source: Garey and Johnson (1979), [LO8]; Cook (1971). -/
public theorem_wanted nonTautology_npComplete :
    nonTautologyDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L nonTautologyDec

end MetaMathlibExt.Complexity.NPComplete.NonTautology
