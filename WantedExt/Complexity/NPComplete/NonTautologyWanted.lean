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
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Cslib.Logics.Propositional.Defs
public import CSLibExt.Logics.Propositional.NaturalDeduction.Semantics

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.NonTautology

open Cslib.Logic.PL

/-!
# NON-TAUTOLOGY is NP-complete

INSTANCE: a Boolean expression `E` over a set `U` of variables, using the connectives `¬`
(not), `∨` (or), `∧` (and), and `→` (implies). QUESTION: is `E` not a tautology, i.e., is
there a truth assignment for `U` that makes `E` false?

The expression is CSLib's `Cslib.Logic.PL.Proposition` over the atoms `WithBot ℕ`: the atom
`(x : ℕ)` is the variable `uₓ`, and negation is CSLib's `Proposition.neg A = A → ⊥`, where `⊥`
is the atom `⊥`. Truth values are CSLibExt's `Proposition.evalBool`, under the valuation that
sends `⊥` to `false` and `uₓ` to `σ x`; with `⊥` false, `¬A` evaluates to `!A`
(`Proposition.evalBool_neg`).

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

/-- An instance: the number `n` of variables `u₀, …, u_{n-1}`, and the postfix token list of
the expression. -/
abbrev NonTautologyInstance := ℕ × List (ℕ × ℕ)

/-- One step of the postfix reader: push a variable, or replace the top one or two
subexpressions by their negation, conjunction, disjunction, or implication. `none` records a
stack underflow or an unknown token code. -/
def pushToken :
    Option (List (Proposition (WithBot ℕ))) → ℕ × ℕ → Option (List (Proposition (WithBot ℕ)))
  | some s, (0, x) => some (Proposition.atom (x : WithBot ℕ) :: s)
  | some (a :: s), (1, _) => some (Proposition.neg a :: s)
  | some (b :: a :: s), (2, _) => some (Proposition.and a b :: s)
  | some (b :: a :: s), (3, _) => some (Proposition.or a b :: s)
  | some (b :: a :: s), (4, _) => some (Proposition.imp a b :: s)
  | _, _ => none

/-- The expression spelled by a postfix token list, if the list spells exactly one. -/
def parse (toks : List (ℕ × ℕ)) : Option (Proposition (WithBot ℕ)) :=
  match toks.foldl pushToken (some []) with
  | some [A] => some A
  | _ => none

/-- The valuation of the atoms for a truth assignment `σ`: `⊥` is false and `uₓ` is `σ x`. -/
def valuation (σ : ℕ → Bool) : WithBot ℕ → Bool :=
  WithBot.recBotCoe false σ

/-- Well-formedness of an instance: the token list spells an expression, and every variable
token names one of `u₀, …, u_{n-1}`. -/
def WellFormed (i : NonTautologyInstance) : Prop :=
  (parse i.2).isSome ∧ ∀ t ∈ i.2, t.1 = 0 → t.2 < i.1

/-- Some truth assignment makes the expression false. Assignments are functions `ℕ → Bool`;
under `WellFormed` only their values on `0, …, n - 1` matter. -/
def NonTautologyFeasible (i : NonTautologyInstance) : Prop :=
  ∃ E, parse i.2 = some E ∧ ∃ σ : ℕ → Bool, E.evalBool (valuation σ) = false

open Classical in
/-- NON-TAUTOLOGY as a decision problem over bitstrings. -/
noncomputable def nonTautologyDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := NonTautologyInstance) x with
  | some i => decide (WellFormed i ∧ NonTautologyFeasible i)
  | none => false

/-- **NON-TAUTOLOGY is NP-complete.** Source: Garey and Johnson (1979), [LO8]; Cook (1971). -/
public theorem_wanted nonTautology_npComplete :
    nonTautologyDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L nonTautologyDec

end MetaMathlibExt.Complexity.NPComplete.NonTautology
