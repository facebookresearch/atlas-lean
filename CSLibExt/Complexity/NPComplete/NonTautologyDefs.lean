/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NON-TAUTOLOGY: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [LO8] NON-TAUTOLOGY;
S. A. Cook, "The complexity of theorem-proving procedures", Proceedings of the
3rd Annual ACM Symposium on Theory of Computing (STOC 1971), 151-158,
doi:10.1145/800157.805047.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Logics.Propositional.Legacy.Defs
public import CSLibExt.Logics.Propositional.NaturalDeduction.Semantics

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.NonTautology

open Cslib.Logic.LegacyPL

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

end MetaMathlibExt.Complexity.NPComplete.NonTautology
