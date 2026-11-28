/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SATISFIABILITY OF BOOLEAN EXPRESSIONS: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [LO7] SATISFIABILITY OF BOOLEAN EXPRESSIONS,
p. 260, crediting S. A. Cook, "The complexity of theorem-proving procedures", Proceedings of the
3rd Annual ACM Symposium on Theory of Computing (1971), 151-158, doi:10.1145/800157.805047
(generic transformation).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SatisfiabilityOfBooleanExpressions

/-- A Boolean expression: a variable `uₓ`, or the binary connective with code `c` applied to two
expressions. -/
inductive BoolExpr where
  | var (x : ℕ)
  | bin (c : ℕ) (a b : BoolExpr)

/-- The binary connective with code `c`: its value at `(p, q)` is bit `2p + q` of `c`. -/
def connective (c : ℕ) (p q : Bool) : Bool :=
  c.testBit (2 * p.toNat + q.toNat)

/-- The truth value of an expression under the truth assignment `σ`. -/
def BoolExpr.eval (σ : ℕ → Bool) : BoolExpr → Bool
  | .var x => σ x
  | .bin c a b => connective c (a.eval σ) (b.eval σ)

/-- One step of the postfix reader: push a variable, or replace the top two subexpressions `a`,
`b` (in written order) by `c(a, b)`. `none` records a stack underflow or an unknown token kind. -/
def pushToken : Option (List BoolExpr) → ℕ × ℕ → Option (List BoolExpr)
  | some s, (0, x) => some (.var x :: s)
  | some (b :: a :: s), (1, c) => some (.bin c a b :: s)
  | _, _ => none

/-- The expression spelled by a postfix token list, if the list spells exactly one. -/
def parse (toks : List (ℕ × ℕ)) : Option BoolExpr :=
  match toks.foldl pushToken (some []) with
  | some [E] => some E
  | _ => none

/-- An instance: the number `n` of variables `u₀, …, u_{n-1}`, the connective codes of `B`, and
the postfix token list of `E`. -/
abbrev SatisfiabilityOfBooleanExpressionsInstance := ℕ × List ℕ × List (ℕ × ℕ)

/-- Well-formedness of an instance: every code in `B` names one of the 16 binary connectives,
the token list spells an expression, every variable token names one of `u₀, …, u_{n-1}`, and
every connective of the expression is in `B`. -/
def WellFormed (i : SatisfiabilityOfBooleanExpressionsInstance) : Prop :=
  (∀ c ∈ i.2.1, c < 16) ∧ (parse i.2.2).isSome ∧ (∀ t ∈ i.2.2, t.1 = 0 → t.2 < i.1) ∧
    ∀ t ∈ i.2.2, t.1 = 1 → t.2 ∈ i.2.1

/-- Some truth assignment satisfies the expression. Assignments are functions `ℕ → Bool`; under
`WellFormed` only their values on `0, …, n - 1` matter. -/
def SatisfiabilityOfBooleanExpressionsFeasible
    (i : SatisfiabilityOfBooleanExpressionsInstance) : Prop :=
  ∃ E, parse i.2.2 = some E ∧ ∃ σ : ℕ → Bool, E.eval σ = true

open Classical in
/-- SATISFIABILITY OF BOOLEAN EXPRESSIONS as a decision problem over bitstrings. -/
noncomputable def satisfiabilityOfBooleanExpressionsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SatisfiabilityOfBooleanExpressionsInstance) x with
  | some i => decide (WellFormed i ∧ SatisfiabilityOfBooleanExpressionsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SatisfiabilityOfBooleanExpressions
