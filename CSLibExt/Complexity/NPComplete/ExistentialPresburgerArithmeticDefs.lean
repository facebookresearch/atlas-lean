/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EXISTENTIAL PRESBURGER ARITHMETIC: definitions

Source:
B. Scarpellini, "Complexity of subcases of Presburger arithmetic", Transactions of the American
Mathematical Society 284 (1984), 203-218, doi:10.1090/S0002-9947-1984-0742421-9 (Section 7,
Corollary 1, and Fact 1 of Section 5).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Logics.Propositional.Legacy.Defs
public import CSLibExt.Logics.Propositional.NaturalDeduction.Semantics
public import CSLibExt.Complexity.NPComplete.NonTautologyDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ExistentialPresburgerArithmetic

open Cslib.Logic.LegacyPL
open NonTautology (parse valuation)

/-- An instance: the number `k` of quantified variables, the atomic formulas as tuples
`(a, b, c, e)` standing for `a · y + b ≤ c · y + e`, and the quantifier-free part as a postfix
token list over them. -/
abbrev ExistentialPresburgerArithmeticInstance :=
  ℕ × List (List ℕ × ℕ × List ℕ × ℕ) × List (ℕ × ℕ)

/-- The truth value of the atomic formula `a · y + b ≤ c · y + e` at the values `ys` of the
variables, where `a · y` is `a₀ y₀ + ⋯ + a_{k-1} y_{k-1}`. -/
def atomValue (atom : List ℕ × ℕ × List ℕ × ℕ) (ys : List ℕ) : Bool :=
  decide ((List.zipWith (· * ·) atom.1 ys).sum + atom.2.1 ≤
    (List.zipWith (· * ·) atom.2.2.1 ys).sum + atom.2.2.2)

/-- Well-formedness of an instance: the tokens spell a quantifier-free formula, every atom
token names an atomic formula of the list, and every atomic formula has one coefficient per
variable on each side. -/
def WellFormed (i : ExistentialPresburgerArithmeticInstance) : Prop :=
  (parse i.2.2).isSome ∧ (∀ t ∈ i.2.2, t.1 = 0 → t.2 < i.2.1.length) ∧
    ∀ atom ∈ i.2.1, atom.1.length = i.1 ∧ atom.2.2.1.length = i.1

/-- The existential formula is true in `ℕ`: some values `y₀, ..., y_{k-1}` make the
quantifier-free part true when each atomic formula takes its truth value at them. -/
def ExistentialPresburgerArithmeticFeasible (i : ExistentialPresburgerArithmeticInstance) :
    Prop :=
  ∃ E, parse i.2.2 = some E ∧ ∃ ys : List ℕ, ys.length = i.1 ∧
    E.evalBool (valuation fun x => atomValue (i.2.1.getD x ([], 0, [], 0)) ys) = true

open Classical in
/-- EXISTENTIAL PRESBURGER ARITHMETIC as a decision problem over bitstrings. -/
noncomputable def existentialPresburgerArithmeticDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ExistentialPresburgerArithmeticInstance) x with
  | some i => decide (WellFormed i ∧ ExistentialPresburgerArithmeticFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ExistentialPresburgerArithmetic
