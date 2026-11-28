/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# LTL(F) SATISFIABILITY: definitions

Source:
A. P. Sistla and E. M. Clarke, "The complexity of propositional linear temporal logics",
Journal of the ACM 32 (1985), 733-749, doi:10.1145/3828.3837, Theorem 3.5 (ii).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Logics.LTL.OmegaWord

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.LTLEventuallySatisfiability

open Cslib.LTL

/-- An instance: the formula as a postfix token list. -/
abbrev LTLEventuallySatisfiabilityInstance := List ℕ

/-- Read a postfix token list onto a stack of formulas: `0` pops `g` and `f` and pushes
`f ∧ g`, `1` pops `f` and pushes `¬f`, `2` pops `f` and pushes `F f`, and `k + 3` pushes the
atomic proposition `Pₖ`. The result is the single formula left on the stack, or `none` when a
token lacks its operands or more than one formula is left. -/
def parse : List ℕ → List (Formula ℕ) → Option (Formula ℕ)
  | [], [f] => some f
  | [], _ => none
  | 0 :: rest, g :: f :: stack => parse rest (Formula.and f g :: stack)
  | 1 :: rest, f :: stack => parse rest (Formula.not f :: stack)
  | 2 :: rest, f :: stack => parse rest (Formula.eventually f :: stack)
  | (k + 3) :: rest, stack => parse rest (Formula.atom k :: stack)
  | _ :: _, _ => none

/-- Well-formedness of an instance: the tokens form an `L(F)` formula. -/
def WellFormed (i : LTLEventuallySatisfiabilityInstance) : Prop :=
  (parse i []).isSome

/-- The formula holds at the first state of some ω-sequence of label sets. -/
def LTLEventuallySatisfiabilityFeasible (i : LTLEventuallySatisfiabilityInstance) : Prop :=
  ∃ f, parse i [] = some f ∧
    ∃ w : Cslib.ωSequence (Set ℕ), Word.Satisfies (fun s a => a ∈ s) w f

open Classical in
/-- LTL(F) SATISFIABILITY as a decision problem over bitstrings. -/
noncomputable def ltlEventuallySatisfiabilityDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := LTLEventuallySatisfiabilityInstance) x with
  | some i => decide (WellFormed i ∧ LTLEventuallySatisfiabilityFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.LTLEventuallySatisfiability
