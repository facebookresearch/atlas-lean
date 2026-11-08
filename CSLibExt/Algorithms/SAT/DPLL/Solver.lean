/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A deterministic DPLL solver
-/
module

public import CSLibExt.Logics.Propositional.CNF.Restriction

/-!
# A deterministic DPLL solver

This module implements a small executable DPLL procedure directly over the CNF
representation used by `Cslib.CookLevin`.  It uses the first unit clause when
one is present and otherwise branches on the first variable in source order.
The fuel used by `dpll` is the number of distinct variables in the input.
-/

@[expose] public section

namespace Cslib.Algorithms.SAT.DPLL

open Cslib.Logic.PL

/-- The first unit literal in source order. -/
def firstUnit : CNF → Option (Nat × Bool)
  | [] => none
  | [literal] :: _ => some literal
  | _ :: formula => firstUnit formula

/-- The first variable occurring in the formula, in source order. -/
def firstVariable : CNF → Option Nat
  | [] => none
  | [] :: formula => firstVariable formula
  | ((x, _) :: _) :: _ => some x

/-- Executable clause satisfaction. -/
def clauseSatisfied (assignment : Nat → Bool) (clause : CNFClause) : Bool :=
  clause.any fun literal => assignment literal.1 == literal.2

/-- Executable formula satisfaction. -/
def formulaSatisfied (assignment : Nat → Bool) (formula : CNF) : Bool :=
  formula.all (clauseSatisfied assignment)

@[simp]
theorem clauseSatisfied_eq_true_iff {assignment : Nat → Bool} {clause : CNFClause} :
    clauseSatisfied assignment clause = true ↔ clause.Satisfies assignment := by
  simp [clauseSatisfied, CNFClause.Satisfies, CNFLiteral.Satisfies]

@[simp]
theorem formulaSatisfied_eq_true_iff {assignment : Nat → Bool} {formula : CNF} :
    formulaSatisfied assignment formula = true ↔ formula.Satisfies assignment := by
  simp [formulaSatisfied, CNF.Satisfies]

/-- Boolean DPLL with an explicit assignment budget.

This is the proof-oriented interface: unit propagation performs one recursive
call, while a decision branches on both polarities.  It does not carry a
witness assignment, so its completeness theorem can follow the restriction
equivalence directly.
-/
def decideWithFuel : Nat → CNF → Bool
  | 0, formula => formula.isEmpty
  | fuel + 1, formula =>
      if formula.isEmpty then
        true
      else if formula.any List.isEmpty then
        false
      else
        match firstUnit formula with
        | some literal => decideWithFuel fuel (CNF.restrict literal formula)
        | none =>
            match firstVariable formula with
            | none => false
            | some x =>
                decideWithFuel fuel (CNF.restrict (x, true) formula) ||
                  decideWithFuel fuel (CNF.restrict (x, false) formula)

/-- Decide satisfiability using one assignment step per distinct input variable. -/
def dpll (formula : CNF) : Bool :=
  decideWithFuel formula.vars.card formula

end Cslib.Algorithms.SAT.DPLL
