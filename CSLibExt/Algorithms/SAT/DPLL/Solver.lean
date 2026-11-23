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

/-- **First unit literal.** For a CNF formula $\varphi$, read as a list of clauses, this returns
the literal $\ell$ of the first clause of $\varphi$ that consists of the single literal $\ell$,
and returns nothing when no clause of $\varphi$ has exactly one literal. -/
def firstUnit : CNF → Option (Nat × Bool)
  | [] => none
  | [literal] :: _ => some literal
  | _ :: formula => firstUnit formula

/-- **First variable of a CNF formula.** For a CNF formula $\varphi$, read as a list of clauses,
this returns the variable of the first literal of the first nonempty clause of $\varphi$, that
is, the first variable occurring in $\varphi$ in source order, and returns nothing when every
clause of $\varphi$ is empty (in particular when $\varphi$ has no clauses). -/
def firstVariable : CNF → Option Nat
  | [] => none
  | [] :: formula => firstVariable formula
  | ((x, _) :: _) :: _ => some x

/-- **Boolean clause satisfaction check.** For an assignment $v$ of Boolean values to the
variables $0, 1, 2, \ldots$ and a clause $C$, whose literals are pairs $(x, b)$ of a variable
$x$ and a polarity $b$, this Boolean is true exactly when some literal $(x, b)$ of $C$ satisfies
$v(x) = b$. -/
def clauseSatisfied (assignment : Nat → Bool) (clause : CNFClause) : Bool :=
  clause.any fun literal => assignment literal.1 == literal.2

/-- **Boolean formula satisfaction check.** For an assignment $v$ of Boolean values to the
variables $0, 1, 2, \ldots$ and a CNF formula $\varphi$, this Boolean is true exactly when every
clause of $\varphi$ passes the Boolean clause satisfaction check for $v$, that is, every clause
contains a literal $(x, b)$ with $v(x) = b$. -/
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

/-- **DPLL with a fuel budget.** Given a natural number $n$ (the fuel) and a CNF formula
$\varphi$, the procedure returns a Boolean value. Literals are pairs $(x, b)$ of a variable $x$
and a polarity $b$. With fuel $0$ the procedure returns true exactly when $\varphi$ has no
clauses. With fuel $n + 1$ it returns true if $\varphi$ has no clauses, and otherwise returns
false if some clause of $\varphi$ is empty. Otherwise, if some clause of $\varphi$ consists of
a single literal, it takes the first such literal $\ell$ in source order and returns the result
of the procedure with fuel $n$ on the restriction of $\varphi$ by $\ell$. Otherwise, if some
variable occurs in $\varphi$, it takes the first such variable $x$ in source order and returns
true exactly when the procedure with fuel $n$ returns true on the restriction of $\varphi$ by
$(x, \mathrm{true})$ or on the restriction of $\varphi$ by $(x, \mathrm{false})$; if no variable
occurs, it returns false.

The restriction of $\varphi$ by a literal $(x, b)$ deletes every clause containing $(x, b)$ and
removes every literal with variable $x$ from the remaining clauses. A decision branches on both
polarities, a unit literal gives a single recursive call, and no satisfying assignment is
returned.
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

/-- **The DPLL procedure.** On a CNF formula $\varphi$, the DPLL procedure runs DPLL with fuel
equal to the number of distinct variables occurring in $\varphi$ and returns its Boolean result. -/
def dpll (formula : CNF) : Bool :=
  decideWithFuel formula.vars.card formula

end Cslib.Algorithms.SAT.DPLL
