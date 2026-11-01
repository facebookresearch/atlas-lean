/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

@[expose] public section

namespace CSLibExt.Languages.MiniImp

/-!
# MiniImp syntax (Week 2 skeleton, 90-day plan #3 LOGICS)

The mini-language for the first VC target (IMP-like). Assignment,
sequencing, if, while. States are `String → Nat` functions.

Loops carry their invariant (`while b I c`): VC generation needs an
invariant annotation, and the invariant is part of the program, not
an afterthought. `BigStep` and `Hoare` read it from the statement.

This is NOT a real language (no Hack/Python/Rust), no heap yet (heap
comes via the iris-lean GenHeap interface, Weeks 3+), no Boole import
(Boole has no Lean API on CSLib main — see Day-1 verification).
-/

/-- Arithmetic expressions: literals, variables, addition. -/
inductive AExp where
  | lit : Nat → AExp
  | var : String → AExp
  | add : AExp → AExp → AExp
  deriving DecidableEq, Repr

/-- Boolean expressions: true, comparison, and, not. -/
inductive BExp where
  | tru : BExp
  | le : AExp → AExp → BExp
  | and : BExp → BExp → BExp
  | not : BExp → BExp
  deriving DecidableEq, Repr

/-- States: variable names to natural numbers. -/
abbrev State := String → Nat

/-- Statements: skip, assignment, sequencing, if, while (with
invariant `I`). -/
inductive Stmt where
  | skip : Stmt
  | assign : String → AExp → Stmt
  | seq : Stmt → Stmt → Stmt
  | if_ : BExp → Stmt → Stmt → Stmt
  | while : BExp → (State → Prop) → Stmt → Stmt

-- No `deriving DecidableEq, Repr` on `Stmt`: the `while` invariant
-- is a `Prop`, which has neither.

/-- Worked example: `x := x + 1` as a statement. -/
def incrX : Stmt := Stmt.assign "x" (AExp.add (AExp.var "x") (AExp.lit 1))

/-- The example is a single assignment, not a loop. -/
example : incrX = Stmt.assign "x" (AExp.add (AExp.var "x") (AExp.lit 1)) := rfl

end CSLibExt.Languages.MiniImp
