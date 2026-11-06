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
# MiniImp syntax

States map scalar variable names to naturals. Arrays are immutable statement
parameters, not a heap. Arithmetic is total natural arithmetic, not bounded
machine arithmetic.

Loop annotations are ghost invariants used by VC generation. Neither the
big-step semantics nor the executable interpreter checks or evaluates them.

`IMPBridge.lean` embeds Atlas's canonical `Cslib.IMP` in this extension.
Canonical IMP lacks division and immutable reads, so this does not translate
the binary-search demonstration back into canonical IMP.
-/

/-- Total natural arithmetic: subtraction truncates at zero; division by zero
is zero. -/
inductive AExp where
  | lit : Nat → AExp
  | var : String → AExp
  | add : AExp → AExp → AExp
  | sub : AExp → AExp → AExp
  | mul : AExp → AExp → AExp
  | div : AExp → AExp → AExp
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
  /-- Read an immutable array. Execution requires the evaluated index to be
  in bounds. -/
  | read : String → Array Nat → AExp → Stmt
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
