/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `85a3956f8d763f4003659b2ea871b54d9d9f711e`.
Original formalization by Zeina Migeed (@migeed-z); ported with permission.
-/

/-
# Syntax and evaluation for IMP expressions
-/
module

public import Mathlib.Data.Nat.Basic
public import Mathlib.Logic.Function.Basic

/-!
# IMP expressions

The state of an IMP program maps numeric variable identifiers to natural
numbers. Arithmetic and Boolean expressions are total and executable.
-/

@[expose] public section

namespace Cslib.IMP

/-- A program store maps variable identifiers to natural-number values. -/
abbrev State := Nat → Nat

/-- Arithmetic expressions. -/
inductive AExp where
  | const (value : Nat)
  | var (name : Nat)
  | add (left right : AExp)
  | sub (left right : AExp)
  | mul (left right : AExp)
  deriving DecidableEq, Repr

/-- Boolean expressions. -/
inductive BExp where
  | truth (value : Bool)
  | eq (left right : AExp)
  | le (left right : AExp)
  | not (body : BExp)
  | and (left right : BExp)
  deriving DecidableEq, Repr

/-- Commands in the deterministic while-language IMP. -/
inductive Cmd where
  | skip
  | assign (name : Nat) (value : AExp)
  | seq (first second : Cmd)
  | ite (guard : BExp) (thenBranch elseBranch : Cmd)
  | while (guard : BExp) (body : Cmd)
  deriving DecidableEq, Repr

namespace AExp

/-- Evaluate an arithmetic expression in a state. -/
def eval : AExp → State → Nat
  | .const value, _ => value
  | .var name, state => state name
  | .add left right, state => left.eval state + right.eval state
  | .sub left right, state => left.eval state - right.eval state
  | .mul left right, state => left.eval state * right.eval state

@[simp] theorem eval_const (value : Nat) (state : State) :
    (AExp.const value).eval state = value := rfl

@[simp] theorem eval_var (name : Nat) (state : State) :
    (AExp.var name).eval state = state name := rfl

@[simp] theorem eval_add (left right : AExp) (state : State) :
    (AExp.add left right).eval state = left.eval state + right.eval state := rfl

@[simp] theorem eval_sub (left right : AExp) (state : State) :
    (AExp.sub left right).eval state = left.eval state - right.eval state := rfl

@[simp] theorem eval_mul (left right : AExp) (state : State) :
    (AExp.mul left right).eval state = left.eval state * right.eval state := rfl

end AExp

namespace BExp

/-- Evaluate a Boolean expression in a state. -/
def eval : BExp → State → Bool
  | .truth value, _ => value
  | .eq left right, state => decide (left.eval state = right.eval state)
  | .le left right, state => decide (left.eval state ≤ right.eval state)
  | .not body, state => !body.eval state
  | .and left right, state => left.eval state && right.eval state

@[simp] theorem eval_truth (value : Bool) (state : State) :
    (BExp.truth value).eval state = value := rfl

@[simp] theorem eval_eq_eq_true {left right : AExp} {state : State} :
    (BExp.eq left right).eval state = true ↔ left.eval state = right.eval state := by
  simp [eval]

@[simp] theorem eval_le_eq_true {left right : AExp} {state : State} :
    (BExp.le left right).eval state = true ↔ left.eval state ≤ right.eval state := by
  simp [eval]

@[simp] theorem eval_not_eq_true {body : BExp} {state : State} :
    (BExp.not body).eval state = true ↔ body.eval state = false := by
  cases hvalue : body.eval state <;> simp [eval, hvalue]

@[simp] theorem eval_and_eq_true {left right : BExp} {state : State} :
    (BExp.and left right).eval state = true ↔
      left.eval state = true ∧ right.eval state = true := by
  simp [eval]

end BExp

end Cslib.IMP
