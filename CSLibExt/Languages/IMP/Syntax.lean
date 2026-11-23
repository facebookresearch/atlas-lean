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

/-- **IMP program states.** A state of an IMP program is a function
$\sigma : \mathbb{N} \to \mathbb{N}$ assigning a natural-number value $\sigma(i)$ to each variable,
where variables are identified by natural numbers $i$. -/
abbrev State := Nat → Nat

/-- **Arithmetic expressions of IMP.** The arithmetic expressions of IMP are built inductively
from the constants $n$, one for each natural number $n$, and the variables $x_i$, one for each
natural number $i$: if $a_1$ and $a_2$ are arithmetic expressions, then so are $a_1 + a_2$,
$a_1 - a_2$ and $a_1 \cdot a_2$. -/
inductive AExp where
  | const (value : Nat)
  | var (name : Nat)
  | add (left right : AExp)
  | sub (left right : AExp)
  | mul (left right : AExp)
  deriving DecidableEq, Repr

/-- **Boolean expressions of IMP.** The Boolean expressions of IMP are built inductively from the
constants true and false and the comparisons $a_1 = a_2$ and $a_1 \le a_2$ of arithmetic
expressions $a_1, a_2$: if $b$, $b_1$ and $b_2$ are Boolean expressions, then so are the negation
$\neg b$ and the conjunction $b_1 \wedge b_2$. -/
inductive BExp where
  | truth (value : Bool)
  | eq (left right : AExp)
  | le (left right : AExp)
  | not (body : BExp)
  | and (left right : BExp)
  deriving DecidableEq, Repr

/-- **Commands of IMP.** The commands of the while-language IMP are built inductively from skip
and the assignments $x_i := a$ of an arithmetic expression $a$ to the variable $x_i$ with index
$i \in \mathbb{N}$: if $c$, $c_1$ and $c_2$ are commands and $b$ is a Boolean expression, then so
are the sequential composition $c_1 ; c_2$, the conditional if $b$ then $c_1$ else $c_2$, and the
loop while $b$ do $c$. -/
inductive Cmd where
  | skip
  | assign (name : Nat) (value : AExp)
  | seq (first second : Cmd)
  | ite (guard : BExp) (thenBranch elseBranch : Cmd)
  | while (guard : BExp) (body : Cmd)
  deriving DecidableEq, Repr

namespace AExp

/-- **Evaluation of IMP arithmetic expressions.** The value of an arithmetic expression in a state
$\sigma : \mathbb{N} \to \mathbb{N}$ is the natural number defined by recursion on the expression:
a constant $n$ has value $n$, the variable $x_i$ with index $i$ has value $\sigma(i)$, and for
arithmetic expressions $a_1$ and $a_2$, the expressions $a_1 + a_2$, $a_1 - a_2$ and
$a_1 \cdot a_2$ have as value the sum, the truncated difference and the product of the values of
$a_1$ and $a_2$. The truncated difference of natural numbers $m$ and $n$ is $\max(m - n, 0)$. -/
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

/-- **Evaluation of IMP Boolean expressions.** The truth value of a Boolean expression in a
state $\sigma : \mathbb{N} \to \mathbb{N}$ is defined by recursion on the expression: the
constants true and false have values true and false; for arithmetic expressions $a_1$ and $a_2$,
the comparison $a_1 = a_2$ is true exactly when the values of $a_1$ and $a_2$ in $\sigma$ are
equal, and $a_1 \le a_2$ is true exactly when the value of $a_1$ is at most the value of $a_2$;
for Boolean expressions $b$, $b_1$ and $b_2$, the negation $\neg b$ is true exactly when $b$ is
false, and the conjunction $b_1 \wedge b_2$ is true exactly when both $b_1$ and $b_2$ are true. -/
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
