/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

/-!
# The CEK machine

The CEK machine evaluates untyped lambda terms by call-by-value with an
explicit environment and continuation. Terms use de Bruijn indices. A closure
pairs the body of an abstraction with the environment in which the abstraction
was evaluated, and an environment is a list of closures, index `0` first. A
machine state either evaluates a term in an environment under a continuation
or returns a closure to a continuation. An application evaluates its function
part, then its argument, and then runs the body of the function closure in
that closure's environment extended with the argument.

`step_deterministic` shows that every state has at most one successor, and
`ret_mt_terminal` shows that returning a closure to the empty continuation is
terminal. Correctness with respect to a substitution or big-step semantics is
not formalized here.

## Source and representation

The CEK machine is due to Felleisen and Friedman [FF86]. This file is a de
Bruijn reformulation of the machine for the pure lambda calculus; the control
operators of [FF86] are not included. Its representation choices are these:
environments are lists indexed by de Bruijn indices, a closure stores the
body of an abstraction together with its environment, a state either
evaluates a term or returns a closure, and a variable whose index is outside
its environment is stuck.

## References

* [FF86] M. Felleisen and D. P. Friedman, *Control operators, the
  SECD-machine, and the λ-calculus*, 3rd Working Conference on the Formal
  Description of Programming Concepts, 1986.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.CEK

/-- Untyped lambda terms with de Bruijn indices. -/
inductive Tm : Type
  /-- The variable with de Bruijn index `n`. -/
  | var (n : Nat) : Tm
  /-- Abstraction; index `0` of the body refers to the bound variable. -/
  | lam (t : Tm) : Tm
  /-- Application of `t` to `u`. -/
  | app (t u : Tm) : Tm

/-- Closures: the body `t` of an abstraction together with the environment
`e` in which the abstraction was evaluated. Environments are lists of
closures, index `0` first. -/
inductive Clos : Type
  | clos (t : Tm) (e : List Clos) : Clos

/-- Continuations: what remains to be done with the value being computed. -/
inductive Kont : Type
  /-- Nothing remains: the value is the result. -/
  | mt : Kont
  /-- Evaluate the argument `u` in the environment `e`, then continue as
  `fn` with the value just computed. -/
  | arg (u : Tm) (e : List Clos) (k : Kont) : Kont
  /-- Apply the function closure `v` to the value just computed, then
  continue with `k`. -/
  | fn (v : Clos) (k : Kont) : Kont

/-- Machine states: evaluating a term in an environment under a
continuation, or returning a closure to a continuation. -/
inductive State : Type
  | eval (t : Tm) (e : List Clos) (k : Kont) : State
  | ret (v : Clos) (k : Kont) : State

/-- One transition of the CEK machine. -/
inductive Step : State → State → Prop
  /-- Evaluate the function part of an application first. -/
  | app {t u : Tm} {e : List Clos} {k : Kont} :
      Step (State.eval (Tm.app t u) e k) (State.eval t e (Kont.arg u e k))
  /-- An abstraction returns its closure. -/
  | lam {t : Tm} {e : List Clos} {k : Kont} :
      Step (State.eval (Tm.lam t) e k) (State.ret (Clos.clos t e) k)
  /-- A variable returns the closure at its index. A variable whose index is
  outside the environment has no transition. -/
  | var {n : Nat} {e : List Clos} {v : Clos} {k : Kont}
      (h : e[n]? = some v) :
      Step (State.eval (Tm.var n) e k) (State.ret v k)
  /-- Once the function is a value, evaluate the argument. -/
  | arg {v : Clos} {u : Tm} {e : List Clos} {k : Kont} :
      Step (State.ret v (Kont.arg u e k)) (State.eval u e (Kont.fn v k))
  /-- Once the argument is a value, run the body of the function closure in
  its environment extended with the argument. -/
  | fn {t : Tm} {e : List Clos} {v : Clos} {k : Kont} :
      Step (State.ret v (Kont.fn (Clos.clos t e) k)) (State.eval t (v :: e) k)

/-- The CEK machine is deterministic: a state has at most one successor. -/
theorem step_deterministic {s s₁ s₂ : State}
    (h₁ : Step s s₁) (h₂ : Step s s₂) : s₁ = s₂ := by
  cases h₁ <;> cases h₂ <;> simp_all

/-- Returning a closure to the empty continuation is terminal: the state has
no successor. -/
theorem ret_mt_terminal (v : Clos) (s : State)
    (h : Step (State.ret v Kont.mt) s) : False := by
  cases h

end Cslib.Languages.LambdaCalculus.CEK
