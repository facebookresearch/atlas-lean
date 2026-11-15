/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.List.Basic

/-!
# CEK machine

The CEK abstract machine evaluates lambda terms with an
explicit environment and continuation. This module defines the
machine states and transitions and proves determinism and
that a returned value with empty continuation is terminal.
Substitution-semantics correctness is not included here.
-/

@[expose] public section

/-- Lambda terms, de Bruijn indices (CEK machine core of VER-29). -/
inductive Tm : Type
  | var (n : ℕ) : Tm
  | lam (t : Tm) : Tm
  | app (t u : Tm) : Tm

/-- Closures: a term with its environment. Environments are
lists of closures. -/
inductive Clos : Type
  | clos (t : Tm) (e : List Clos) : Clos

/-- Continuations. -/
inductive Kont : Type
  | mt : Kont
  | arg (u : Tm) (e : List Clos) (k : Kont) : Kont
  | fn (v : Clos) (k : Kont) : Kont

/-- Machine states: evaluating, or returning a value. -/
inductive State : Type
  | eval (t : Tm) (e : List Clos) (k : Kont) : State
  | ret (v : Clos) (k : Kont) : State

/-- CEK transition relation. -/
inductive Step : State → State → Prop
  | app {t u : Tm} {e : List Clos} {k : Kont} :
      Step (State.eval (Tm.app t u) e k) (State.eval t e (Kont.arg u e k))
  | lam {t : Tm} {e : List Clos} {k : Kont} :
      Step (State.eval (Tm.lam t) e k) (State.ret (Clos.clos t e) k)
  | var {n : ℕ} {e : List Clos} {v : Clos} {k : Kont}
      (h : e[n]? = some v) :
      Step (State.eval (Tm.var n) e k) (State.ret v k)
  | arg {v : Clos} {u : Tm} {e : List Clos} {k : Kont} :
      Step (State.ret v (Kont.arg u e k)) (State.eval u e (Kont.fn v k))
  | fn {t : Tm} {e : List Clos} {v : Clos} {k : Kont} :
      Step (State.ret v (Kont.fn (Clos.clos t e) k)) (State.eval t (v :: e) k)

/-- The CEK machine is deterministic. -/
theorem step_deterministic {s s₁ s₂ : State}
    (h₁ : Step s s₁) (h₂ : Step s s₂) : s₁ = s₂ := by
  cases h₁ <;> cases h₂ <;> simp_all

/-- A returned value with empty continuation is terminal. -/
theorem ret_mt_terminal (v : Clos) (s : State)
    (h : Step (State.ret v Kont.mt) s) : False := by
  cases h

end
