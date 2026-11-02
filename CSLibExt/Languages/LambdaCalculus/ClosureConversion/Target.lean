/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Closure conversion: target language
-/
module

public import Mathlib.Data.List.Basic

/-!
# Target language of closure conversion

A call-by-value language whose functions are closed code: `code b` is a
function of one argument whose body `b` may refer only to that argument
(variable `0`). Closures are represented explicitly as data, with pairs,
projections, `unit`, and `let`.

* `Tm.Eval ρ e v`: big-step semantics in an environment `ρ` (index `0` first).
  Applying `code b` runs `b` in the one-element environment `[arg]`, so code
  never sees the caller's environment.
* `Tm.rename`: renaming of free variables. Code bodies are closed and are not
  renamed. `Eval.rename` shows evaluation is stable under renamings that agree
  with the environments.
* `Tm.Scoped m e`: every free variable of `e` is below `m`, and every code body
  is closed (`Scoped 1`).
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.ClosureConversion.Target

/-- **Target terms of closure conversion.** The terms of the closure-conversion target language,
with variables as de Bruijn indices, are: a variable $n$ for each natural number $n$; code
$\mathsf{code}\,b$ of one parameter, whose body $b$ is evaluated with only its parameter in scope,
as variable $0$; application $f\,a$ of code to an argument; the unit term $\mathsf{unit}$ (the
empty tuple); pairs $(a, b)$; the projections $\mathsf{fst}\,e$ and $\mathsf{snd}\,e$; and
$\mathsf{let}\ e\ \mathsf{in}\ b$, which binds the value of $e$ as variable $0$ in $b$. -/
inductive Tm where
  /-- A de Bruijn variable. -/
  | var : Nat → Tm
  /-- Closed code of one parameter; the body sees only variable `0`. -/
  | code : Tm → Tm
  /-- Call code with an argument. -/
  | app : Tm → Tm → Tm
  /-- The empty tuple. -/
  | unit : Tm
  /-- Pairing. -/
  | pair : Tm → Tm → Tm
  /-- First projection. -/
  | fst : Tm → Tm
  /-- Second projection. -/
  | snd : Tm → Tm
  /-- `letIn e b` evaluates `e` and binds it as variable `0` in `b`. -/
  | letIn : Tm → Tm → Tm
  deriving DecidableEq, Repr

/-- **Target values of closure conversion.** A value of the closure-conversion target language is
code $\mathsf{code}\,b$ for a target term $b$, the unit value $\mathsf{unit}$, or a pair $(v, w)$
of values. -/
inductive Value where
  | code : Tm → Value
  | unit : Value
  | pair : Value → Value → Value
  deriving DecidableEq, Repr

namespace Tm

/-- **Big-step semantics of the closure-conversion target.** Evaluation $\rho \vdash e \Downarrow v$
of a target term $e$ to a target value $v$ in an environment $\rho$ (a list of values, where
variable $n$ refers to the entry of $\rho$ at index $n$, counting from $0$) is the least relation
closed under the following rules. A variable $n$ evaluates to the entry of $\rho$ at index $n$,
when that entry exists. Code evaluates to itself: $\rho \vdash \mathsf{code}\,b \Downarrow
\mathsf{code}\,b$. If $\rho \vdash f \Downarrow \mathsf{code}\,b$, $\rho \vdash a \Downarrow v$ and
$[v] \vdash b \Downarrow w$, then $\rho \vdash f\,a \Downarrow w$; so a code body runs in the
one-element environment $[v]$ and never sees $\rho$. The unit term evaluates to the unit value.
If $\rho \vdash a \Downarrow v$ and $\rho \vdash b \Downarrow w$, then
$\rho \vdash (a, b) \Downarrow (v, w)$. If $\rho \vdash e \Downarrow (v, w)$, then
$\rho \vdash \mathsf{fst}\,e \Downarrow v$ and $\rho \vdash \mathsf{snd}\,e \Downarrow w$. If
$\rho \vdash e \Downarrow v$ and $v :: \rho \vdash b \Downarrow w$, where $v :: \rho$ is $\rho$
with $v$ added at index $0$, then $\rho \vdash \mathsf{let}\ e\ \mathsf{in}\ b \Downarrow w$. -/
inductive Eval : List Value → Tm → Value → Prop
  | var {ρ : List Value} {n : Nat} {v : Value} (h : ρ[n]? = some v) : Eval ρ (.var n) v
  | code {ρ : List Value} {b : Tm} : Eval ρ (.code b) (.code b)
  | app {ρ : List Value} {f a b : Tm} {v w : Value}
      (hf : Eval ρ f (.code b)) (ha : Eval ρ a v) (hb : Eval [v] b w) : Eval ρ (.app f a) w
  | unit {ρ : List Value} : Eval ρ .unit .unit
  | pair {ρ : List Value} {a b : Tm} {v w : Value}
      (ha : Eval ρ a v) (hb : Eval ρ b w) : Eval ρ (.pair a b) (.pair v w)
  | fst {ρ : List Value} {e : Tm} {v w : Value}
      (h : Eval ρ e (.pair v w)) : Eval ρ (.fst e) v
  | snd {ρ : List Value} {e : Tm} {v w : Value}
      (h : Eval ρ e (.pair v w)) : Eval ρ (.snd e) w
  | letIn {ρ : List Value} {e b : Tm} {v w : Value}
      (he : Eval ρ e v) (hb : Eval (v :: ρ) b w) : Eval ρ (.letIn e b) w

/-- **Lifting a renaming under a binder, for the closure-conversion target.** The lift
$r^{\uparrow}$ of a renaming $r : \mathbb{N} \to \mathbb{N}$ of de Bruijn indices sends $0$ to $0$
and $i + 1$ to $r(i) + 1$. -/
def liftRen (r : Nat → Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => r i + 1

/-- **Renaming target terms.** For $r : \mathbb{N} \to \mathbb{N}$, the renaming $t[r]$ of a target
term $t$ replaces each variable $i$ by $r(i)$, leaves code $\mathsf{code}\,b$ unchanged (its body
$b$ is not renamed), fixes $\mathsf{unit}$, commutes with application, pairing and the two
projections, and sends $\mathsf{let}\ e\ \mathsf{in}\ b$ to
$\mathsf{let}\ e[r]\ \mathsf{in}\ b[r^{\uparrow}]$, where $r^{\uparrow}$, the lift of $r$ under
one binder, sends $0$ to $0$ and $i + 1$ to $r(i) + 1$. -/
def rename (r : Nat → Nat) : Tm → Tm
  | .var i => .var (r i)
  | .code b => .code b
  | .app f a => .app (rename r f) (rename r a)
  | .unit => .unit
  | .pair a b => .pair (rename r a) (rename r b)
  | .fst e => .fst (rename r e)
  | .snd e => .snd (rename r e)
  | .letIn e b => .letIn (rename r e) (rename (liftRen r) b)

/-- **Shifting a target term.** The shift of a target term $e$ is its renaming by the successor map
$i \mapsto i + 1$: every free variable of $e$ goes up by one, and code bodies are left unchanged. -/
def shift (e : Tm) : Tm := rename Nat.succ e

/-- **Evaluation is stable under renaming.** Let $\rho$ and $\rho'$ be environments and
$r : \mathbb{N} \to \mathbb{N}$ a renaming such that, for every index $i$ and value $w$, if $\rho$
has entry $w$ at index $i$ then $\rho'$ has entry $w$ at index $r(i)$. If a target term $e$
evaluates to $v$ in $\rho$, then the renaming of $e$ by $r$ evaluates to $v$ in $\rho'$. -/
theorem Eval.rename {ρ ρ' : List Value} {e : Tm} {v : Value} (h : Eval ρ e v)
    {r : Nat → Nat} (hr : ∀ i w, ρ[i]? = some w → ρ'[r i]? = some w) :
    Eval ρ' (e.rename r) v := by
  induction h generalizing ρ' r with
  | var h => exact .var (hr _ _ h)
  | code => exact .code
  | app _ _ hb ihf iha _ => exact .app (ihf hr) (iha hr) hb
  | unit => exact .unit
  | pair _ _ iha ihb => exact .pair (iha hr) (ihb hr)
  | fst _ ih => exact .fst (ih hr)
  | snd _ ih => exact .snd (ih hr)
  | letIn _ _ ihe ihb =>
      refine .letIn (ihe hr) (ihb ?_)
      intro i w hi
      cases i with
      | zero => exact hi
      | succ i => exact hr i w hi

/-- **Evaluation of a shifted term.** If a target term $e$ evaluates to $v$ in an environment
$\rho$, then for every value $x$ the shift of $e$ evaluates to $v$ in the environment $x :: \rho$
obtained from $\rho$ by adding $x$ at index $0$. -/
theorem Eval.shift {ρ : List Value} {e : Tm} {v : Value} (x : Value) (h : Eval ρ e v) :
    Eval (x :: ρ) e.shift v :=
  h.rename fun _ _ hi => hi

/-- **Well-scoped target terms.** For a natural number $m$, a target term $e$ is scoped in $m$
when every free variable of $e$ is less than $m$ and every code body in $e$ is closed, that is,
scoped in $1$. Inductively: a variable $i$ is scoped in $m$ when $i < m$; $\mathsf{code}\,b$ is
scoped in every $m$ when $b$ is scoped in $1$; $\mathsf{unit}$ is scoped in every $m$; an
application, a pair or a projection is scoped in $m$ when its immediate subterms are; and
$\mathsf{let}\ e\ \mathsf{in}\ b$ is scoped in $m$ when $e$ is scoped in $m$ and $b$ is scoped in
$m + 1$. -/
inductive Scoped : Nat → Tm → Prop
  | var {m i : Nat} (h : i < m) : Scoped m (.var i)
  | code {m : Nat} {b : Tm} (hb : Scoped 1 b) : Scoped m (.code b)
  | app {m : Nat} {f a : Tm} (hf : Scoped m f) (ha : Scoped m a) : Scoped m (.app f a)
  | unit {m : Nat} : Scoped m .unit
  | pair {m : Nat} {a b : Tm} (ha : Scoped m a) (hb : Scoped m b) : Scoped m (.pair a b)
  | fst {m : Nat} {e : Tm} (h : Scoped m e) : Scoped m (.fst e)
  | snd {m : Nat} {e : Tm} (h : Scoped m e) : Scoped m (.snd e)
  | letIn {m : Nat} {e b : Tm} (he : Scoped m e) (hb : Scoped (m + 1) b) :
      Scoped m (.letIn e b)

/-- **Shifting preserves scoping.** If a target term $e$ is scoped in $m$, then its shift is scoped
in $m + 1$. -/
theorem Scoped.shift {m : Nat} {e : Tm} (h : Scoped m e) : Scoped (m + 1) e.shift := by
  suffices key : ∀ {m m' : Nat} {e : Tm} {r : Nat → Nat}, Scoped m e →
      (∀ i, i < m → r i < m') → Scoped m' (e.rename r) from
    key h fun i hi => Nat.succ_lt_succ hi
  intro m m' e r h hr
  induction h generalizing m' r with
  | var hi => exact .var (hr _ hi)
  | code hb => exact .code hb
  | app _ _ ihf iha => exact .app (ihf hr) (iha hr)
  | unit => exact .unit
  | pair _ _ iha ihb => exact .pair (iha hr) (ihb hr)
  | fst _ ih => exact .fst (ih hr)
  | snd _ ih => exact .snd (ih hr)
  | letIn _ _ ihe ihb =>
      refine .letIn (ihe hr) (ihb ?_)
      intro i hi
      cases i with
      | zero => exact Nat.zero_lt_succ _
      | succ i => exact Nat.succ_lt_succ (hr i (Nat.lt_of_succ_lt_succ hi))

end Tm

end Cslib.Languages.LambdaCalculus.ClosureConversion.Target
