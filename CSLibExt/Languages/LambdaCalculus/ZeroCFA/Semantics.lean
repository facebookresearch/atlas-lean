/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.LambdaCalculus.ZeroCFA.Syntax
public import Mathlib.Logic.Relation

/-!
# The CEK machine for labelled λ-terms

Call-by-value evaluation of labelled λ-terms by the CEK machine of Felleisen and Friedman, in the
form of *Abstracting Abstract Machines* §2.1, Figure 1. A closure pairs a λ-abstraction with the
environment in which it was evaluated; an environment maps names to closures, newest binding
first. Continuation frames record the label of their application, which does not affect
transitions. The meaning of a program is its set of reachable machine states, so states of
non-terminating runs are included. No correspondence with substitution-based reduction is stated
here.

* `Clos`, `Env`, `Kont` and `State`: closures, environments (association lists, newest binding
  first, read by `Env.lookup`), continuations `mt`, `ar` and `fn`, and states that either
  evaluate a term (`ev`) or return a closure (`ret`).
* `Step` has five rules: `var` looks a name up, `lam` forms a closure, `app` evaluates the
  function first, `arg` then evaluates the argument, and `call` runs the body of the function
  closure in its own environment extended with the argument. The rules `var`, `app`, `arg` and
  `call` are the four rules of Figure 1. Figure 1 treats an abstraction in control position as a
  value; here the separate rule `lam` forms its closure.
* `inj P` starts the program `P` in the empty environment with the empty continuation, and
  `Reachable P s` says that the machine reaches `s` from `inj P`. `step` is the transition
  function (`step_eq_some_iff`), so examples run by computation.
* `Step.deterministic`, `not_step_ret_mt` and `not_step_var_of_lookup_none`: a state has at most
  one successor, returning a closure to the empty continuation is final, and a variable without
  a binding is stuck.
* `StateIn P s` says that every term, closure, environment and frame of `s` comes from the
  program `P`: control terms and closure bodies are subterms of `P`, every frame belongs to an
  application of `P`, and every bound name is a binder of `P`. It holds for every reachable state
  (`Reachable.stateIn`).

## References

* M. Felleisen and D. P. Friedman, *Control operators, the SECD-machine, and the λ-calculus*,
  3rd Working Conference on the Formal Description of Programming Concepts, 1986.
* D. Van Horn and M. Might, *Abstracting Abstract Machines*, ICFP 2010 (arXiv:1007.4446), §2.1
  *The CEK machine*, Figure 1.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.ZeroCFA

universe u v

/-- **Closures.** The closure `mk x body l env` pairs the abstraction `lam x body l` with the
environment `env` in which it was evaluated. An environment is a list of bindings of names to
closures, newest binding first. -/
inductive Clos (Var : Type u) (Lab : Type v) : Type (max u v) where
  /-- The abstraction `lam x body l` closed by the environment `env`. -/
  | mk (x : Var) (body : Tm Var Lab) (l : Lab) (env : List (Var × Clos Var Lab))

/-- **The abstraction of a closure.** The abstraction `lam x body l` of the closure
`mk x body l env`. -/
def Clos.term {Var : Type u} {Lab : Type v} : Clos Var Lab → Tm Var Lab
  | .mk x body l _ => .lam x body l

/-- **Environments.** A list of bindings of names to closures, newest binding first. -/
abbrev Env (Var : Type u) (Lab : Type v) : Type (max u v) :=
  List (Var × Clos Var Lab)

/-- **Looking a name up.** The closure bound to `x` by the newest binding of `x` in the
environment, or `none` when the environment does not bind `x`. It is `List.lookup x env`, the
value of the first pair in the list whose key is `x`. -/
def Env.lookup {Var : Type u} {Lab : Type v} [DecidableEq Var] :
    Env Var Lab → Var → Option (Clos Var Lab) :=
  fun env x => List.lookup x env

/-- **Continuations.** What remains to be done with the value being computed, in one of three
forms. The empty continuation `mt` means that the value is the result. The argument frame
`ar site arg env k` holds the argument `arg` of the application labelled `site`, the environment
`env` in which to evaluate it, and the continuation `k` that follows. The function frame
`fn site f k` holds the function closure `f` of the application labelled `site` and the
continuation `k` that follows. The label `site` records the application a frame belongs to; no
transition rule inspects it. -/
inductive Kont (Var : Type u) (Lab : Type v) : Type (max u v) where
  /-- Nothing remains: the value is the result. -/
  | mt
  /-- Evaluate the argument `arg` of the application labelled `site` in the environment `env`,
  then continue as `fn` with the value just computed. -/
  | ar (site : Lab) (arg : Tm Var Lab) (env : Env Var Lab) (k : Kont Var Lab)
  /-- Call the function closure `f` of the application labelled `site` on the value just
  computed, then continue with `k`. -/
  | fn (site : Lab) (f : Clos Var Lab) (k : Kont Var Lab)

/-- **Machine states.** Evaluating the term `e` in the environment `env` under the continuation
`k`, or returning the closure `v` to the continuation `k`. -/
inductive State (Var : Type u) (Lab : Type v) : Type (max u v) where
  /-- Evaluate `e` in `env`, then continue with `k`. -/
  | ev (e : Tm Var Lab) (env : Env Var Lab) (k : Kont Var Lab)
  /-- Return the closure `v` to `k`. -/
  | ret (v : Clos Var Lab) (k : Kont Var Lab)

/-- **Transitions of the CEK machine.** Call-by-value evaluation in five rules, where
`ev e env k` evaluates `e` in the environment `env` and `ret v k` returns the closure `v` to `k`:

* `var`: `ev (var x l) env k` steps to `ret c k` when `Env.lookup env x = some c`, the newest
  binding of `x` in the current environment `env`;
* `lam`: `ev (lam x body l) env k` steps to `ret (mk x body l env) k`, the closure of the
  abstraction in the current environment `env`;
* `app`: `ev (app fn arg l) env k` steps to `ev fn env (ar l arg env k)`, which evaluates the
  function `fn` in `env` and saves the argument `arg` and `env` in an argument frame;
* `arg`: `ret c (ar l arg env k)` steps to `ev arg env (fn l c k)`, which evaluates the argument
  in the environment `env` saved in the frame and saves the function closure `c` in a function
  frame;
* `call`: `ret v (fn l (mk x body l' env) k)` steps to `ev body ((x, v) :: env) k`, which runs
  the body of the function closure in the environment `env` of that closure, not the caller's,
  extended by binding its parameter `x` to the argument `v`.

A variable whose name has no binding in the current environment, and a closure returned to the
empty continuation, have no transition. -/
inductive Step {Var : Type u} {Lab : Type v} [DecidableEq Var] :
    State Var Lab → State Var Lab → Prop
  /-- A variable returns the closure bound to its name. -/
  | var {x : Var} {l : Lab} {env : Env Var Lab} {k : Kont Var Lab} {c : Clos Var Lab}
      (h : Env.lookup env x = some c) :
      Step (.ev (.var x l) env k) (.ret c k)
  /-- An abstraction returns its closure in the current environment. -/
  | lam {x : Var} {body : Tm Var Lab} {l : Lab} {env : Env Var Lab} {k : Kont Var Lab} :
      Step (.ev (.lam x body l) env k) (.ret (.mk x body l env) k)
  /-- An application evaluates its function first. -/
  | app {fn arg : Tm Var Lab} {l : Lab} {env : Env Var Lab} {k : Kont Var Lab} :
      Step (.ev (.app fn arg l) env k) (.ev fn env (.ar l arg env k))
  /-- Once the function is a closure, the argument is evaluated. -/
  | arg {c : Clos Var Lab} {l : Lab} {arg : Tm Var Lab} {env : Env Var Lab} {k : Kont Var Lab} :
      Step (.ret c (.ar l arg env k)) (.ev arg env (.fn l c k))
  /-- Once the argument is a closure `v`, the body of the function closure runs in the
  environment of that closure extended by binding its parameter to `v`. -/
  | call {v : Clos Var Lab} {l : Lab} {x : Var} {body : Tm Var Lab} {l' : Lab}
      {env : Env Var Lab} {k : Kont Var Lab} :
      Step (.ret v (.fn l (.mk x body l' env) k)) (.ev body ((x, v) :: env) k)

/-- **The initial state.** The program `P` evaluated in the empty environment with the empty
continuation. -/
def inj {Var : Type u} {Lab : Type v} (P : Tm Var Lab) : State Var Lab :=
  .ev P [] .mt

/-- **Runs of the machine.** The reflexive-transitive closure of `Step`. -/
abbrev Steps {Var : Type u} {Lab : Type v} [DecidableEq Var] :
    State Var Lab → State Var Lab → Prop :=
  Relation.ReflTransGen Step

/-- **Reachable states.** The machine reaches `s` from the initial state of the program `P`. The
meaning of `P` is the set of its reachable states. -/
def Reachable {Var : Type u} {Lab : Type v} [DecidableEq Var] (P : Tm Var Lab)
    (s : State Var Lab) : Prop :=
  Steps (inj P) s

/-- **The transition function.** The successor of a state, or `none` when the state has no
transition. -/
def step {Var : Type u} {Lab : Type v} [DecidableEq Var] :
    State Var Lab → Option (State Var Lab)
  | .ev (.var x _) env k => (Env.lookup env x).map fun c => .ret c k
  | .ev (.lam x body l) env k => some (.ret (.mk x body l env) k)
  | .ev (.app fn arg l) env k => some (.ev fn env (.ar l arg env k))
  | .ret _ .mt => none
  | .ret c (.ar l arg env k) => some (.ev arg env (.fn l c k))
  | .ret v (.fn _ (.mk x body _ env) k) => some (.ev body ((x, v) :: env) k)

/-- **The transition function computes the transitions.** `step s` is `some s'` exactly when the
machine takes `s` to `s'`. -/
theorem step_eq_some_iff {Var : Type u} {Lab : Type v} [DecidableEq Var]
    {s s' : State Var Lab} : step s = some s' ↔ Step s s' := by
  constructor
  · intro h
    rcases s with ⟨e, env, k⟩ | ⟨v, k⟩
    · rcases e with ⟨x, l⟩ | ⟨x, body, l⟩ | ⟨fn, arg, l⟩
      · simp only [step, Option.map_eq_some_iff] at h
        obtain ⟨c, hc, rfl⟩ := h
        exact .var hc
      · simp only [step, Option.some.injEq] at h
        subst h
        exact .lam
      · simp only [step, Option.some.injEq] at h
        subst h
        exact .app
    · rcases k with _ | ⟨l, arg, env, k⟩ | ⟨l, ⟨x, body, l', env⟩, k⟩
      · simp [step] at h
      · simp only [step, Option.some.injEq] at h
        subst h
        exact .arg
      · simp only [step, Option.some.injEq] at h
        subst h
        exact .call
  · intro h
    cases h with
    | var hc => simp [step, hc]
    | lam => rfl
    | app => rfl
    | arg => rfl
    | call => rfl

/-- **The machine is deterministic.** A state has at most one successor. -/
theorem Step.deterministic {Var : Type u} {Lab : Type v} [DecidableEq Var]
    {s s₁ s₂ : State Var Lab} (h₁ : Step s s₁) (h₂ : Step s s₂) : s₁ = s₂ := by
  have e₁ := step_eq_some_iff.mpr h₁
  have e₂ := step_eq_some_iff.mpr h₂
  rw [e₁] at e₂
  exact Option.some.inj e₂

/-- **Returning to the empty continuation is final.** A state that returns a closure to the empty
continuation has no successor. -/
theorem not_step_ret_mt {Var : Type u} {Lab : Type v} [DecidableEq Var] {v : Clos Var Lab}
    {s : State Var Lab} : ¬ Step (.ret v .mt) s := by
  intro h
  cases h

/-- **A variable without a binding is stuck.** If the environment `env` does not bind `x`, then
evaluating the variable `x` in `env` has no successor. -/
theorem not_step_var_of_lookup_none {Var : Type u} {Lab : Type v} [DecidableEq Var]
    {env : Env Var Lab} {x : Var} {l : Lab} {k : Kont Var Lab} {s : State Var Lab}
    (h : Env.lookup env x = none) : ¬ Step (.ev (.var x l) env k) s := by
  intro hs
  cases hs with
  | var hc => simp [h] at hc

mutual

/-- **Closures from a program.** `ClosIn P c` says that the abstraction of the closure `c` is a
subterm of `P` and that its environment comes from `P` (`EnvIn P`). -/
inductive ClosIn {Var : Type u} {Lab : Type v} (P : Tm Var Lab) : Clos Var Lab → Prop
  /-- A closure of a subterm of `P` whose environment comes from `P`. -/
  | mk {x : Var} {body : Tm Var Lab} {l : Lab} {env : Env Var Lab} :
      Tm.lam x body l ∈ P.subterms → EnvIn P env → ClosIn P (.mk x body l env)

/-- **Environments from a program.** `EnvIn P env` says that every name bound by `env` is a
binder of `P` and every closure in `env` comes from `P` (`ClosIn P`). -/
inductive EnvIn {Var : Type u} {Lab : Type v} (P : Tm Var Lab) : Env Var Lab → Prop
  /-- The empty environment. -/
  | nil : EnvIn P []
  /-- A binding of a binder of `P` to a closure from `P`, in front of an environment from `P`. -/
  | cons {y : Var} {c : Clos Var Lab} {env : Env Var Lab} :
      y ∈ P.binders → ClosIn P c → EnvIn P env → EnvIn P ((y, c) :: env)

end

/-- **Continuations from a program.** `KontIn P k` says that every frame of `k` belongs to an
application of `P`: an `ar` frame holds the argument of an application of `P` with the frame's
label and an environment from `P`, and an `fn` frame holds the label of an application of `P` and
a closure from `P`. -/
inductive KontIn {Var : Type u} {Lab : Type v} (P : Tm Var Lab) : Kont Var Lab → Prop
  /-- The empty continuation. -/
  | mt : KontIn P .mt
  /-- An argument frame of an application `app fn arg l` of `P`. -/
  | ar {l : Lab} {fn arg : Tm Var Lab} {env : Env Var Lab} {k : Kont Var Lab} :
      Tm.app fn arg l ∈ P.subterms → EnvIn P env → KontIn P k → KontIn P (.ar l arg env k)
  /-- A function frame of an application `app fn arg l` of `P`. -/
  | fn {l : Lab} {fn arg : Tm Var Lab} {c : Clos Var Lab} {k : Kont Var Lab} :
      Tm.app fn arg l ∈ P.subterms → ClosIn P c → KontIn P k → KontIn P (.fn l c k)

/-- **States from a program.** `StateIn P s` says that the state `s` comes from the program `P`,
in one of two cases. An evaluating state `ev e env k` comes from `P` when `e` is a subterm of `P`,
its environment comes from `P` (`EnvIn P env`) and its continuation comes from `P`
(`KontIn P k`). A returning state `ret v k` has no control term or environment of its own: it comes
from `P` when the returned closure comes from `P` (`ClosIn P v`) and its continuation comes from
`P` (`KontIn P k`). -/
inductive StateIn {Var : Type u} {Lab : Type v} (P : Tm Var Lab) : State Var Lab → Prop
  /-- Evaluating a subterm of `P`. -/
  | ev {e : Tm Var Lab} {env : Env Var Lab} {k : Kont Var Lab} :
      e ∈ P.subterms → EnvIn P env → KontIn P k → StateIn P (.ev e env k)
  /-- Returning a closure from `P`. -/
  | ret {v : Clos Var Lab} {k : Kont Var Lab} :
      ClosIn P v → KontIn P k → StateIn P (.ret v k)

/-- **Looking a name up in an environment from the program.** If the environment `env` comes from
the program `P` and binds `x` to the closure `c`, then `c` comes from `P`. -/
private theorem closIn_of_lookup {Var : Type u} {Lab : Type v} [DecidableEq Var]
    {P : Tm Var Lab} {env : Env Var Lab} {x : Var} {c : Clos Var Lab} (h : EnvIn P env)
    (hx : Env.lookup env x = some c) : ClosIn P c := by
  induction env with
  | nil => simp [Env.lookup] at hx
  | cons b env ih =>
    obtain ⟨y, c'⟩ := b
    cases h with
    | cons _ hc' henv =>
      simp only [Env.lookup, List.lookup_cons] at hx
      split at hx
      · cases hx
        exact hc'
      · exact ih henv hx

/-- **Abstractions of a program bind binders of the program.** If the abstraction `lam x body l`
is a subterm of the program `P`, then `x` is a binder of `P`. -/
private theorem mem_binders_of_lam_mem {Var : Type u} {Lab : Type v} {P : Tm Var Lab} {x : Var}
    {body : Tm Var Lab} {l : Lab} (h : Tm.lam x body l ∈ P.subterms) : x ∈ P.binders := by
  induction P with
  | var y l' => simp [Tm.subterms] at h
  | lam y b l' ih =>
    simp only [Tm.subterms, List.mem_cons, Tm.lam.injEq] at h
    simp only [Tm.binders, List.mem_cons]
    rcases h with ⟨rfl, -, -⟩ | h
    · exact .inl rfl
    · exact .inr (ih h)
  | app f a l' ihf iha =>
    simp only [Tm.subterms, List.mem_cons, List.mem_append, reduceCtorEq, false_or] at h
    simp only [Tm.binders, List.mem_append]
    rcases h with h | h
    · exact .inl (ihf h)
    · exact .inr (iha h)

/-- **Transitions stay in the program.** If every part of `s` comes from the program `P` and the
machine takes `s` to `s'`, then every part of `s'` comes from `P`. -/
theorem Step.stateIn {Var : Type u} {Lab : Type v} [DecidableEq Var] {P : Tm Var Lab}
    {s s' : State Var Lab} (hs : StateIn P s) (h : Step s s') : StateIn P s' := by
  cases h with
  | var hc =>
    cases hs with
    | ev _ henv hk => exact .ret (closIn_of_lookup henv hc) hk
  | lam =>
    cases hs with
    | ev he henv hk => exact .ret (.mk he henv) hk
  | app =>
    cases hs with
    | ev he henv hk =>
      exact .ev (Tm.subterms_trans he (by simp [Tm.subterms, Tm.mem_subterms_self])) henv
        (.ar he henv hk)
  | arg =>
    cases hs with
    | ret hc hk =>
      cases hk with
      | ar happ henv hk =>
        exact .ev (Tm.subterms_trans happ (by simp [Tm.subterms, Tm.mem_subterms_self])) henv
          (.fn happ hc hk)
  | call =>
    cases hs with
    | ret hv hk =>
      cases hk with
      | fn happ hf hk =>
        cases hf with
        | mk hlam henv =>
          exact .ev (Tm.subterms_trans hlam (by simp [Tm.subterms, Tm.mem_subterms_self]))
            (.cons (mem_binders_of_lam_mem hlam) hv henv) hk

/-- **Reachable states stay in the program.** Every part of every state reachable from the
program `P` comes from `P`. -/
theorem Reachable.stateIn {Var : Type u} {Lab : Type v} [DecidableEq Var] {P : Tm Var Lab}
    {s : State Var Lab} (h : Reachable P s) : StateIn P s := by
  unfold Reachable at h
  induction h with
  | refl => exact .ev (Tm.mem_subterms_self P) .nil .mt
  | tail _ hstep ih => exact hstep.stateIn ih

end Cslib.Languages.LambdaCalculus.ZeroCFA
