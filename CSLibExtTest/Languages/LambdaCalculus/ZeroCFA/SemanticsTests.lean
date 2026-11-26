/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.LambdaCalculus.ZeroCFA.Semantics

@[expose] public section

/-!
# Client tests for labelled λ-terms and their CEK machine

The higher-order example of *Static Program Analysis* §9.1 runs to a closure that has the
abstraction the analysis predicts for the whole program, `λt.λe.e`, and at the call `s z` the
name `s` is bound to a closure that has the abstraction the analysis predicts for `s`,
`λn.λt.λe.e`. The analysis predicts abstractions, not the environments that closures capture.
The term `Ω` runs forever around a cycle of five
transitions. The negative controls check that an unbound variable is stuck, that closures use the
environment of their definition (static scoping), that the newest binding of a name wins, and
that the program conditions reject a repeated label and a repeated binder. Erasure, the
containment of states in their program, and the type of every public declaration are pinned.
-/

namespace Cslib.Languages.LambdaCalculus.ZeroCFA.SemanticsTests

open Cslib.Languages.LambdaCalculus.ZeroCFA

universe u v

/-! ### Signatures -/

example {Var : Type u} {Lab : Type v} (e : Tm Var Lab) : e ∈ e.subterms :=
  Tm.mem_subterms_self e

example {Var : Type u} {Lab : Type v} {e s t : Tm Var Lab} (hs : s ∈ e.subterms)
    (ht : t ∈ s.subterms) : t ∈ e.subterms :=
  Tm.subterms_trans hs ht

example {Var : Type u} {Lab : Type v} {e s t : Tm Var Lab} (he : e.WellLabelled)
    (hs : s ∈ e.subterms) (ht : t ∈ e.subterms) (hl : s.label = t.label) : s = t :=
  he.label_inj hs ht hl

example {Var : Type u} {Lab : Type v} (e : Tm Var Lab) : e.labels = e.subterms.map Tm.label :=
  rfl

example {Var : Type u} {Lab : Type v} (e : Tm Var Lab) : e.WellLabelled ↔ e.labels.Nodup :=
  Iff.rfl

example {Var : Type u} {Lab : Type v} (e : Tm Var Lab) : e.UniqueBinders ↔ e.binders.Nodup :=
  Iff.rfl

example {Var : Type u} {Lab : Type v} [DecidableEq Var] (e : Tm Var Lab) : e.Closed ↔ e.fv = ∅ :=
  Iff.rfl

example {Var : Type u} {Lab : Type v} [DecidableEq Var] (e : Tm Var Lab) :
    e.erase = Cslib.LambdaCalculus.Named.Untyped.LocallyNamelessBridge.toLocallyNameless e.forget :=
  rfl

example {Var : Type u} {Lab : Type v} [DecidableEq Var] (e : Tm Var Lab) : e.erase.LC :=
  e.erase_lc

example {Var : Type u} {Lab : Type v} [DecidableEq Var] (e : Tm Var Lab) :
    e.erase.fv = e.fv :=
  e.fv_erase

example {Var : Type u} {Lab : Type v} (x : Var) (body : Tm Var Lab) (l : Lab)
    (env : Env Var Lab) : (Clos.mk x body l env).term = .lam x body l :=
  rfl

example {Var : Type u} {Lab : Type v} [DecidableEq Var] (env : Env Var Lab) (x : Var) :
    Env.lookup env x = List.lookup x env :=
  rfl

example {Var : Type u} {Lab : Type v} [DecidableEq Var] (y x : Var) (c : Clos Var Lab)
    (env : Env Var Lab) :
    Env.lookup ((y, c) :: env) x = if x = y then some c else Env.lookup env x := by
  show List.lookup x ((y, c) :: env) = if x = y then some c else List.lookup x env
  rw [List.lookup_cons]
  by_cases h : x = y
  · subst h
    simp
  · rw [beq_eq_false_iff_ne.mpr h]
    simp [h]

example {Var : Type u} {Lab : Type v} (P : Tm Var Lab) : inj P = .ev P [] .mt :=
  rfl

example {Var : Type u} {Lab : Type v} [DecidableEq Var] (P : Tm Var Lab) (s : State Var Lab) :
    Reachable P s ↔ Relation.ReflTransGen Step (inj P) s :=
  Iff.rfl

example {Var : Type u} {Lab : Type v} [DecidableEq Var] {s s' : State Var Lab} :
    step s = some s' ↔ Step s s' :=
  step_eq_some_iff

example {Var : Type u} {Lab : Type v} [DecidableEq Var] {s s₁ s₂ : State Var Lab}
    (h₁ : Step s s₁) (h₂ : Step s s₂) : s₁ = s₂ :=
  h₁.deterministic h₂

example {Var : Type u} {Lab : Type v} [DecidableEq Var] (c : Clos Var Lab) (s : State Var Lab) :
    ¬ Step (.ret c .mt) s :=
  not_step_ret_mt

example {Var : Type u} {Lab : Type v} [DecidableEq Var] {env : Env Var Lab} {x : Var} {l : Lab}
    {k : Kont Var Lab} {s : State Var Lab} (h : Env.lookup env x = none) :
    ¬ Step (.ev (.var x l) env k) s :=
  not_step_var_of_lookup_none h

example {Var : Type u} {Lab : Type v} [DecidableEq Var] {P : Tm Var Lab} {s s' : State Var Lab}
    (hs : StateIn P s) (h : Step s s') : StateIn P s' :=
  h.stateIn hs

example {Var : Type u} {Lab : Type v} [DecidableEq Var] {P : Tm Var Lab} {s : State Var Lab}
    (h : Reachable P s) : StateIn P s :=
  h.stateIn

/-! ### The examples -/

/-- Names used by the examples. -/
inductive V where
  | s | z | n | t | e | r | p | x | y | f | u | v | w | o
  deriving DecidableEq

/-- `run n s` takes `n` transitions from `s`, or is `none` when the machine stops earlier. -/
def run {Var : Type u} {Lab : Type v} [DecidableEq Var] :
    ℕ → State Var Lab → Option (State Var Lab)
  | 0, s => some s
  | n + 1, s => (step s).bind (run n)

/-- Proves `Relation.ReflTransGen Step s s'` for concrete states by following the machine one
rule at a time. -/
macro "cek_steps" : tactic => `(tactic| repeat (first
  | exact Relation.ReflTransGen.refl
  | refine Relation.ReflTransGen.head (Step.var (by rfl)) ?_
  | refine Relation.ReflTransGen.head Step.lam ?_
  | refine Relation.ReflTransGen.head Step.app ?_
  | refine Relation.ReflTransGen.head Step.arg ?_
  | refine Relation.ReflTransGen.head Step.call ?_))

/-- `λs.λz.s z`, with labels `3` to `7`. -/
def lamS : Tm V ℕ := .lam .s (.lam .z (.app (.var .s 6) (.var .z 7) 5) 4) 3

/-- `λn.λt.λe.e`, with labels `8` to `11`. -/
def lamN : Tm V ℕ := .lam .n (.lam .t (.lam .e (.var .e 11) 10) 9) 8

/-- `λr.λp.r`, with labels `12` to `14`. -/
def lamR : Tm V ℕ := .lam .r (.lam .p (.var .r 14) 13) 12

/-- The program `(λs.λz.s z) (λn.λt.λe.e) (λr.λp.r)` of *Static Program Analysis* §9.1, with
seven abstractions, three applications and four variables, labelled `1` to `14` in preorder. -/
def spa : Tm V ℕ := .app (.app lamS lamN 2) lamR 1

/-- The closure of `λn.λt.λe.e` in the empty environment. -/
def closN : Clos V ℕ := .mk .n (.lam .t (.lam .e (.var .e 11) 10) 9) 8 []

/-- The closure of `λr.λp.r` in the empty environment. -/
def closR : Clos V ℕ := .mk .r (.lam .p (.var .r 14) 13) 12 []

/-- The final state of the example: the closure of `λt.λe.e` with `n` bound to `closR`, returned
to the empty continuation. -/
def spaResult : State V ℕ := .ret (.mk .t (.lam .e (.var .e 11) 10) 9 [(.n, closR)]) .mt

/-! ### T1: the higher-order example runs -/

/-- After 16 transitions the machine returns the closure of `λt.λe.e`. -/
example : run 16 (inj spa) = some spaResult := rfl

/-- The final state has no successor, so the run stops there. -/
example : step spaResult = none := rfl

/-- The function is evaluated before the argument: after two transitions the machine evaluates
`λs.λz.s z` under the argument frames of both applications. -/
example : run 2 (inj spa) = some (.ev lamS [] (.ar 2 lamN [] (.ar 1 lamR [] .mt))) := rfl

/-- The final state is reachable, by an explicit chain of transitions. -/
example : Reachable spa spaResult := by
  unfold Reachable inj
  cek_steps

/-- The returned closure has the abstraction the analysis predicts for the whole program, the
label-`9` abstraction `λt.λe.e`; the analysis does not predict the environment it captures. -/
example : (Clos.mk V.t (.lam .e (.var .e 11) 10) 9 [(.n, closR)]).term =
    .lam .t (.lam .e (.var .e 11) 10) 9 :=
  rfl

/-! ### T2: the call site `s z` -/

/-- The state that evaluates `s z`, with `z` bound to `closR` and `s` bound to `closN`, is
reachable. -/
example : Reachable spa (.ev (.app (.var .s 6) (.var .z 7) 5) [(.z, closR), (.s, closN)] .mt) := by
  unfold Reachable inj
  cek_steps

/-- There `s` is bound to a closure that has the abstraction the analysis predicts for `s`,
`λn.λt.λe.e`. -/
example : Env.lookup [(V.z, closR), (V.s, closN)] V.s = some closN ∧ closN.term = lamN :=
  ⟨rfl, rfl⟩

/-! ### T3: divergence -/

/-- `Ω = (λx.x x) (λy.y y)`, labelled `1` to `9` in preorder. -/
def omegaProg : Tm V ℕ :=
  .app (.lam .x (.app (.var .x 4) (.var .x 5) 3) 2) (.lam .y (.app (.var .y 8) (.var .y 9) 7) 6) 1

/-- The closure of `λy.y y` in the empty environment. -/
def closY : Clos V ℕ := .mk .y (.app (.var .y 8) (.var .y 9) 7) 6 []

/-- Evaluating `y y` with `y` bound to `closY`. -/
def loopState : State V ℕ := .ev (.app (.var .y 8) (.var .y 9) 7) [(.y, closY)] .mt

/-- The run of `Ω` reaches `loopState` after 10 transitions and again after 15. -/
example : run 10 (inj omegaProg) = some loopState ∧ run 15 (inj omegaProg) = some loopState :=
  ⟨rfl, rfl⟩

/-- `loopState` is reachable from `Ω`. -/
example : Reachable omegaProg loopState := by
  unfold Reachable inj
  cek_steps

/-- `loopState` returns to itself after a nonempty run, so the run of `Ω` never stops. -/
example : Relation.TransGen Step loopState loopState := by
  unfold loopState
  exact Relation.TransGen.head' Step.app (by cek_steps)

/-! ### T4: determinism and final states -/

/-- The initial state of the example has exactly one successor. -/
example (s' : State V ℕ) (h : Step (inj spa) s') :
    s' = .ev (.app lamS lamN 2) [] (.ar 1 lamR [] .mt) := by
  cases h
  rfl

/-- The same instance, from `Step.deterministic`. -/
example (s' : State V ℕ) (h : Step (inj spa) s') :
    s' = .ev (.app lamS lamN 2) [] (.ar 1 lamR [] .mt) :=
  h.deterministic Step.app

/-- Returning a closure to the empty continuation has no successor. -/
example (c : Clos V ℕ) (s : State V ℕ) : ¬ Step (.ret c .mt) s := nofun

/-! ### T5: an unbound variable is stuck -/

/-- Evaluating the variable `y` in the empty environment has no successor. -/
example (s : State V ℕ) : ¬ Step (.ev (.var V.y 1) [] .mt) s := by
  intro h
  cases h with
  | var h => cases h

/-- The transition function agrees. -/
example : step (.ev (.var V.y 1) [] .mt : State V ℕ) = none := rfl

/-- The same, from `not_step_var_of_lookup_none`. -/
example (s : State V ℕ) : ¬ Step (.ev (.var V.y 1) [] .mt) s := not_step_var_of_lookup_none rfl

/-! ### T6: static scoping -/

/-- The closed term `λu.u`, labelled `15` and `16`; it plays the argument `a`. -/
def termA : Tm V ℕ := .lam .u (.var .u 16) 15

/-- The closed term `λv.v`, labelled `9` and `10`; it plays the argument `d`. -/
def termD : Tm V ℕ := .lam .v (.var .v 10) 9

/-- The closed term `λw.w`, labelled `11` and `12`; it plays the argument `e`. -/
def termE : Tm V ℕ := .lam .w (.var .w 12) 11

/-- `(λx.((λf.((λx.f d) e)) (λy.x))) a`, labelled `1` to `16` in preorder. Its binders are not
unique: `x` is bound twice. -/
def scoping : Tm V ℕ :=
  .app (.lam .x (.app (.lam .f (.app (.lam .x (.app (.var .f 8) termD 7) 6) termE 5) 4)
    (.lam .y (.var .x 14) 13) 3) 2) termA 1

/-- The program returns the closure of `a`: the body `x` of `λy.x` is evaluated in the
environment of that abstraction, where `x` is bound to `a`. Under dynamic scoping it would
return the closure of `e`, the newer binding of `x` in the calling environment. -/
example : run 21 (inj scoping) = some (.ret (.mk .u (.var .u 16) 15 []) .mt) := rfl

/-- The final state is reachable. -/
example : Reachable scoping (.ret (.mk .u (.var .u 16) 15 []) .mt) := by
  unfold Reachable inj
  cek_steps

/-- The closures of `a` and of `e` have different abstractions. -/
example : termA ≠ termE := by decide

/-! ### T7: the newest binding wins -/

/-- The closed term `λo.o`, labelled `8` and `9`; it plays the argument `b`. -/
def termB : Tm V ℕ := .lam .o (.var .o 9) 8

/-- `(λx.λx.x) a b`, labelled `1` to `9` in preorder, with `a = λu.u`. -/
def shadowing : Tm V ℕ :=
  .app (.app (.lam .x (.lam .x (.var .x 5) 4) 3) (.lam .u (.var .u 7) 6) 2) termB 1

/-- The program returns the closure of `b`: the inner binding of `x` is the newest. -/
example : run 11 (inj shadowing) = some (.ret (.mk .o (.var .o 9) 8 []) .mt) := rfl

/-- The final state is reachable. -/
example : Reachable shadowing (.ret (.mk .o (.var .o 9) 8 []) .mt) := by
  unfold Reachable inj
  cek_steps

/-! ### T8: program conditions -/

/-- The example is well labelled. -/
example : spa.WellLabelled := by
  unfold Tm.WellLabelled
  decide

/-- The example has unique binders. -/
example : spa.UniqueBinders := by
  unfold Tm.UniqueBinders
  decide

/-- The example is closed. -/
example : spa.Closed := by
  unfold Tm.Closed
  decide

/-- A term with the label `2` on two nodes is not well labelled. -/
example : ¬ (Tm.app (.lam .x (.var .x 2) 2) (.lam .y (.var .y 3) 4) 1 : Tm V ℕ).WellLabelled := by
  unfold Tm.WellLabelled
  decide

/-- A term that binds `x` twice does not have unique binders. -/
example : ¬ shadowing.UniqueBinders := by
  unfold Tm.UniqueBinders
  decide

/-- A free variable is not closed. -/
example : ¬ (Tm.var V.x 1 : Tm V ℕ).Closed := by
  unfold Tm.Closed
  decide

/-! ### T9: erasure -/

/-- The erasure of the example: `(λ.λ.1 0) (λ.λ.λ.0) (λ.λ.1)` with de Bruijn indices. -/
example : spa.erase =
    .app (.app (.abs (.abs (.app (.bvar 1) (.bvar 0)))) (.abs (.abs (.abs (.bvar 0)))))
      (.abs (.abs (.bvar 1))) :=
  rfl

/-- The erasure of the example is locally closed, by the translation of named terms. -/
example : spa.erase.LC :=
  Cslib.LambdaCalculus.Named.Untyped.LocallyNamelessBridge.toLocallyNameless_lc spa.forget

/-- The same, from `Tm.erase_lc`. -/
example : spa.erase.LC := spa.erase_lc

/-- The example with every label raised by `100`. -/
def spaRelabelled : Tm V ℕ :=
  .app (.app (.lam .s (.lam .z (.app (.var .s 106) (.var .z 107) 105) 104) 103)
    (.lam .n (.lam .t (.lam .e (.var .e 111) 110) 109) 108) 102)
    (.lam .r (.lam .p (.var .r 114) 113) 112) 101

/-- Relabelling does not change the erasure. -/
example : spa.erase = spaRelabelled.erase := rfl

/-! ### T10: reachable states stay in the program -/

/-- The final state of the example comes from the program: the abstraction `λt.λe.e` and the
closure of `λr.λp.r` are subterms of `spa`, and `n` is one of its binders. -/
example : StateIn spa spaResult := by
  refine .ret (.mk ?_ (.cons ?_ (.mk ?_ .nil) .nil)) .mt <;> decide

/-- The state at the call site `s z` comes from the program as well. -/
example : StateIn spa (.ev (.app (.var .s 6) (.var .z 7) 5) [(.z, closR), (.s, closN)] .mt) := by
  refine .ev ?_ (.cons ?_ (.mk ?_ .nil) (.cons ?_ (.mk ?_ .nil) .nil)) .mt <;> decide

/-- The same for the final state, from `Reachable.stateIn`. -/
example : StateIn spa spaResult :=
  Reachable.stateIn (by unfold Reachable inj; cek_steps)

end Cslib.Languages.LambdaCalculus.ZeroCFA.SemanticsTests
