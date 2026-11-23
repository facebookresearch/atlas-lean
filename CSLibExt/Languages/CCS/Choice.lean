/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `290c48922e071d1e4267dd103a14e73b547adf60`.
Original formalization by Zeina Migeed (@migeed-z); ported with permission.
-/

/-
# Finite CCS choice processes
-/
module

public import CSLibExt.Foundations.Semantics.LTS.Bisimulation

/-!
# A finite fragment of CCS

This file gives a small structural operational semantics for terminated
processes, action prefix, and nondeterministic choice.  Strong bisimulation is
then used to establish the algebraic laws of choice and congruence of both
constructors.  The proofs operate on transition derivations rather than on a
syntactic normalization of processes.
-/

@[expose] public section

namespace Cslib.CCS

variable (Action : Type*)

/-- **Finite CCS processes.** For a type $A$ of actions, the finite CCS processes over $A$ are
built from the inactive process $\mathbf{0}$ by action prefix $a.P$ (an action $a \in A$
followed by a process $P$), nondeterministic choice $P + Q$, and parallel composition
$P \mid Q$. -/
inductive Process where
  | nil
  | prefix (action : Action) (continuation : Process)
  | choice (left right : Process)
  | parallel (left right : Process)
  deriving DecidableEq

namespace Process

variable {Action}

/-- **Operational semantics of finite CCS with a synchronization function.** Let $\sigma$ be a
partial function that assigns to some pairs of actions $(a, b)$ an action $\sigma(a, b)$. The
transition relation $P \xrightarrow{a} P'$ on finite CCS processes (built from prefix $a.P$,
choice $P + Q$ and parallel composition $P \mid Q$) determined by $\sigma$ is the least relation
such that $a.P \xrightarrow{a} P$; if $P \xrightarrow{a} P'$ then $P + Q \xrightarrow{a} P'$,
$Q + P \xrightarrow{a} P'$, $P \mid Q \xrightarrow{a} P' \mid Q$ and
$Q \mid P \xrightarrow{a} Q \mid P'$; and if $P \xrightarrow{a} P'$, $Q \xrightarrow{b} Q'$ and
$\sigma(a, b) = c$, then $P \mid Q \xrightarrow{c} P' \mid Q'$. -/
inductive RawStep (synchronize : Action → Action → Option Action) :
    Process Action → Action → Process Action → Prop
  | prefix (action : Action) (continuation : Process Action) :
      RawStep synchronize (.prefix action continuation) action continuation
  | choiceLeft {left right next : Process Action} {action : Action}
      (step : RawStep synchronize left action next) :
      RawStep synchronize (.choice left right) action next
  | choiceRight {left right next : Process Action} {action : Action}
      (step : RawStep synchronize right action next) :
      RawStep synchronize (.choice left right) action next
  | parallelLeft {left right next : Process Action} {action : Action}
      (step : RawStep synchronize left action next) :
      RawStep synchronize (.parallel left right) action (.parallel next right)
  | parallelRight {left right next : Process Action} {action : Action}
      (step : RawStep synchronize right action next) :
      RawStep synchronize (.parallel left right) action (.parallel left next)
  | communicate {left right left' right' : Process Action}
      {leftAction rightAction result : Action}
      (leftStep : RawStep synchronize left leftAction left')
      (rightStep : RawStep synchronize right rightAction right')
      (syncs : synchronize leftAction rightAction = some result) :
      RawStep synchronize (.parallel left right) result (.parallel left' right')

/-- **Transitions of finite CCS without communication.** The transition relation
$P \xrightarrow{a} P'$ on finite CCS processes is the operational semantics of finite CCS whose
synchronization function is undefined on every pair of actions. Thus prefix and choice move as
usual, and a parallel composition $P \mid Q$ moves only by letting one of $P$ and $Q$ move;
there are no communication steps. -/
abbrev Step : Process Action → Action → Process Action → Prop :=
  RawStep (fun _ _ => none)

/-- **Labelled transition system of finite CCS.** The labelled transition system whose states are
the finite CCS processes, whose labels are the actions, and whose transitions $P \xrightarrow{a} P'$
are those of the communication-free operational semantics of finite CCS. -/
def lts : Cslib.LTS (Process Action) Action := ⟨Step⟩

open Cslib.LTS

theorem nil_no_step {action : Action} {next : Process Action} :
    ¬Step .nil action next := by
  intro h
  cases h

theorem prefix_step_iff {head action : Action} {continuation next : Process Action} :
    Step (.prefix head continuation) action next ↔
      action = head ∧ next = continuation := by
  constructor
  · intro h
    cases h
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact .prefix _ _

theorem choice_step_iff {left right next : Process Action} {action : Action} :
    Step (.choice left right) action next ↔
      Step left action next ∨ Step right action next := by
  constructor
  · intro h
    cases h with
    | choiceLeft hstep => exact Or.inl hstep
    | choiceRight hstep => exact Or.inr hstep
  · rintro (hstep | hstep)
    · exact .choiceLeft hstep
    · exact .choiceRight hstep

/-- **Lifting relations through choice.** Given relations $R$ and $S$ on finite CCS processes,
write $P_1 + P_2$ for the nondeterministic choice of $P_1$ and $P_2$. The choice lift of $R$
and $S$ relates $P$ to $Q$ exactly when $R(P, Q)$ holds, or $S(P, Q)$ holds, or $P = P_1 + P_2$
and $Q = Q_1 + Q_2$ with $R(P_1, Q_1)$ and $S(P_2, Q_2)$. -/
inductive ChoiceLift (leftRel rightRel : Process Action → Process Action → Prop) :
    Process Action → Process Action → Prop
  | left {left₁ left₂} (relation : leftRel left₁ left₂) :
      ChoiceLift leftRel rightRel left₁ left₂
  | right {right₁ right₂} (relation : rightRel right₁ right₂) :
      ChoiceLift leftRel rightRel right₁ right₂
  | choice {left₁ left₂ right₁ right₂}
      (left : leftRel left₁ left₂) (right : rightRel right₁ right₂) :
      ChoiceLift leftRel rightRel (.choice left₁ right₁) (.choice left₂ right₂)

theorem choiceLift_isSimulation {leftRel rightRel : Process Action → Process Action → Prop}
    (hleft : (lts (Action := Action)).IsHomSimulation leftRel)
    (hright : (lts (Action := Action)).IsHomSimulation rightRel) :
    (lts (Action := Action)).IsHomSimulation (ChoiceLift leftRel rightRel) := by
  intro source target hrel action next hstep
  cases hrel with
  | left hrel =>
      obtain ⟨next', hnext', hrel'⟩ := hleft.follow hrel hstep
      exact ⟨next', hnext', .left hrel'⟩
  | right hrel =>
      obtain ⟨next', hnext', hrel'⟩ := hright.follow hrel hstep
      exact ⟨next', hnext', .right hrel'⟩
  | choice hleftRel hrightRel =>
      change Step (.choice _ _) action next at hstep
      rw [choice_step_iff] at hstep
      rcases hstep with hstep | hstep
      · obtain ⟨next', hnext', hrel'⟩ := hleft.follow hleftRel hstep
        exact ⟨next', .choiceLeft hnext', .left hrel'⟩
      · obtain ⟨next', hnext', hrel'⟩ := hright.follow hrightRel hstep
        exact ⟨next', .choiceRight hnext', .right hrel'⟩

theorem choiceLift_isBisimulation {leftRel rightRel : Process Action → Process Action → Prop}
    (hleft : (lts (Action := Action)).IsHomBisimulation leftRel)
    (hright : (lts (Action := Action)).IsHomBisimulation rightRel) :
    (lts (Action := Action)).IsHomBisimulation (ChoiceLift leftRel rightRel) := by
  intro source target hrel action
  constructor
  · intro next hstep
    cases hrel with
    | left hrel =>
      obtain ⟨next', hnext', hrel'⟩ := (hleft hrel action).1 next hstep
      exact ⟨next', hnext', .left hrel'⟩
    | right hrel =>
      obtain ⟨next', hnext', hrel'⟩ := (hright hrel action).1 next hstep
      exact ⟨next', hnext', .right hrel'⟩
    | choice hleftRel hrightRel =>
      change Step (.choice _ _) action next at hstep
      rw [choice_step_iff] at hstep
      rcases hstep with hstep | hstep
      · obtain ⟨next', hnext', hrel'⟩ := (hleft hleftRel action).1 next hstep
        exact ⟨next', .choiceLeft hnext', .left hrel'⟩
      · obtain ⟨next', hnext', hrel'⟩ := (hright hrightRel action).1 next hstep
        exact ⟨next', .choiceRight hnext', .right hrel'⟩
  · intro next hstep
    cases hrel with
    | left hrel =>
      obtain ⟨next', hnext', hrel'⟩ := (hleft hrel action).2 next hstep
      exact ⟨next', hnext', .left hrel'⟩
    | right hrel =>
      obtain ⟨next', hnext', hrel'⟩ := (hright hrel action).2 next hstep
      exact ⟨next', hnext', .right hrel'⟩
    | choice hleftRel hrightRel =>
      change Step (.choice _ _) action next at hstep
      rw [choice_step_iff] at hstep
      rcases hstep with hstep | hstep
      · obtain ⟨next', hnext', hrel'⟩ := (hleft hleftRel action).2 next hstep
        exact ⟨next', .choiceLeft hnext', .left hrel'⟩
      · obtain ⟨next', hnext', hrel'⟩ := (hright hrightRel action).2 next hstep
        exact ⟨next', .choiceRight hnext', .right hrel'⟩

theorem choice_congr {left₁ left₂ right₁ right₂ : Process Action}
    (hleft : (lts (Action := Action)).HomBisimilarity left₁ left₂)
    (hright : (lts (Action := Action)).HomBisimilarity right₁ right₂) :
    (lts (Action := Action)).HomBisimilarity (.choice left₁ right₁) (.choice left₂ right₂) := by
  obtain ⟨leftRel, hleftRel, hleftBisim⟩ := hleft
  obtain ⟨rightRel, hrightRel, hrightBisim⟩ := hright
  exact ⟨ChoiceLift leftRel rightRel, .choice hleftRel hrightRel,
    choiceLift_isBisimulation hleftBisim hrightBisim⟩

/-- **Prefix preserves strong bisimilarity.** For every action $a$ and all finite CCS processes
$P$ and $Q$, if $P$ and $Q$ are strongly bisimilar in the labelled transition system of finite
CCS, then the prefixed processes $a.P$ and $a.Q$ are strongly bisimilar there as well. -/
theorem prefix_congr (action : Action) {left right : Process Action}
    (hcontinuation : (lts (Action := Action)).HomBisimilarity left right) :
    (lts (Action := Action)).HomBisimilarity (.prefix action left) (.prefix action right) := by
  obtain ⟨relation, hrel, hbisim⟩ := hcontinuation
  let prefixed : Process Action → Process Action → Prop := fun p q =>
    (p = .prefix action left ∧ q = .prefix action right) ∨ relation p q
  have hbisim' : (lts (Action := Action)).IsHomBisimulation prefixed := by
    intro p q hpq label
    constructor
    · intro p' hstep
      rcases hpq with ⟨rfl, rfl⟩ | hpq
      · cases hstep
        exact ⟨right, .prefix _ _, Or.inr hrel⟩
      · obtain ⟨q', hq', hpq'⟩ := (hbisim hpq label).1 p' hstep
        exact ⟨q', hq', Or.inr hpq'⟩
    · intro q' hstep
      rcases hpq with ⟨rfl, rfl⟩ | hpq
      · cases hstep
        exact ⟨left, .prefix _ _, Or.inr hrel⟩
      · obtain ⟨p', hp', hpq'⟩ := (hbisim hpq label).2 q' hstep
        exact ⟨p', hp', Or.inr hpq'⟩
  exact ⟨prefixed, Or.inl ⟨rfl, rfl⟩, hbisim'⟩

/-- **Reflexive closure of a relation on processes.** Given a relation $E$ on finite CCS processes,
its equation closure relates $P$ to $Q$ exactly when $P = Q$ or $E(P, Q)$; that is, it is the
reflexive closure of $E$.

It is used to prove the algebraic laws of nondeterministic choice up to strong bisimilarity. -/
def EquationClosure (equation : Process Action → Process Action → Prop) :
    Process Action → Process Action → Prop :=
  fun left right => left = right ∨ equation left right

theorem equationClosure_isBisimulation
    {equation : Process Action → Process Action → Prop}
    (hforward : ∀ ⦃left right action next⦄,
      equation left right → Step left action next → Step right action next)
    (hbackward : ∀ ⦃left right action next⦄,
      equation left right → Step right action next → Step left action next) :
    (lts (Action := Action)).IsHomBisimulation (EquationClosure equation) := by
  intro left right hrel action
  constructor
  · intro next hstep
    rcases hrel with rfl | hrel
    · exact ⟨next, hstep, Or.inl rfl⟩
    · exact ⟨next, hforward hrel hstep, Or.inl rfl⟩
  · intro next hstep
    rcases hrel with rfl | hrel
    · exact ⟨next, hstep, Or.inl rfl⟩
    · exact ⟨next, hbackward hrel hstep, Or.inl rfl⟩

theorem choice_comm (left right : Process Action) :
    (lts (Action := Action)).HomBisimilarity (.choice left right) (.choice right left) := by
  let equation : Process Action → Process Action → Prop := fun p q =>
    p = .choice left right ∧ q = .choice right left
  refine ⟨EquationClosure equation, Or.inr ⟨rfl, rfl⟩, equationClosure_isBisimulation ?_ ?_⟩
  · rintro p q action next ⟨rfl, rfl⟩ hstep
    rw [choice_step_iff] at hstep ⊢
    exact hstep.symm
  · rintro p q action next ⟨rfl, rfl⟩ hstep
    rw [choice_step_iff] at hstep ⊢
    exact hstep.symm

theorem choice_nil_left (process : Process Action) :
    (lts (Action := Action)).HomBisimilarity (.choice .nil process) process := by
  let equation : Process Action → Process Action → Prop := fun p q =>
    p = .choice .nil process ∧ q = process
  refine ⟨EquationClosure equation, Or.inr ⟨rfl, rfl⟩, equationClosure_isBisimulation ?_ ?_⟩
  · rintro p q action next ⟨rfl, rfl⟩ hstep
    rw [choice_step_iff] at hstep
    rcases hstep with hstep | hstep
    · exact (nil_no_step hstep).elim
    · exact hstep
  · rintro p q action next ⟨rfl, rfl⟩ hstep
    exact .choiceRight hstep

theorem choice_nil_right (process : Process Action) :
    (lts (Action := Action)).HomBisimilarity (.choice process .nil) process := by
  exact (choice_comm process .nil).trans (choice_nil_left process)

theorem choice_idem (process : Process Action) :
    (lts (Action := Action)).HomBisimilarity (.choice process process) process := by
  let equation : Process Action → Process Action → Prop := fun p q =>
    p = .choice process process ∧ q = process
  refine ⟨EquationClosure equation, Or.inr ⟨rfl, rfl⟩, equationClosure_isBisimulation ?_ ?_⟩
  · rintro p q action next ⟨rfl, rfl⟩ hstep
    rw [choice_step_iff] at hstep
    exact hstep.elim id id
  · rintro p q action next ⟨rfl, rfl⟩ hstep
    exact .choiceLeft hstep

theorem choice_assoc (first second third : Process Action) :
    (lts (Action := Action)).HomBisimilarity
      (.choice (.choice first second) third)
      (.choice first (.choice second third)) := by
  let equation : Process Action → Process Action → Prop := fun p q =>
    p = .choice (.choice first second) third ∧
      q = .choice first (.choice second third)
  refine ⟨EquationClosure equation, Or.inr ⟨rfl, rfl⟩, equationClosure_isBisimulation ?_ ?_⟩
  · rintro p q action next ⟨rfl, rfl⟩ hstep
    repeat' rw [choice_step_iff] at hstep ⊢
    exact hstep.elim (fun h => h.elim Or.inl (fun hs => Or.inr (Or.inl hs)))
      (fun ht => Or.inr (Or.inr ht))
  · rintro p q action next ⟨rfl, rfl⟩ hstep
    repeat' rw [choice_step_iff] at hstep ⊢
    exact hstep.elim (fun hf => Or.inl (Or.inl hf))
      (fun h => h.elim (fun hs => Or.inl (Or.inr hs)) Or.inr)

end Process

end Cslib.CCS
