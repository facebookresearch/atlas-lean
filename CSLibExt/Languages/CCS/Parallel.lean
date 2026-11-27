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
# CCS parallel composition and synchronization
-/
module

public import CSLibExt.Languages.CCS.Choice

/-!
# CCS parallel composition

This module extends the finite choice fragment with complementary input and
output actions, parallel composition, and the CCS communication rule.  It
proves the structural transition equations and establishes that strong
bisimilarity is a congruence for every constructor, including parallel
composition.

The presentation follows Robin Milner, *Communication and Concurrency*,
Prentice Hall, 1989, Chapters 2--3 (ISBN 978-0-13-115007-2).
-/

@[expose] public section

namespace Cslib.CCS

/-- **CCS labels.** For a set of names, a CCS label is either the silent action $\tau$, the input
on a name $a$, or the output on a name $a$. -/
inductive Label (Name : Type*) where
  | tau
  | input (name : Name)
  | output (name : Name)
  deriving DecidableEq

namespace Label

variable {Name : Type*}

/-- The silent CCS action is the distinguished `HasTau` label. -/
instance : HasTau (Label Name) := ⟨.tau⟩

/-- **Complementary labels.** Two CCS labels are complementary when one is the input on a name $a$
and the other is the output on the same name $a$, in either order. No other pair of labels is
complementary; in particular the silent label $\tau$ has no complement. -/
def Complementary : Label Name → Label Name → Prop
  | .input left, .output right => left = right
  | .output left, .input right => left = right
  | _, _ => False

theorem complementary_symm {left right : Label Name}
    (h : Complementary left right) : Complementary right left := by
  cases left <;> cases right <;> simp_all [Complementary]

theorem not_complementary_tau_left (label : Label Name) :
    ¬Complementary .tau label := by
  cases label <;> simp [Complementary]

theorem not_complementary_tau_right (label : Label Name) :
    ¬Complementary label .tau := by
  intro h
  exact not_complementary_tau_left label (complementary_symm h)

/-- **Synchronization of CCS labels.** Let the names form a type with decidable equality. For
labels $a$ and $b$, the synchronization of $a$ with $b$ is the silent action $\tau$ when $a$ is
the input on a name $n$ and $b$ is the output on the same name $n$, or when $a$ is the output on
$n$ and $b$ is the input on $n$. For every other pair of labels, including any pair involving
$\tau$, there is no result.

This partial function supplies the communication rule of the CCS operational semantics. -/
def synchronize [DecidableEq Name] : Label Name → Label Name → Option (Label Name)
  | .input left, .output right => if left = right then some .tau else none
  | .output left, .input right => if left = right then some .tau else none
  | _, _ => none

theorem synchronize_eq_some_iff [DecidableEq Name]
    {left right result : Label Name} :
    synchronize left right = some result ↔ result = .tau ∧ Complementary left right := by
  cases left <;> cases right <;>
    simp [synchronize, Complementary, and_comm, eq_comm]

end Label

namespace Process

variable {Name : Type*} [DecidableEq Name]

/-- **CCS transition relation with communication.** The transition relation on CCS processes with
labels over a set of names given by the raw step relation for the synchronization function under
which an input and an output on the same name, in either order, synchronize to the silent label
$\tau$, and no other pair of labels synchronizes. -/
abbrev CommunicationStep : Process (Label Name) → Label Name → Process (Label Name) → Prop :=
  RawStep Label.synchronize

/-- **Labelled transition system of CCS with communication.** The labelled transition system whose
states are CCS processes with labels over a set of names, whose labels are CCS labels over those
names, and whose transition relation is the CCS transition relation with communication. -/
def communicationLTS : Cslib.LTS (Process (Label Name)) (Label Name) :=
  ⟨CommunicationStep⟩

open Cslib.LTS

theorem communication_nil_no_step {label : Label Name} {next : Process (Label Name)} :
    ¬CommunicationStep .nil label next := by
  intro h
  cases h

theorem communication_prefix_step_iff {head label : Label Name}
    {continuation next : Process (Label Name)} :
    CommunicationStep (.prefix head continuation) label next ↔
      label = head ∧ next = continuation := by
  constructor
  · intro h
    cases h
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact .prefix _ _

theorem communication_choice_step_iff {left right next : Process (Label Name)}
    {label : Label Name} :
    CommunicationStep (.choice left right) label next ↔
      CommunicationStep left label next ∨ CommunicationStep right label next := by
  constructor
  · intro h
    cases h with
    | choiceLeft step => exact Or.inl step
    | choiceRight step => exact Or.inr step
  · rintro (step | step)
    · exact .choiceLeft step
    · exact .choiceRight step

/-- **Transitions of a parallel composition.** For CCS processes $P$, $Q$, $R$ and a CCS label $a$,
the parallel composition $P \mid Q$ has a transition labelled $a$ to $R$ in the CCS transition
relation with communication if and only if one of the following holds: $P$ has a transition
labelled $a$ to some $P'$ and $R = P' \mid Q$; or $Q$ has a transition labelled $a$ to some $Q'$
and $R = P \mid Q'$; or $a = \tau$ and there are processes $P'$, $Q'$ and complementary labels
$b$, $c$ such that $P$ has a transition labelled $b$ to $P'$, $Q$ has a transition labelled $c$
to $Q'$, and $R = P' \mid Q'$. -/
theorem communication_parallel_step_iff {left right next : Process (Label Name)}
    {label : Label Name} :
    CommunicationStep (.parallel left right) label next ↔
      (∃ left', CommunicationStep left label left' ∧ next = .parallel left' right) ∨
      (∃ right', CommunicationStep right label right' ∧ next = .parallel left right') ∨
      (label = .tau ∧ ∃ left' right' leftLabel rightLabel,
        CommunicationStep left leftLabel left' ∧ CommunicationStep right rightLabel right' ∧
        leftLabel.Complementary rightLabel ∧ next = .parallel left' right') := by
  constructor
  · intro h
    cases h with
    | parallelLeft step => exact Or.inl ⟨_, step, rfl⟩
    | parallelRight step => exact Or.inr (Or.inl ⟨_, step, rfl⟩)
    | communicate leftStep rightStep syncs =>
        obtain ⟨rfl, complementary⟩ := Label.synchronize_eq_some_iff.mp syncs
        exact Or.inr (Or.inr ⟨rfl, _, _, _, _, leftStep, rightStep,
          complementary, rfl⟩)
  · rintro (⟨left', step, rfl⟩ | ⟨right', step, rfl⟩ |
      ⟨rfl, left', right', leftLabel, rightLabel, leftStep, rightStep,
        complementary, rfl⟩)
    · exact .parallelLeft step
    · exact .parallelRight step
    · exact .communicate leftStep rightStep
        (Label.synchronize_eq_some_iff.mpr ⟨rfl, complementary⟩)

/-- **Parallel lift of two relations.** Given two relations $R$ and $S$ on CCS processes with
labels over a set of names, their parallel lift relates a process $U$ to a process $V$ exactly
when $R$ relates $U$ to $V$, or $S$ relates $U$ to $V$, or $U = P_1 \mid Q_1$ and
$V = P_2 \mid Q_2$ where $R$ relates $P_1$ to $P_2$ and $S$ relates $Q_1$ to $Q_2$. -/
inductive ParallelLift
    (leftRel rightRel : Process (Label Name) → Process (Label Name) → Prop) :
    Process (Label Name) → Process (Label Name) → Prop
  | left {left₁ left₂} (relation : leftRel left₁ left₂) :
      ParallelLift leftRel rightRel left₁ left₂
  | right {right₁ right₂} (relation : rightRel right₁ right₂) :
      ParallelLift leftRel rightRel right₁ right₂
  | parallel {left₁ left₂ right₁ right₂}
      (left : leftRel left₁ left₂) (right : rightRel right₁ right₂) :
      ParallelLift leftRel rightRel (.parallel left₁ right₁) (.parallel left₂ right₂)

theorem parallelLift_isSimulation
    {leftRel rightRel : Process (Label Name) → Process (Label Name) → Prop}
    (hleft : (communicationLTS (Name := Name)).IsHomSimulation leftRel)
    (hright : (communicationLTS (Name := Name)).IsHomSimulation rightRel) :
    (communicationLTS (Name := Name)).IsHomSimulation (ParallelLift leftRel rightRel) := by
  intro source target hrel label next hstep
  cases hrel with
  | left hrel =>
      obtain ⟨next', hnext', hrel'⟩ := hleft.follow hrel hstep
      exact ⟨next', hnext', .left hrel'⟩
  | right hrel =>
      obtain ⟨next', hnext', hrel'⟩ := hright.follow hrel hstep
      exact ⟨next', hnext', .right hrel'⟩
  | parallel hleftRel hrightRel =>
      cases hstep with
      | parallelLeft step =>
          obtain ⟨next', hnext', hrel'⟩ := hleft.follow hleftRel step
          exact ⟨.parallel next' _, .parallelLeft hnext', .parallel hrel' hrightRel⟩
      | parallelRight step =>
          obtain ⟨next', hnext', hrel'⟩ := hright.follow hrightRel step
          exact ⟨.parallel _ next', .parallelRight hnext', .parallel hleftRel hrel'⟩
      | communicate leftStep rightStep syncs =>
          obtain ⟨left', hleft', hleftRel'⟩ := hleft.follow hleftRel leftStep
          obtain ⟨right', hright', hrightRel'⟩ := hright.follow hrightRel rightStep
          exact ⟨.parallel left' right', .communicate hleft' hright' syncs,
            .parallel hleftRel' hrightRel'⟩

theorem parallelLift_isBisimulation
    {leftRel rightRel : Process (Label Name) → Process (Label Name) → Prop}
    (hleft : (communicationLTS (Name := Name)).IsHomBisimulation leftRel)
    (hright : (communicationLTS (Name := Name)).IsHomBisimulation rightRel) :
    (communicationLTS (Name := Name)).IsHomBisimulation (ParallelLift leftRel rightRel) := by
  intro source target hrel label
  constructor
  · intro next hstep
    cases hrel with
    | left hrel =>
        obtain ⟨next', hnext', hrel'⟩ := (hleft hrel _).1 next hstep
        exact ⟨next', hnext', .left hrel'⟩
    | right hrel =>
        obtain ⟨next', hnext', hrel'⟩ := (hright hrel _).1 next hstep
        exact ⟨next', hnext', .right hrel'⟩
    | parallel hleftRel hrightRel =>
        cases hstep with
        | parallelLeft step =>
            obtain ⟨next', hnext', hrel'⟩ := (hleft hleftRel _).1 _ step
            exact ⟨.parallel next' _, .parallelLeft hnext', .parallel hrel' hrightRel⟩
        | parallelRight step =>
            obtain ⟨next', hnext', hrel'⟩ := (hright hrightRel _).1 _ step
            exact ⟨.parallel _ next', .parallelRight hnext', .parallel hleftRel hrel'⟩
        | communicate leftStep rightStep syncs =>
            obtain ⟨left', hleft', hleftRel'⟩ := (hleft hleftRel _).1 _ leftStep
            obtain ⟨right', hright', hrightRel'⟩ := (hright hrightRel _).1 _ rightStep
            exact ⟨.parallel left' right', .communicate hleft' hright' syncs,
              .parallel hleftRel' hrightRel'⟩
  · intro next hstep
    cases hrel with
    | left hrel =>
        obtain ⟨next', hnext', hrel'⟩ := (hleft hrel _).2 next hstep
        exact ⟨next', hnext', .left hrel'⟩
    | right hrel =>
        obtain ⟨next', hnext', hrel'⟩ := (hright hrel _).2 next hstep
        exact ⟨next', hnext', .right hrel'⟩
    | parallel hleftRel hrightRel =>
        cases hstep with
        | parallelLeft step =>
            obtain ⟨next', hnext', hrel'⟩ := (hleft hleftRel _).2 _ step
            exact ⟨.parallel next' _, .parallelLeft hnext', .parallel hrel' hrightRel⟩
        | parallelRight step =>
            obtain ⟨next', hnext', hrel'⟩ := (hright hrightRel _).2 _ step
            exact ⟨.parallel _ next', .parallelRight hnext', .parallel hleftRel hrel'⟩
        | communicate leftStep rightStep syncs =>
            obtain ⟨left', hleft', hleftRel'⟩ := (hleft hleftRel _).2 _ leftStep
            obtain ⟨right', hright', hrightRel'⟩ := (hright hrightRel _).2 _ rightStep
            exact ⟨.parallel left' right', .communicate hleft' hright' syncs,
              .parallel hleftRel' hrightRel'⟩

/-- **Parallel composition preserves strong bisimilarity.** For CCS processes $P_1$, $P_2$, $Q_1$,
$Q_2$ with labels over a set of names: if $P_1$ and $P_2$ are strongly bisimilar and $Q_1$ and
$Q_2$ are strongly bisimilar in the labelled transition system of CCS with communication, then
the parallel compositions $P_1 \mid Q_1$ and $P_2 \mid Q_2$ are strongly bisimilar there. -/
theorem parallel_congr {left₁ left₂ right₁ right₂ : Process (Label Name)}
    (hleft : (communicationLTS (Name := Name)).HomBisimilarity left₁ left₂)
    (hright : (communicationLTS (Name := Name)).HomBisimilarity right₁ right₂) :
    (communicationLTS (Name := Name)).HomBisimilarity
      (.parallel left₁ right₁) (.parallel left₂ right₂) := by
  obtain ⟨leftRel, hleftRel, hleftBisim⟩ := hleft
  obtain ⟨rightRel, hrightRel, hrightBisim⟩ := hright
  exact ⟨ParallelLift leftRel rightRel, .parallel hleftRel hrightRel,
    parallelLift_isBisimulation hleftBisim hrightBisim⟩

/-- **Prefix preserves strong bisimilarity in CCS with communication.** For every CCS label $a$ and
all CCS processes $P$ and $Q$: if $P$ and $Q$ are strongly bisimilar in the labelled transition
system of CCS with communication, then so are the prefixed processes $a.P$ and $a.Q$. -/
theorem communication_prefix_congr (label : Label Name)
    {left right : Process (Label Name)}
    (hcontinuation : (communicationLTS (Name := Name)).HomBisimilarity left right) :
    (communicationLTS (Name := Name)).HomBisimilarity
      (.prefix label left) (.prefix label right) := by
  obtain ⟨relation, hrel, hbisim⟩ := hcontinuation
  let lifted : Process (Label Name) → Process (Label Name) → Prop := fun p q =>
    (p = .prefix label left ∧ q = .prefix label right) ∨ relation p q
  refine ⟨lifted, Or.inl ⟨rfl, rfl⟩, ?_⟩
  intro p q hpq action
  constructor
  · intro next hstep
    rcases hpq with ⟨rfl, rfl⟩ | hpq
    · cases hstep
      exact ⟨right, .prefix _ _, Or.inr hrel⟩
    · obtain ⟨q', hq', hpq'⟩ := (hbisim hpq action).1 next hstep
      exact ⟨q', hq', Or.inr hpq'⟩
  · intro next hstep
    rcases hpq with ⟨rfl, rfl⟩ | hpq
    · cases hstep
      exact ⟨left, .prefix _ _, Or.inr hrel⟩
    · obtain ⟨p', hp', hpq'⟩ := (hbisim hpq action).2 next hstep
      exact ⟨p', hp', Or.inr hpq'⟩

/-- **Choice preserves strong bisimilarity in CCS with communication.** For CCS processes $P_1$,
$P_2$, $Q_1$, $Q_2$ with labels over a set of names: if $P_1$ and $P_2$ are strongly bisimilar and
$Q_1$ and $Q_2$ are strongly bisimilar in the labelled transition system of CCS with
communication, then the choices $P_1 + Q_1$ and $P_2 + Q_2$ are strongly bisimilar there. -/
theorem communication_choice_congr {left₁ left₂ right₁ right₂ : Process (Label Name)}
    (hleft : (communicationLTS (Name := Name)).HomBisimilarity left₁ left₂)
    (hright : (communicationLTS (Name := Name)).HomBisimilarity right₁ right₂) :
    (communicationLTS (Name := Name)).HomBisimilarity
      (.choice left₁ right₁) (.choice left₂ right₂) := by
  obtain ⟨leftRel, hleftRel, hleftBisim⟩ := hleft
  obtain ⟨rightRel, hrightRel, hrightBisim⟩ := hright
  let lifted : Process (Label Name) → Process (Label Name) → Prop := fun p q =>
    (∃ l₁ l₂ r₁ r₂, p = .choice l₁ r₁ ∧ q = .choice l₂ r₂ ∧
      leftRel l₁ l₂ ∧ rightRel r₁ r₂) ∨ leftRel p q ∨ rightRel p q
  refine ⟨lifted, Or.inl ⟨_, _, _, _, rfl, rfl, hleftRel, hrightRel⟩, ?_⟩
  intro p q hpq action
  constructor
  · intro next hstep
    rcases hpq with ⟨l₁, l₂, r₁, r₂, rfl, rfl, hl, hr⟩ | hpq
    · change CommunicationStep (.choice l₁ r₁) action next at hstep
      rw [communication_choice_step_iff] at hstep
      rcases hstep with hstep | hstep
      · obtain ⟨next', hnext', hrel'⟩ := (hleftBisim hl action).1 next hstep
        exact ⟨next', .choiceLeft hnext', Or.inr (Or.inl hrel')⟩
      · obtain ⟨next', hnext', hrel'⟩ := (hrightBisim hr action).1 next hstep
        exact ⟨next', .choiceRight hnext', Or.inr (Or.inr hrel')⟩
    · rcases hpq with hpq | hpq
      · obtain ⟨next', hnext', hrel'⟩ := (hleftBisim hpq action).1 next hstep
        exact ⟨next', hnext', Or.inr (Or.inl hrel')⟩
      · obtain ⟨next', hnext', hrel'⟩ := (hrightBisim hpq action).1 next hstep
        exact ⟨next', hnext', Or.inr (Or.inr hrel')⟩
  · intro next hstep
    rcases hpq with ⟨l₁, l₂, r₁, r₂, rfl, rfl, hl, hr⟩ | hpq
    · change CommunicationStep (.choice l₂ r₂) action next at hstep
      rw [communication_choice_step_iff] at hstep
      rcases hstep with hstep | hstep
      · obtain ⟨next', hnext', hrel'⟩ := (hleftBisim hl action).2 next hstep
        exact ⟨next', .choiceLeft hnext', Or.inr (Or.inl hrel')⟩
      · obtain ⟨next', hnext', hrel'⟩ := (hrightBisim hr action).2 next hstep
        exact ⟨next', .choiceRight hnext', Or.inr (Or.inr hrel')⟩
    · rcases hpq with hpq | hpq
      · obtain ⟨next', hnext', hrel'⟩ := (hleftBisim hpq action).2 next hstep
        exact ⟨next', hnext', Or.inr (Or.inl hrel')⟩
      · obtain ⟨next', hnext', hrel'⟩ := (hrightBisim hpq action).2 next hstep
        exact ⟨next', hnext', Or.inr (Or.inr hrel')⟩

theorem equationClosure_isCommunicationBisimulation
    {equation : Process (Label Name) → Process (Label Name) → Prop}
    (hforward : ∀ ⦃left right label next⦄,
      equation left right → CommunicationStep left label next →
        ∃ next', CommunicationStep right label next' ∧ EquationClosure equation next next')
    (hbackward : ∀ ⦃left right label next⦄,
      equation left right → CommunicationStep right label next →
        ∃ next', CommunicationStep left label next' ∧ EquationClosure equation next' next) :
    (communicationLTS (Name := Name)).IsHomBisimulation (EquationClosure equation) := by
  intro left right hrel label
  constructor
  · intro next hstep
    rcases hrel with rfl | hrel
    · exact ⟨next, hstep, Or.inl rfl⟩
    · exact hforward hrel hstep
  · intro next hstep
    rcases hrel with rfl | hrel
    · exact ⟨next, hstep, Or.inl rfl⟩
    · exact hbackward hrel hstep

/-- **Parallel composition is commutative up to strong bisimilarity.** For all CCS processes $P$
and $Q$ with labels over a set of names, $P \mid Q$ and $Q \mid P$ are strongly bisimilar in the
labelled transition system of CCS with communication. -/
theorem parallel_comm (left right : Process (Label Name)) :
    (communicationLTS (Name := Name)).HomBisimilarity
      (.parallel left right) (.parallel right left) := by
  let equation : Process (Label Name) → Process (Label Name) → Prop := fun p q =>
    ∃ l r, p = .parallel l r ∧ q = .parallel r l
  refine ⟨EquationClosure equation, Or.inr ⟨left, right, rfl, rfl⟩,
    equationClosure_isCommunicationBisimulation ?_ ?_⟩
  · rintro p q label next ⟨l, r, rfl, rfl⟩ hstep
    cases hstep with
    | parallelLeft step =>
        exact ⟨.parallel r _, .parallelRight step,
          Or.inr ⟨_, _, rfl, rfl⟩⟩
    | parallelRight step =>
        exact ⟨.parallel _ l, .parallelLeft step,
          Or.inr ⟨_, _, rfl, rfl⟩⟩
    | communicate leftStep rightStep syncs =>
        obtain ⟨rfl, complementary⟩ := Label.synchronize_eq_some_iff.mp syncs
        exact ⟨.parallel _ _,
          .communicate rightStep leftStep
            (Label.synchronize_eq_some_iff.mpr
              ⟨rfl, Label.complementary_symm complementary⟩),
          Or.inr ⟨_, _, rfl, rfl⟩⟩
  · rintro p q label next ⟨l, r, rfl, rfl⟩ hstep
    cases hstep with
    | parallelLeft step =>
        exact ⟨.parallel l _, .parallelRight step,
          Or.inr ⟨_, _, rfl, rfl⟩⟩
    | parallelRight step =>
        exact ⟨.parallel _ r, .parallelLeft step,
          Or.inr ⟨_, _, rfl, rfl⟩⟩
    | communicate leftStep rightStep syncs =>
        obtain ⟨rfl, complementary⟩ := Label.synchronize_eq_some_iff.mp syncs
        exact ⟨.parallel _ _,
          .communicate rightStep leftStep
            (Label.synchronize_eq_some_iff.mpr
              ⟨rfl, Label.complementary_symm complementary⟩),
          Or.inr ⟨_, _, rfl, rfl⟩⟩

/-- **The inactive process is a left unit for parallel composition.** Let the names form a type
with decidable equality. For every CCS process $P$ over input, output and silent labels on these
names, the parallel composition $0 \mid P$ of the inactive process $0$ with $P$ is strongly
bisimilar to $P$ in the communication labelled transition system. -/
theorem parallel_nil_left (process : Process (Label Name)) :
    (communicationLTS (Name := Name)).HomBisimilarity (.parallel .nil process) process := by
  let equation : Process (Label Name) → Process (Label Name) → Prop := fun p q =>
    ∃ continuation, p = .parallel .nil continuation ∧ q = continuation
  refine ⟨EquationClosure equation, Or.inr ⟨process, rfl, rfl⟩,
    equationClosure_isCommunicationBisimulation ?_ ?_⟩
  · rintro p q label next ⟨continuation, rfl, rfl⟩ hstep
    cases hstep with
    | parallelLeft step => exact (communication_nil_no_step step).elim
    | parallelRight step =>
        exact ⟨_, step, Or.inr ⟨_, rfl, rfl⟩⟩
    | communicate leftStep _ _ => exact (communication_nil_no_step leftStep).elim
  · rintro p q label next ⟨continuation, rfl, rfl⟩ hstep
    exact ⟨.parallel .nil next, .parallelRight hstep,
      Or.inr ⟨_, rfl, rfl⟩⟩

/-- **The inactive process is a right unit for parallel composition.** Let the names form a type
with decidable equality. For every CCS process $P$ over input, output and silent labels on these
names, the parallel composition $P \mid 0$ of $P$ with the inactive process $0$ is strongly
bisimilar to $P$ in the communication labelled transition system. -/
theorem parallel_nil_right (process : Process (Label Name)) :
    (communicationLTS (Name := Name)).HomBisimilarity (.parallel process .nil) process := by
  exact (parallel_comm process .nil).trans (parallel_nil_left process)

end Process

end Cslib.CCS
