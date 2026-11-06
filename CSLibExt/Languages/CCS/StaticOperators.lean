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
# CCS restriction and relabelling
-/
module

public import CSLibExt.Languages.CCS.Parallel

/-!
# CCS restriction and relabelling

This module extends the finite CCS language with the static operators of
restriction and relabelling.  Restrictions are finite lists of channel names,
and relabellings are finite tables with identity as the default.  This syntax
keeps equality decidable while making the CCS invariants structural: silent
actions cannot be restricted or renamed, and inputs and outputs are renamed
in complementary pairs.

The presentation follows Robin Milner, *Communication and Concurrency*,
Prentice Hall, 1989, Chapters 2--3 (ISBN 978-0-13-115007-2).
-/

@[expose] public section

namespace Cslib.CCS

/-- A visible CCS label, excluding the silent action. -/
inductive VisibleLabel (Name : Type*) where
  | input (name : Name)
  | output (name : Name)
  deriving DecidableEq

namespace VisibleLabel

variable {Name : Type*}

/-- **Complement of a visible label.** The complement of the input label on a channel $a$ is the
output label on $a$, and the complement of the output label on $a$ is the input label on $a$. -/
def complement : VisibleLabel Name → VisibleLabel Name
  | .input name => .output name
  | .output name => .input name

/-- **Visible labels as CCS labels.** The inclusion of visible labels into CCS labels sends the
input on a channel $a$ to the input on $a$, and the output on $a$ to the output on $a$. -/
def toLabel : VisibleLabel Name → Label Name
  | .input name => .input name
  | .output name => .output name

@[simp] theorem complement_complement (label : VisibleLabel Name) :
    label.complement.complement = label := by
  cases label <;> rfl

theorem toLabel_complementary (label : VisibleLabel Name) :
    label.toLabel.Complementary label.complement.toLabel := by
  cases label <;> simp [toLabel, complement, Label.Complementary]

end VisibleLabel

/-- **Relabelling.** A finite CCS relabelling over channel names is a finite list of entries
$(a, \ell)$, each pairing a channel name $a$ with a visible label $\ell$, that is, an input or an
output on some channel. The entry $(a, \ell)$ gives $\ell$ as the image of the input on $a$; the
image of the output on $a$ is then the complement of $\ell$. The first entry with name $a$ is
used, and a name occurring in no entry is mapped to itself. -/
structure Relabelling (Name : Type*) where
  entries : List (Name × VisibleLabel Name)
  deriving DecidableEq

namespace Relabelling

variable {Name : Type*} [DecidableEq Name]

def applyEntries : List (Name × VisibleLabel Name) → Name → VisibleLabel Name
  | [], name => .input name
  | (source, target) :: rest, name =>
      if name = source then target else applyEntries rest name

/-- **Applying a relabelling to a channel name.** Let $f$ be a finite relabelling whose table lists
the entries $(a_1, \ell_1), \dots, (a_k, \ell_k)$, where each $a_i$ is a channel name and each
$\ell_i$ a visible label. The image of a channel name $a$ under $f$ is $\ell_i$ for the first index
$i$ with $a_i = a$, and the input label on $a$ when no entry has name $a$. -/
def apply (rename : Relabelling Name) (name : Name) : VisibleLabel Name :=
  applyEntries rename.entries name

@[simp] theorem apply_empty (name : Name) :
    (Relabelling.mk []).apply name = .input name := rfl

@[simp] theorem apply_cons_self (source : Name) (target : VisibleLabel Name)
    (rest : List (Name × VisibleLabel Name)) :
    (Relabelling.mk ((source, target) :: rest)).apply source = target := by
  simp [apply, applyEntries]

theorem apply_cons_of_ne {source name : Name} {target : VisibleLabel Name}
    (rest : List (Name × VisibleLabel Name))
    (hne : name ≠ source) :
    (Relabelling.mk ((source, target) :: rest)).apply name =
      (Relabelling.mk rest).apply name := by
  simp [apply, applyEntries, hne]

end Relabelling

/-- **Static CCS processes.** Finite CCS processes with the static operators, over a type of
channel names, are built from the inactive process $0$ by the prefix $\alpha.P$ of a CCS action
$\alpha$ (silent, an input or an output) and a process $P$, the choice $P + Q$, the parallel
composition $P \mid Q$, the restriction $P \setminus L$ of $P$ by a finite list $L$ of names, and
the relabelling $P[f]$ of $P$ by a finite relabelling $f$.

Unlike function-valued operators, finite lists and tables preserve decidable
equality of processes and cannot express relabellings that alter the silent action $\tau$ or fail
to preserve complementary visible actions. -/
inductive StaticProcess (Name : Type*) where
  | nil
  | prefix (action : Label Name) (continuation : StaticProcess Name)
  | choice (left right : StaticProcess Name)
  | parallel (left right : StaticProcess Name)
  | restriction (blocked : List Name) (process : StaticProcess Name)
  | relabelling (rename : Relabelling Name) (process : StaticProcess Name)
  deriving DecidableEq

namespace StaticProcess

variable {Name : Type*} [DecidableEq Name]

/-- **Embedding finite CCS into CCS with static operators.** Each finite CCS process over CCS
labels is sent to the process with static operators of the same shape: the inactive process goes
to the inactive process, the prefix of an action $\alpha$ to a process $P$ goes to the prefix of
$\alpha$ to the image of $P$, and a choice or a parallel composition of $P$ and $Q$ goes to the
choice or the parallel composition of the images of $P$ and $Q$. -/
def ofProcess : Process (Label Name) → StaticProcess Name
  | .nil => .nil
  | .prefix action continuation => .prefix action (ofProcess continuation)
  | .choice left right => .choice (ofProcess left) (ofProcess right)
  | .parallel left right => .parallel (ofProcess left) (ofProcess right)

/-- **Relabelling an action.** For a relabelling $f$, the silent action $\tau$ is relabelled to
$\tau$, an input on a channel $a$ is relabelled to the image of $a$ under $f$, and an output on
$a$ is relabelled to the complement of the image of $a$ under $f$, each viewed as a CCS label. -/
def relabelAction (rename : Relabelling Name) : Label Name → Label Name
  | .tau => .tau
  | .input name => (rename.apply name).toLabel
  | .output name => (rename.apply name).complement.toLabel

@[simp] theorem relabelAction_tau (rename : Relabelling Name) :
    relabelAction rename (.tau : Label Name) = .tau := rfl

@[simp] theorem relabelAction_input (rename : Relabelling Name) (name : Name) :
    relabelAction rename (.input name) = (rename.apply name).toLabel := rfl

@[simp] theorem relabelAction_output (rename : Relabelling Name) (name : Name) :
    relabelAction rename (.output name) = (rename.apply name).complement.toLabel := rfl

/-- **Relabelling preserves complementary actions.** For every relabelling $f$ and all CCS labels
$\alpha$ and $\beta$, if $\alpha$ and $\beta$ are complementary, then the actions obtained by
relabelling $\alpha$ and $\beta$ with $f$ are complementary. -/
theorem relabelAction_complementary {left right : Label Name}
    (h : left.Complementary right) (rename : Relabelling Name) :
    (relabelAction rename left).Complementary (relabelAction rename right) := by
  cases left with
  | tau => exact False.elim (Label.not_complementary_tau_left right h)
  | input leftName =>
      cases right with
      | tau => exact False.elim (Label.not_complementary_tau_right (.input leftName) h)
      | input rightName => exact False.elim h
      | output rightName =>
          change leftName = rightName at h
          subst rightName
          exact VisibleLabel.toLabel_complementary (rename.apply leftName)
  | output leftName =>
      cases right with
      | tau => exact False.elim (Label.not_complementary_tau_right (.output leftName) h)
      | input rightName =>
          change leftName = rightName at h
          subst rightName
          exact Label.complementary_symm
            (VisibleLabel.toLabel_complementary (rename.apply leftName))
      | output rightName => exact False.elim h

/-- **Actions permitted by a restriction.** Given a finite list $L$ of blocked channel names, the
silent action $\tau$ is always permitted, and an input or an output on a channel $a$ is permitted
exactly when $a \notin L$. -/
def Allowed (blocked : List Name) : Label Name → Prop
  | .tau => True
  | .input name => name ∉ blocked
  | .output name => name ∉ blocked

/-- Whether a finite restriction permits an action is decidable. -/
instance instDecidableAllowed (blocked : List Name) (action : Label Name) :
    Decidable (Allowed blocked action) := by
  cases action <;> simp only [Allowed] <;> infer_instance

omit [DecidableEq Name] in
@[simp] theorem allowed_tau (blocked : List Name) :
    Allowed blocked (.tau : Label Name) := trivial

omit [DecidableEq Name] in
@[simp] theorem allowed_input (blocked : List Name) (name : Name) :
    Allowed blocked (.input name) ↔ name ∉ blocked := Iff.rfl

omit [DecidableEq Name] in
@[simp] theorem allowed_output (blocked : List Name) (name : Name) :
    Allowed blocked (.output name) ↔ name ∉ blocked := Iff.rfl

/-- **Transitions of static CCS.** The labelled transition relation $P \xrightarrow{\alpha} P'$ on
static CCS processes, with actions $\alpha$ the CCS labels (silent $\tau$, inputs and outputs), is
the least relation closed under the following rules, where $\alpha.P$ is the prefix, $P + Q$ the
choice, $P \mid Q$ the parallel composition, $P \setminus L$ the restriction of $P$ by a finite
list $L$ of channel names, and $P[f]$ the relabelling of $P$ by a finite relabelling $f$. The
prefix has the transition $\alpha.P \xrightarrow{\alpha} P$. If $P \xrightarrow{\alpha} P'$, then
$P + Q \xrightarrow{\alpha} P'$, $Q + P \xrightarrow{\alpha} P'$,
$P \mid Q \xrightarrow{\alpha} P' \mid Q$ and $Q \mid P \xrightarrow{\alpha} Q \mid P'$. If
$P \xrightarrow{\alpha} P'$ and $Q \xrightarrow{\beta} Q'$ where $\alpha$ and $\beta$ are
complementary (an input and an output on the same channel), then
$P \mid Q \xrightarrow{\tau} P' \mid Q'$. If $P \xrightarrow{\alpha} P'$ and $\alpha$ is $\tau$ or
its channel is not in $L$, then $P \setminus L \xrightarrow{\alpha} P' \setminus L$. If
$P \xrightarrow{\alpha} P'$, then $P[f] \xrightarrow{f(\alpha)} P'[f]$, where $f(\tau) = \tau$, an
input on a channel $a$ is sent to the visible label $f(a)$ that $f$ assigns to $a$, and an output
on $a$ is sent to the complement of $f(a)$. -/
inductive Step : StaticProcess Name → Label Name → StaticProcess Name → Prop
  | prefix (action) (continuation) : Step (.prefix action continuation) action continuation
  | choiceLeft {left right next action} (step : Step left action next) :
      Step (.choice left right) action next
  | choiceRight {left right next action} (step : Step right action next) :
      Step (.choice left right) action next
  | parallelLeft {left right next action} (step : Step left action next) :
      Step (.parallel left right) action (.parallel next right)
  | parallelRight {left right next action} (step : Step right action next) :
      Step (.parallel left right) action (.parallel left next)
  | communicate {left right left' right' leftAction rightAction}
      (leftStep : Step left leftAction left') (rightStep : Step right rightAction right')
      (complementary : leftAction.Complementary rightAction) :
      Step (.parallel left right) .tau (.parallel left' right')
  | restrict {blocked process next action}
      (step : Step process action next) (allowed : Allowed blocked action) :
      Step (.restriction blocked process) action (.restriction blocked next)
  | relabel {rename process next action} (step : Step process action next) :
      Step (.relabelling rename process) (relabelAction rename action)
        (.relabelling rename next)

/-- **Transition system of CCS with restriction and relabelling.** The labelled transition system
of finite CCS with static operators has the finite CCS processes with restriction and relabelling
as states and the CCS labels as labels, and its transitions are the steps of the structural
operational semantics of these processes. -/
def lts : Cslib.LTS (StaticProcess Name) (Label Name) := ⟨Step⟩

open Cslib.LTS

theorem nil_no_step {action : Label Name} {next : StaticProcess Name} :
    ¬Step .nil action next := by
  intro h
  cases h

theorem prefix_step_iff {head action : Label Name} {continuation next : StaticProcess Name} :
    Step (.prefix head continuation) action next ↔
      action = head ∧ next = continuation := by
  constructor
  · intro h
    cases h
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact .prefix _ _

theorem choice_step_iff {left right next : StaticProcess Name} {action : Label Name} :
    Step (.choice left right) action next ↔ Step left action next ∨ Step right action next := by
  constructor
  · intro h
    cases h with
    | choiceLeft step => exact Or.inl step
    | choiceRight step => exact Or.inr step
  · rintro (step | step)
    · exact .choiceLeft step
    · exact .choiceRight step

theorem restriction_step_iff {blocked : List Name} {process next : StaticProcess Name}
    {action : Label Name} :
    Step (.restriction blocked process) action next ↔
      ∃ process', Step process action process' ∧ Allowed blocked action ∧
        next = .restriction blocked process' := by
  constructor
  · intro h
    cases h with
    | restrict step allowed => exact ⟨_, step, allowed, rfl⟩
  · rintro ⟨process', step, allowed, rfl⟩
    exact .restrict step allowed

theorem relabelling_step_iff {rename : Relabelling Name}
    {process next : StaticProcess Name} {action : Label Name} :
    Step (.relabelling rename process) action next ↔
      ∃ sourceAction process', Step process sourceAction process' ∧
        action = relabelAction rename sourceAction ∧
        next = .relabelling rename process' := by
  constructor
  · intro h
    cases h with
    | relabel step => exact ⟨_, _, step, rfl, rfl⟩
  · rintro ⟨sourceAction, process', step, rfl, rfl⟩
    exact .relabel step

/-- **Lifting a relation through a restriction.** Given a finite list $L$ of channel names and a
relation $R$ on static CCS processes, the lifted relation relates $P$ to $Q$ exactly when either
$R$ relates $P$ to $Q$, or $P = P' \setminus L$ and $Q = Q' \setminus L$ for some processes $P'$
and $Q'$ that $R$ relates. -/
inductive RestrictionLift (blocked : List Name)
    (relation : StaticProcess Name → StaticProcess Name → Prop) :
    StaticProcess Name → StaticProcess Name → Prop
  | base {left right} (related : relation left right) : RestrictionLift blocked relation left right
  | restriction {left right} (related : relation left right) :
      RestrictionLift blocked relation (.restriction blocked left) (.restriction blocked right)

theorem restrictionLift_isSimulation {blocked : List Name}
    {relation : StaticProcess Name → StaticProcess Name → Prop}
    (hsim : lts.IsHomSimulation relation) :
    lts.IsHomSimulation (RestrictionLift blocked relation) := by
  intro source target hrel action next hstep
  cases hrel with
  | base hrel =>
      obtain ⟨next', hnext', hrel'⟩ := hsim.follow hrel hstep
      exact ⟨next', hnext', .base hrel'⟩
  | restriction hrel =>
      change Step (.restriction blocked _) action next at hstep
      rw [restriction_step_iff] at hstep
      obtain ⟨source', hsource', allowed, rfl⟩ := hstep
      obtain ⟨target', htarget', hrel'⟩ := hsim.follow hrel hsource'
      exact ⟨.restriction blocked target', .restrict htarget' allowed, .restriction hrel'⟩

theorem restrictionLift_isBisimulation {blocked : List Name}
    {relation : StaticProcess Name → StaticProcess Name → Prop}
    (hbisim : lts.IsHomBisimulation relation) :
    lts.IsHomBisimulation (RestrictionLift blocked relation) := by
  intro source target hrel action
  constructor
  · intro next hstep
    cases hrel with
    | base hrel =>
        obtain ⟨next', hnext', hrel'⟩ := (hbisim hrel _).1 next hstep
        exact ⟨next', hnext', .base hrel'⟩
    | restriction hrel =>
        change Step (.restriction blocked _) action next at hstep
        rw [restriction_step_iff] at hstep
        obtain ⟨source', hsource', allowed, rfl⟩ := hstep
        obtain ⟨target', htarget', hrel'⟩ := (hbisim hrel _).1 _ hsource'
        exact ⟨.restriction blocked target', .restrict htarget' allowed, .restriction hrel'⟩
  · intro next hstep
    cases hrel with
    | base hrel =>
        obtain ⟨next', hnext', hrel'⟩ := (hbisim hrel _).2 next hstep
        exact ⟨next', hnext', .base hrel'⟩
    | restriction hrel =>
        change Step (.restriction blocked _) action next at hstep
        rw [restriction_step_iff] at hstep
        obtain ⟨target', htarget', allowed, rfl⟩ := hstep
        obtain ⟨source', hsource', hrel'⟩ := (hbisim hrel _).2 _ htarget'
        exact ⟨.restriction blocked source', .restrict hsource' allowed, .restriction hrel'⟩

/-- **Restriction preserves strong bisimilarity.** For every finite list $L$ of channel names and
all static CCS processes $P$ and $Q$, if $P$ and $Q$ are strongly bisimilar in the labelled
transition system of finite CCS with static operators, then so are the restricted processes
$P \setminus L$ and $Q \setminus L$. -/
theorem restriction_congr (blocked : List Name) {left right : StaticProcess Name}
    (h : lts.HomBisimilarity left right) :
    lts.HomBisimilarity (.restriction blocked left) (.restriction blocked right) := by
  obtain ⟨relation, hrel, hbisim⟩ := h
  exact ⟨RestrictionLift blocked relation, .restriction hrel,
    restrictionLift_isBisimulation hbisim⟩

/-- **Closure of a relation under one relabelling.** Given a relabelling $f$ and a relation $R$
on finite CCS processes with static operators, the lifted relation is the least relation that
relates $P$ to $Q$ and relates the relabelling of $P$ by $f$ to the relabelling of $Q$ by $f$
whenever $R$ relates $P$ to $Q$. -/
inductive RelabellingLift (rename : Relabelling Name)
    (relation : StaticProcess Name → StaticProcess Name → Prop) :
    StaticProcess Name → StaticProcess Name → Prop
  | base {left right} (related : relation left right) : RelabellingLift rename relation left right
  | relabelling {left right} (related : relation left right) :
      RelabellingLift rename relation (.relabelling rename left) (.relabelling rename right)

theorem relabellingLift_isSimulation {rename : Relabelling Name}
    {relation : StaticProcess Name → StaticProcess Name → Prop}
    (hsim : lts.IsHomSimulation relation) :
    lts.IsHomSimulation (RelabellingLift rename relation) := by
  intro source target hrel action next hstep
  cases hrel with
  | base hrel =>
      obtain ⟨next', hnext', hrel'⟩ := hsim.follow hrel hstep
      exact ⟨next', hnext', .base hrel'⟩
  | relabelling hrel =>
      change Step (.relabelling rename _) action next at hstep
      rw [relabelling_step_iff] at hstep
      obtain ⟨sourceAction, source', hsource', rfl, rfl⟩ := hstep
      obtain ⟨target', htarget', hrel'⟩ := hsim.follow hrel hsource'
      exact ⟨.relabelling rename target', .relabel htarget', .relabelling hrel'⟩

theorem relabellingLift_isBisimulation {rename : Relabelling Name}
    {relation : StaticProcess Name → StaticProcess Name → Prop}
    (hbisim : lts.IsHomBisimulation relation) :
    lts.IsHomBisimulation (RelabellingLift rename relation) := by
  intro source target hrel action
  constructor
  · intro next hstep
    cases hrel with
    | base hrel =>
        obtain ⟨next', hnext', hrel'⟩ := (hbisim hrel _).1 next hstep
        exact ⟨next', hnext', .base hrel'⟩
    | relabelling hrel =>
        change Step (.relabelling rename _) action next at hstep
        rw [relabelling_step_iff] at hstep
        obtain ⟨sourceAction, source', hsource', rfl, rfl⟩ := hstep
        obtain ⟨target', htarget', hrel'⟩ := (hbisim hrel _).1 _ hsource'
        exact ⟨.relabelling rename target', .relabel htarget', .relabelling hrel'⟩
  · intro next hstep
    cases hrel with
    | base hrel =>
        obtain ⟨next', hnext', hrel'⟩ := (hbisim hrel _).2 next hstep
        exact ⟨next', hnext', .base hrel'⟩
    | relabelling hrel =>
        change Step (.relabelling rename _) action next at hstep
        rw [relabelling_step_iff] at hstep
        obtain ⟨sourceAction, target', htarget', rfl, rfl⟩ := hstep
        obtain ⟨source', hsource', hrel'⟩ := (hbisim hrel _).2 _ htarget'
        exact ⟨.relabelling rename source', .relabel hsource', .relabelling hrel'⟩

/-- **Relabelling preserves strong bisimilarity.** For every relabelling $f$ and all finite CCS
processes $P$ and $Q$ with static operators, if $P$ and $Q$ are strongly bisimilar in the
labelled transition system of finite CCS with static operators, then the relabellings of $P$
and of $Q$ by $f$ are strongly bisimilar there. -/
theorem relabelling_congr (rename : Relabelling Name) {left right : StaticProcess Name}
    (h : lts.HomBisimilarity left right) :
    lts.HomBisimilarity (.relabelling rename left) (.relabelling rename right) := by
  obtain ⟨relation, hrel, hbisim⟩ := h
  exact ⟨RelabellingLift rename relation, .relabelling hrel,
    relabellingLift_isBisimulation hbisim⟩

end StaticProcess

end Cslib.CCS
