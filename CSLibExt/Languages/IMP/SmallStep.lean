/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Small-step semantics for IMP
-/
module

public import CSLibExt.Languages.IMP.Syntax
public import Mathlib.Logic.Relation

/-!
# Small-step operational semantics

The inductive relation `Step` describes single execution steps between
configurations, and `Steps` is its reflexive, transitive closure. A command
terminates from an initial state to a final state when it reaches `skip`.
The single-step relation is deterministic, and `skip` is its only terminal
command.
-/

@[expose] public section

namespace Cslib.IMP

/-- A configuration pairs a command with a state. -/
abbrev Config := Cmd × State

/-- Single small-step transitions between IMP configurations. -/
inductive Step : Config → Config → Prop
  | assign (state) (name) (value) :
      Step (.assign name value, state)
        (.skip, Function.update state name (value.eval state))
  | seqSkip (second) (state) :
      Step (.seq .skip second, state) (second, state)
  | seqStep {first first' second initial final}
      (step : Step (first, initial) (first', final)) :
      Step (.seq first second, initial) (.seq first' second, final)
  | iteTrue {guard thenBranch elseBranch state}
      (guardTrue : guard.eval state = true) :
      Step (.ite guard thenBranch elseBranch, state) (thenBranch, state)
  | iteFalse {guard thenBranch elseBranch state}
      (guardFalse : guard.eval state = false) :
      Step (.ite guard thenBranch elseBranch, state) (elseBranch, state)
  | whileStep (guard) (body) (state) :
      Step (.while guard body, state)
        (.ite guard (.seq body (.while guard body)) .skip, state)

/-- Finite sequences of small steps. -/
abbrev Steps : Config → Config → Prop := Relation.ReflTransGen Step

/-- A command terminates by reaching `skip` in a final state. -/
def Terminates (command : Cmd) (initial final : State) : Prop :=
  Steps (command, initial) (.skip, final)

namespace Step

theorem skip_not_step {state : State} {next : Config} :
    ¬ Step (.skip, state) next := by
  intro h
  cases h

@[simp]
theorem assign_iff {name : Nat} {value : AExp} {state : State} {next : Config} :
    Step (.assign name value, state) next ↔
      next = (.skip, Function.update state name (value.eval state)) := by
  constructor
  · intro h
    cases h
    rfl
  · rintro rfl
    exact .assign state name value

theorem seq_iff {first second : Cmd} {state : State} {next : Config} :
    Step (.seq first second, state) next ↔
      (first = .skip ∧ next = (second, state)) ∨
      ∃ first' state', Step (first, state) (first', state') ∧
        next = (.seq first' second, state') := by
  constructor
  · intro h
    cases h with
    | seqSkip => exact Or.inl ⟨rfl, rfl⟩
    | seqStep hstep => exact Or.inr ⟨_, _, hstep, rfl⟩
  · rintro (⟨rfl, rfl⟩ | ⟨first', state', hstep, rfl⟩)
    · exact .seqSkip second state
    · exact .seqStep hstep

theorem ite_iff {guard : BExp} {t e : Cmd} {state : State} {next : Config} :
    Step (.ite guard t e, state) next ↔
      (guard.eval state = true ∧ next = (t, state)) ∨
      (guard.eval state = false ∧ next = (e, state)) := by
  constructor
  · intro h
    cases h with
    | iteTrue hg => exact Or.inl ⟨hg, rfl⟩
    | iteFalse hg => exact Or.inr ⟨hg, rfl⟩
  · rintro (⟨hg, rfl⟩ | ⟨hg, rfl⟩)
    · exact .iteTrue hg
    · exact .iteFalse hg

@[simp]
theorem while_iff {guard : BExp} {body : Cmd} {state : State} {next : Config} :
    Step (.while guard body, state) next ↔
      next = (.ite guard (.seq body (.while guard body)) .skip, state) := by
  constructor
  · intro h
    cases h
    rfl
  · rintro rfl
    exact .whileStep guard body state

/-- The small-step relation is deterministic. -/
theorem deterministic {x y z : Config} (h1 : Step x y) (h2 : Step x z) : y = z := by
  induction h1 generalizing z with
  | assign =>
      rw [assign_iff] at h2
      exact h2.symm
  | seqSkip =>
      rw [seq_iff] at h2
      rcases h2 with ⟨_, hnext⟩ | ⟨_, _, hstep, _⟩
      · exact hnext.symm
      · exact absurd hstep skip_not_step
  | seqStep hstep ih =>
      rw [seq_iff] at h2
      rcases h2 with ⟨hskip, _⟩ | ⟨first'', state'', hstep2, hnext⟩
      · subst hskip
        exact absurd hstep skip_not_step
      · have hEq := ih hstep2
        rw [hnext]
        cases hEq
        rfl
  | iteTrue hg =>
      rw [ite_iff] at h2
      rcases h2 with ⟨_, hnext⟩ | ⟨hgfalse, _⟩
      · exact hnext.symm
      · simp [hg] at hgfalse
  | iteFalse hg =>
      rw [ite_iff] at h2
      rcases h2 with ⟨hgtrue, _⟩ | ⟨_, hnext⟩
      · simp [hg] at hgtrue
      · exact hnext.symm
  | whileStep =>
      rw [while_iff] at h2
      exact h2.symm

theorem exists_step {command : Cmd} {state : State} (h : command ≠ .skip) :
    ∃ next, Step (command, state) next := by
  revert h
  induction command with
  | skip =>
      intro h
      exact absurd rfl h
  | assign name value =>
      intro _
      exact ⟨_, .assign state name value⟩
  | seq first second ihFirst _ihSecond =>
      intro _
      by_cases hf : first = .skip
      · subst hf
        exact ⟨_, .seqSkip second state⟩
      · obtain ⟨⟨first', state'⟩, hstep⟩ := ihFirst hf
        exact ⟨_, .seqStep hstep⟩
  | ite guard thenBranch elseBranch _ihThen _ihElse =>
      intro _
      cases hguard : guard.eval state with
      | true => exact ⟨_, .iteTrue hguard⟩
      | false => exact ⟨_, .iteFalse hguard⟩
  | «while» guard body _ihBody =>
      intro _
      exact ⟨_, .whileStep guard body state⟩

theorem terminal_iff {command : Cmd} {state : State} :
    (∀ next, ¬ Step (command, state) next) ↔ command = .skip := by
  constructor
  · intro h
    by_contra hne
    obtain ⟨next, hstep⟩ := exists_step hne
    exact h next hstep
  · rintro rfl
    intro next hstep
    exact skip_not_step hstep

end Step

namespace Steps

theorem single {x y : Config} (h : Step x y) : Steps x y :=
  Relation.ReflTransGen.single h

theorem seq_congr {first first' : Cmd} {second : Cmd} {initial final : State}
    (h : Steps (first, initial) (first', final)) :
    Steps (.seq first second, initial) (.seq first' second, final) := by
  have key : ∀ {x y : Config}, Steps x y →
      Steps (.seq x.1 second, x.2) (.seq y.1 second, y.2) := by
    intro x y hxy
    induction hxy with
    | refl => exact .refl
    | tail _hsteps hstep ih => exact ih.tail (.seqStep hstep)
  exact key h

theorem seq_skip {second : Cmd} {state : State} :
    Steps (.seq .skip second, state) (second, state) :=
  single (.seqSkip second state)

end Steps

namespace Terminates

theorem skip (state : State) : Terminates .skip state state :=
  Relation.ReflTransGen.refl

theorem assign (state : State) (name : Nat) (value : AExp) :
    Terminates (.assign name value) state
      (Function.update state name (value.eval state)) :=
  Steps.single (.assign state name value)

theorem seq {first second : Cmd} {initial middle final : State}
    (h1 : Terminates first initial middle) (h2 : Terminates second middle final) :
    Terminates (.seq first second) initial final :=
  (Steps.seq_congr h1).trans (Steps.seq_skip.trans h2)

end Terminates

end Cslib.IMP
