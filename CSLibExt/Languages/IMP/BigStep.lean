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
# Big-step semantics for IMP
-/
module

public import CSLibExt.Languages.IMP.Syntax

/-!
# Big-step operational semantics

The inductive relation `BigStep command initial final` describes terminating
executions. The central metatheorem proves that this semantics is deterministic,
including the recursive while case.
-/

@[expose] public section

namespace Cslib.IMP

/-- Terminating big-step executions of IMP commands. -/
inductive BigStep : Cmd → State → State → Prop
  | skip (state) : BigStep .skip state state
  | assign (state) (name) (value) :
      BigStep (.assign name value) state (Function.update state name (value.eval state))
  | seq {first second initial middle final}
      (firstStep : BigStep first initial middle)
      (secondStep : BigStep second middle final) :
      BigStep (.seq first second) initial final
  | iteTrue {guard thenBranch elseBranch initial final}
      (guardTrue : guard.eval initial = true)
      (branchStep : BigStep thenBranch initial final) :
      BigStep (.ite guard thenBranch elseBranch) initial final
  | iteFalse {guard thenBranch elseBranch initial final}
      (guardFalse : guard.eval initial = false)
      (branchStep : BigStep elseBranch initial final) :
      BigStep (.ite guard thenBranch elseBranch) initial final
  | whileFalse {guard body state}
      (guardFalse : guard.eval state = false) :
      BigStep (.while guard body) state state
  | whileTrue {guard body initial middle final}
      (guardTrue : guard.eval initial = true)
      (bodyStep : BigStep body initial middle)
      (loopStep : BigStep (.while guard body) middle final) :
      BigStep (.while guard body) initial final

namespace BigStep

@[simp]
theorem skip_iff {initial final : State} :
    BigStep .skip initial final ↔ final = initial := by
  constructor
  · intro h
    cases h
    rfl
  · rintro rfl
    exact .skip _

@[simp]
theorem assign_iff {name : Nat} {value : AExp} {initial final : State} :
    BigStep (.assign name value) initial final ↔
      final = Function.update initial name (value.eval initial) := by
  constructor
  · intro h
    cases h
    rfl
  · rintro rfl
    exact .assign initial name value

theorem seq_iff {first second : Cmd} {initial final : State} :
    BigStep (.seq first second) initial final ↔
      ∃ middle, BigStep first initial middle ∧ BigStep second middle final := by
  constructor
  · intro h
    cases h with
    | seq hfirst hsecond => exact ⟨_, hfirst, hsecond⟩
  · rintro ⟨middle, hfirst, hsecond⟩
    exact .seq hfirst hsecond

theorem ite_iff {guard : BExp} {thenBranch elseBranch : Cmd} {initial final : State} :
    BigStep (.ite guard thenBranch elseBranch) initial final ↔
      (guard.eval initial = true ∧ BigStep thenBranch initial final) ∨
      (guard.eval initial = false ∧ BigStep elseBranch initial final) := by
  constructor
  · intro h
    cases h with
    | iteTrue hg hb => exact Or.inl ⟨hg, hb⟩
    | iteFalse hg hb => exact Or.inr ⟨hg, hb⟩
  · rintro (⟨hg, hb⟩ | ⟨hg, hb⟩)
    · exact .iteTrue hg hb
    · exact .iteFalse hg hb

theorem while_iff {guard : BExp} {body : Cmd} {initial final : State} :
    BigStep (.while guard body) initial final ↔
      (guard.eval initial = false ∧ final = initial) ∨
      (guard.eval initial = true ∧ ∃ middle,
        BigStep body initial middle ∧ BigStep (.while guard body) middle final) := by
  constructor
  · intro h
    cases h with
    | whileFalse hg => exact Or.inl ⟨hg, rfl⟩
    | whileTrue hg hb hl => exact Or.inr ⟨hg, _, hb, hl⟩
  · rintro (⟨hg, rfl⟩ | ⟨hg, middle, hb, hl⟩)
    · exact .whileFalse hg
    · exact .whileTrue hg hb hl

/-- The deterministic IMP big-step semantics has at most one final state. -/
theorem deterministic {command : Cmd} {initial firstFinal secondFinal : State}
    (first : BigStep command initial firstFinal)
    (second : BigStep command initial secondFinal) :
    firstFinal = secondFinal := by
  induction first generalizing secondFinal with
  | skip =>
      rw [skip_iff] at second
      exact second.symm
  | assign =>
      rw [assign_iff] at second
      exact second.symm
  | seq firstStep secondStep ihFirst ihSecond =>
      rw [seq_iff] at second
      obtain ⟨otherMiddle, otherFirst, otherSecond⟩ := second
      have hmiddle := ihFirst otherFirst
      subst otherMiddle
      exact ihSecond otherSecond
  | iteTrue guardTrue branchStep ih =>
      rw [ite_iff] at second
      rcases second with ⟨_, other⟩ | ⟨guardFalse, _⟩
      · exact ih other
      · simp [guardTrue] at guardFalse
  | iteFalse guardFalse branchStep ih =>
      rw [ite_iff] at second
      rcases second with ⟨guardTrue, _⟩ | ⟨_, other⟩
      · simp [guardFalse] at guardTrue
      · exact ih other
  | whileFalse guardFalse =>
      rw [while_iff] at second
      rcases second with ⟨_, hfinal⟩ | ⟨guardTrue, _⟩
      · exact hfinal.symm
      · simp [guardFalse] at guardTrue
  | whileTrue guardTrue bodyStep loopStep ihBody ihLoop =>
      rw [while_iff] at second
      rcases second with ⟨guardFalse, _⟩ | ⟨_, otherMiddle, otherBody, otherLoop⟩
      · simp [guardTrue] at guardFalse
      · have hmiddle := ihBody otherBody
        subst otherMiddle
        exact ihLoop otherLoop

end BigStep

end Cslib.IMP
