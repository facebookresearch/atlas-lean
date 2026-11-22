/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Total-correctness Hoare logic for IMP
-/
module

public import CSLibExt.Languages.IMP.Hoare
public import CSLibExt.Languages.IMP.Equivalence

/-!
# Total-correctness Hoare logic and weakest preconditions

`TValid pre command post` strengthens `Valid` with termination: every
initial state satisfying `pre` has a terminating execution ending in `post`.
The file proves the standard structural rules, a variant rule for while
loops, and Dijkstra's semantic weakest precondition `wp`.
-/

@[expose] public section

namespace Cslib.IMP

/-- Semantic validity of a total-correctness Hoare triple: every initial
state satisfying the precondition has a terminating execution ending in the
postcondition. -/
def TValid (pre : Assertion) (command : Cmd) (post : Assertion) : Prop :=
  ∀ ⦃s : State⦄, pre s → ∃ s', BigStep command s s' ∧ post s'

namespace TValid

theorem skip (assertion : Assertion) : TValid assertion .skip assertion := by
  intro state hpre
  exact ⟨state, .skip state, hpre⟩

theorem assign (post : Assertion) (name : Nat) (value : AExp) :
    TValid (post.subst name value) (.assign name value) post := by
  intro state hpre
  exact ⟨Function.update state name (value.eval state),
    .assign state name value, hpre⟩

theorem seq {pre middle post : Assertion} {first second : Cmd}
    (hfirst : TValid pre first middle) (hsecond : TValid middle second post) :
    TValid pre (.seq first second) post := by
  intro initial hpre
  obtain ⟨state, hfirstStep, hmiddle⟩ := hfirst hpre
  obtain ⟨final, hsecondStep, hpost⟩ := hsecond hmiddle
  exact ⟨final, .seq hfirstStep hsecondStep, hpost⟩

theorem consequence {pre pre' post post' : Assertion} {command : Cmd}
    (hpre : pre.Entails pre') (hvalid : TValid pre' command post')
    (hpost : post'.Entails post) :
    TValid pre command post := by
  intro initial hinitial
  obtain ⟨final, hstep, hfinal⟩ := hvalid (hpre hinitial)
  exact ⟨final, hstep, hpost hfinal⟩

theorem ite {pre post : Assertion} {guard : BExp} {thenBranch elseBranch : Cmd}
    (hthen : TValid (fun state => pre state ∧ guard.eval state = true)
      thenBranch post)
    (helse : TValid (fun state => pre state ∧ guard.eval state = false)
      elseBranch post) :
    TValid pre (.ite guard thenBranch elseBranch) post := by
  intro initial hpre
  by_cases hguardTrue : guard.eval initial = true
  · obtain ⟨final, hstep, hpost⟩ := hthen ⟨hpre, hguardTrue⟩
    exact ⟨final, .iteTrue hguardTrue hstep, hpost⟩
  · have hguardFalse : guard.eval initial = false := by
      cases h : guard.eval initial with
      | false => rfl
      | true => exact absurd h hguardTrue
    obtain ⟨final, hstep, hpost⟩ := helse ⟨hpre, hguardFalse⟩
    exact ⟨final, .iteFalse hguardFalse hstep, hpost⟩

/-- The variant rule for total correctness of while loops: if every guarded
body execution from the invariant terminates, restores the invariant, and
strictly decreases the variant, then the loop terminates in a state
satisfying the invariant with the guard false. -/
theorem whileVariant {invariant : Assertion} {variant : State → Nat}
    {guard : BExp} {body : Cmd}
    (hbody : ∀ s, invariant s → guard.eval s = true →
      ∃ s', BigStep body s s' ∧ invariant s' ∧ variant s' < variant s) :
    TValid invariant (.while guard body)
      (fun s => invariant s ∧ guard.eval s = false) := by
  intro initial hinvariant
  have key : ∀ n state, invariant state → variant state = n →
      ∃ final, BigStep (.while guard body) state final ∧
        invariant final ∧ guard.eval final = false := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro state hinvariant hvariant
      by_cases hguardFalse : guard.eval state = false
      · exact ⟨state, .whileFalse hguardFalse, hinvariant, hguardFalse⟩
      · have hguardTrue : guard.eval state = true := by
          cases h : guard.eval state with
          | false => exact absurd h hguardFalse
          | true => rfl
        obtain ⟨state', hbodyStep, hinvariant', hdecrease⟩ :=
          hbody state hinvariant hguardTrue
        obtain ⟨final, hloopStep, hinvariantFinal, hguardFinal⟩ :=
          ih (variant state') (by rw [← hvariant]; exact hdecrease)
            state' hinvariant' rfl
        exact ⟨final, .whileTrue hguardTrue hbodyStep hloopStep,
          hinvariantFinal, hguardFinal⟩
  obtain ⟨final, hstep, hinvariantFinal, hguardFinal⟩ :=
    key (variant initial) initial hinvariant rfl
  exact ⟨final, hstep, hinvariantFinal, hguardFinal⟩

/-- Total correctness implies partial correctness. -/
theorem valid {pre post : Assertion} {command : Cmd}
    (htotal : TValid pre command post) : Valid pre command post := by
  intro initial final hpre hstep
  obtain ⟨final', hstep', hpost⟩ := htotal hpre
  rw [BigStep.deterministic hstep hstep']
  exact hpost

/-- Total correctness yields a terminating small-step execution. -/
theorem terminates {pre post : Assertion} {command : Cmd}
    (htotal : TValid pre command post) {state : State} (hpre : pre state) :
    ∃ final, Terminates command state final ∧ post final := by
  obtain ⟨final, hstep, hpost⟩ := htotal hpre
  exact ⟨final, terminates_iff_bigStep.mpr hstep, hpost⟩

end TValid

/-- Semantic weakest precondition for total correctness. -/
def wp (command : Cmd) (post : Assertion) : Assertion :=
  fun s => ∃ s', BigStep command s s' ∧ post s'

namespace wp

theorem sound (command : Cmd) (post : Assertion) :
    TValid (wp command post) command post := by
  intro state hpre
  exact hpre

theorem weakest {pre post : Assertion} {command : Cmd}
    (htotal : TValid pre command post) : pre.Entails (wp command post) := by
  intro state hpre
  exact htotal hpre

theorem tvalid_iff {pre post : Assertion} {command : Cmd} :
    TValid pre command post ↔ pre.Entails (wp command post) := by
  constructor
  · exact fun htotal => weakest htotal
  · intro hentails
    exact TValid.consequence hentails (sound command post)
      (Assertion.entails_refl post)

@[simp]
theorem skip (post : Assertion) : wp .skip post = post := by
  funext state
  apply propext
  constructor
  · rintro ⟨final, hstep, hpost⟩
    rw [BigStep.skip_iff] at hstep
    simpa [hstep] using hpost
  · intro hpost
    exact ⟨state, .skip state, hpost⟩

@[simp]
theorem assign (post : Assertion) (name : Nat) (value : AExp) :
    wp (.assign name value) post = post.subst name value := by
  funext state
  apply propext
  constructor
  · rintro ⟨final, hstep, hpost⟩
    rw [BigStep.assign_iff] at hstep
    simpa [Assertion.subst, hstep] using hpost
  · intro hpre
    exact ⟨Function.update state name (value.eval state),
      .assign state name value, hpre⟩

theorem seq (first second : Cmd) (post : Assertion) :
    wp (.seq first second) post = wp first (wp second post) := by
  funext initial
  apply propext
  constructor
  · rintro ⟨final, hstep, hpost⟩
    rw [BigStep.seq_iff] at hstep
    obtain ⟨middle, hfirstStep, hsecondStep⟩ := hstep
    exact ⟨middle, hfirstStep, final, hsecondStep, hpost⟩
  · rintro ⟨middle, hfirstStep, final, hsecondStep, hpost⟩
    exact ⟨final, .seq hfirstStep hsecondStep, hpost⟩

theorem ite (guard : BExp) (thenBranch elseBranch : Cmd) (post : Assertion) :
    wp (.ite guard thenBranch elseBranch) post = fun state =>
      (guard.eval state = true → wp thenBranch post state) ∧
      (guard.eval state = false → wp elseBranch post state) := by
  funext initial
  apply propext
  constructor
  · rintro ⟨final, hstep, hpost⟩
    rw [BigStep.ite_iff] at hstep
    rcases hstep with ⟨hguard, hbranch⟩ | ⟨hguard, hbranch⟩
    · refine ⟨fun _ => ⟨final, hbranch, hpost⟩, fun hfalse => ?_⟩
      simp [hguard] at hfalse
    · refine ⟨fun htrue => ?_, fun _ => ⟨final, hbranch, hpost⟩⟩
      simp [hguard] at htrue
  · rintro ⟨hthen, helse⟩
    by_cases hguardTrue : guard.eval initial = true
    · obtain ⟨final, hstep, hpost⟩ := hthen hguardTrue
      exact ⟨final, .iteTrue hguardTrue hstep, hpost⟩
    · have hguardFalse : guard.eval initial = false := by
        cases h : guard.eval initial with
        | false => rfl
        | true => exact absurd h hguardTrue
      obtain ⟨final, hstep, hpost⟩ := helse hguardFalse
      exact ⟨final, .iteFalse hguardFalse hstep, hpost⟩

/-- Weakest preconditions unfold a while loop into its exit case and one
guarded body iteration followed by the loop again. -/
theorem while_iff {guard : BExp} {body : Cmd} {post : Assertion}
    {state : State} :
    wp (.while guard body) post state ↔
      (guard.eval state = false ∧ post state) ∨
      (guard.eval state = true ∧
        wp body (wp (.while guard body) post) state) := by
  constructor
  · rintro ⟨final, hstep, hpost⟩
    rw [BigStep.while_iff] at hstep
    rcases hstep with ⟨hguard, rfl⟩ | ⟨hguard, middle, hbodyStep, hloopStep⟩
    · exact Or.inl ⟨hguard, hpost⟩
    · exact Or.inr ⟨hguard, middle, hbodyStep, final, hloopStep, hpost⟩
  · rintro (⟨hguard, hpost⟩ |
      ⟨hguard, middle, hbodyStep, final, hloopStep, hpost⟩)
    · exact ⟨state, .whileFalse hguard, hpost⟩
    · exact ⟨final, .whileTrue hguard hbodyStep hloopStep, hpost⟩

theorem monotone {firstPost secondPost : Assertion} {command : Cmd}
    (hpost : firstPost.Entails secondPost) :
    (wp command firstPost).Entails (wp command secondPost) := by
  intro initial hfirst
  obtain ⟨final, hstep, hfinal⟩ := hfirst
  exact ⟨final, hstep, hpost hfinal⟩

/-- The weakest precondition strengthens the weakest liberal precondition. -/
theorem le_wlp {command : Cmd} {post : Assertion} {state : State}
    (hwp : wp command post state) : wlp command post state := by
  obtain ⟨final, hstep, hpost⟩ := hwp
  intro otherFinal hotherStep
  rw [BigStep.deterministic hotherStep hstep]
  exact hpost

end wp

end Cslib.IMP
