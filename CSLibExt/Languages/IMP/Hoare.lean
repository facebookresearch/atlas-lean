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
# Hoare logic for IMP
-/
module

public import CSLibExt.Languages.IMP.BigStep

/-!
# Partial-correctness Hoare logic

Assertions are predicates on states. `Valid pre command post` states partial
correctness: every terminating execution beginning in `pre` ends in `post`.
The file proves the standard structural rules, the invariant rule for while,
and a semantic weakest-liberal-precondition calculus.
-/

@[expose] public section

namespace Cslib.IMP

/-- State assertions used as Hoare preconditions and postconditions. -/
abbrev Assertion := State → Prop

namespace Assertion

/-- Pointwise implication between assertions. -/
def Entails (left right : Assertion) : Prop :=
  ∀ ⦃state⦄, left state → right state

theorem entails_refl (assertion : Assertion) : assertion.Entails assertion :=
  fun _ h => h

theorem Entails.trans {first second third : Assertion}
    (hfirst : first.Entails second) (hsecond : second.Entails third) :
    first.Entails third := fun _ h => hsecond (hfirst h)

/-- Substitute an arithmetic expression for a variable in an assertion. -/
def subst (post : Assertion) (name : Nat) (value : AExp) : Assertion :=
  fun state => post (Function.update state name (value.eval state))

end Assertion

/-- Semantic validity of a partial-correctness Hoare triple. -/
def Valid (pre : Assertion) (command : Cmd) (post : Assertion) : Prop :=
  ∀ ⦃initial final⦄, pre initial → BigStep command initial final → post final

namespace Valid

theorem skip (assertion : Assertion) : Valid assertion .skip assertion := by
  intro initial final hpre hstep
  rw [BigStep.skip_iff] at hstep
  simpa [hstep] using hpre

theorem assign (post : Assertion) (name : Nat) (value : AExp) :
    Valid (post.subst name value) (.assign name value) post := by
  intro initial final hpre hstep
  rw [BigStep.assign_iff] at hstep
  simpa [Assertion.subst, hstep] using hpre

theorem seq {pre middle post : Assertion} {first second : Cmd}
    (hfirst : Valid pre first middle) (hsecond : Valid middle second post) :
    Valid pre (.seq first second) post := by
  intro initial final hpre hstep
  rw [BigStep.seq_iff] at hstep
  obtain ⟨state, hfirstStep, hsecondStep⟩ := hstep
  exact hsecond (hfirst hpre hfirstStep) hsecondStep

theorem consequence {pre pre' post post' : Assertion} {command : Cmd}
    (hpre : pre.Entails pre') (hvalid : Valid pre' command post')
    (hpost : post'.Entails post) :
    Valid pre command post := by
  intro initial final hinitial hstep
  exact hpost (hvalid (hpre hinitial) hstep)

theorem ite {pre post : Assertion} {guard : BExp} {thenBranch elseBranch : Cmd}
    (hthen : Valid (fun state => pre state ∧ guard.eval state = true) thenBranch post)
    (helse : Valid (fun state => pre state ∧ guard.eval state = false) elseBranch post) :
    Valid pre (.ite guard thenBranch elseBranch) post := by
  intro initial final hpre hstep
  rw [BigStep.ite_iff] at hstep
  rcases hstep with ⟨hguard, hbranch⟩ | ⟨hguard, hbranch⟩
  · exact hthen ⟨hpre, hguard⟩ hbranch
  · exact helse ⟨hpre, hguard⟩ hbranch

/-- The standard invariant rule for partial correctness of while loops. -/
theorem whileLoop {invariant : Assertion} {guard : BExp} {body : Cmd}
    (hbody : Valid (fun state => invariant state ∧ guard.eval state = true)
      body invariant) :
    Valid invariant (.while guard body)
      (fun state => invariant state ∧ guard.eval state = false) := by
  intro initial final hinvariant hloop
  generalize heq : Cmd.while guard body = command at hloop
  induction hloop generalizing guard body with
  | skip => cases heq
  | assign => cases heq
  | seq => cases heq
  | iteTrue => cases heq
  | iteFalse => cases heq
  | whileFalse hguard =>
      cases heq
      exact ⟨hinvariant, hguard⟩
  | whileTrue hguard hbodyStep hloopStep _ ihLoop =>
      cases heq
      have hmiddle := hbody ⟨hinvariant, hguard⟩ hbodyStep
      exact ihLoop hbody hmiddle rfl

end Valid

/-- Semantic weakest liberal precondition. It is liberal because no termination
claim is made: every final state of any terminating execution must satisfy the
postcondition. -/
def wlp (command : Cmd) (post : Assertion) : Assertion :=
  fun initial => ∀ ⦃final⦄, BigStep command initial final → post final

namespace wlp

theorem valid (command : Cmd) (post : Assertion) : Valid (wlp command post) command post :=
  by
    intro initial final hpre hstep
    exact hpre hstep

theorem valid_iff {pre post : Assertion} {command : Cmd} :
    Valid pre command post ↔ pre.Entails (wlp command post) := by
  constructor
  · intro hvalid initial hpre final hstep
    exact hvalid hpre hstep
  · intro hentails initial final hpre hstep
    exact hentails hpre hstep

@[simp]
theorem skip (post : Assertion) : wlp .skip post = post := by
  funext state
  apply propext
  constructor
  · intro h
    exact h (.skip state)
  · intro h final hstep
    rw [BigStep.skip_iff] at hstep
    simpa [hstep] using h

@[simp]
theorem assign (post : Assertion) (name : Nat) (value : AExp) :
    wlp (.assign name value) post = post.subst name value := by
  funext state
  apply propext
  constructor
  · intro h
    exact h (.assign state name value)
  · intro h final hstep
    rw [BigStep.assign_iff] at hstep
    simpa [Assertion.subst, hstep] using h

theorem seq (first second : Cmd) (post : Assertion) :
    wlp (.seq first second) post = wlp first (wlp second post) := by
  funext initial
  apply propext
  constructor
  · intro h middle hfirst final hsecond
    exact h (.seq hfirst hsecond)
  · intro h final hseq
    rw [BigStep.seq_iff] at hseq
    obtain ⟨middle, hfirst, hsecond⟩ := hseq
    exact h hfirst hsecond

theorem ite (guard : BExp) (thenBranch elseBranch : Cmd) (post : Assertion) :
    wlp (.ite guard thenBranch elseBranch) post = fun state =>
      (guard.eval state = true → wlp thenBranch post state) ∧
      (guard.eval state = false → wlp elseBranch post state) := by
  funext initial
  apply propext
  constructor
  · intro h
    constructor
    · intro hguard final hstep
      exact h (.iteTrue hguard hstep)
    · intro hguard final hstep
      exact h (.iteFalse hguard hstep)
  · rintro ⟨hthen, helse⟩ final hstep
    rw [BigStep.ite_iff] at hstep
    rcases hstep with ⟨hguard, hbranch⟩ | ⟨hguard, hbranch⟩
    · exact hthen hguard hbranch
    · exact helse hguard hbranch

/-- Weakest liberal preconditions unfold a while loop into its exit case and
one guarded body iteration followed by the loop again. -/
theorem whileLoop (guard : BExp) (body : Cmd) (post : Assertion) :
    wlp (.while guard body) post = fun state =>
      (guard.eval state = false → post state) ∧
      (guard.eval state = true → wlp body (wlp (.while guard body) post) state) := by
  funext initial
  apply propext
  constructor
  · intro h
    constructor
    · intro hguard
      exact h (.whileFalse hguard)
    · intro hguard middle hbody final hloop
      exact h (.whileTrue hguard hbody hloop)
  · rintro ⟨hexit, hiterate⟩ final hloop
    rw [BigStep.while_iff] at hloop
    rcases hloop with ⟨hguard, rfl⟩ | ⟨hguard, middle, hbody, hrest⟩
    · exact hexit hguard
    · exact hiterate hguard hbody hrest

theorem monotone {firstPost secondPost : Assertion} {command : Cmd}
    (hpost : firstPost.Entails secondPost) :
    (wlp command firstPost).Entails (wlp command secondPost) := by
  intro initial hfirst final hstep
  exact hpost (hfirst hstep)

theorem conjunction (command : Cmd) (firstPost secondPost : Assertion) :
    wlp command (fun state => firstPost state ∧ secondPost state) =
      fun state => wlp command firstPost state ∧ wlp command secondPost state := by
  funext initial
  apply propext
  constructor
  · intro h
    exact ⟨fun _ hstep => (h hstep).1, fun _ hstep => (h hstep).2⟩
  · rintro ⟨hfirst, hsecond⟩ final hstep
    exact ⟨hfirst hstep, hsecond hstep⟩

/-- An invariant is a post-fixed point of the semantic while transformer. -/
theorem invariant_le_while {invariant post : Assertion} {guard : BExp} {body : Cmd}
    (hbody : Assertion.Entails
      (fun state => invariant state ∧ guard.eval state = true) (wlp body invariant))
    (hexit : Assertion.Entails
      (fun state => invariant state ∧ guard.eval state = false) post) :
    invariant.Entails (wlp (.while guard body) post) := by
  intro initial hinvariant final hloop
  have hvalidBody : Valid
      (fun state => invariant state ∧ guard.eval state = true) body invariant :=
    valid_iff.mpr hbody
  have hvalidLoop := Valid.whileLoop hvalidBody
  exact hexit (hvalidLoop hinvariant hloop)

end wlp

end Cslib.IMP
