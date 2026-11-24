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

/-- **Validity of total-correctness Hoare triples.** For assertions $P$ and $Q$ on states and a
command $c$, the total-correctness Hoare triple with precondition $P$, command $c$ and
postcondition $Q$ is valid when every state $s$ satisfying $P$ has a terminating big-step
execution of $c$ from $s$ ending in a state $t$ that satisfies $Q$. -/
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

/-- **Variant rule for while loops.** Let $I$ be an assertion (the invariant), $V$ a function
from states to natural numbers (the variant), $b$ a Boolean guard and $c$ a command. Suppose
that for every state $s$ satisfying $I$ in which $b$ evaluates to true, there is a terminating
big-step execution of $c$ from $s$ ending in a state $s'$ that satisfies $I$ with
$V(s') < V(s)$. Then the total-correctness Hoare triple with precondition $I$, command
$\mathtt{while}\ b\ \mathtt{do}\ c$ and postcondition "$I$ holds and $b$ evaluates to false"
is valid. -/
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

/-- **Total correctness implies partial correctness.** For assertions $P$, $Q$ and a command
$c$, if the total-correctness Hoare triple with precondition $P$, command $c$ and
postcondition $Q$ is valid, then the partial-correctness Hoare triple with the same
precondition, command and postcondition is valid. -/
theorem valid {pre post : Assertion} {command : Cmd}
    (htotal : TValid pre command post) : Valid pre command post := by
  intro initial final hpre hstep
  obtain ⟨final', hstep', hpost⟩ := htotal hpre
  rw [BigStep.deterministic hstep hstep']
  exact hpost

/-- **Total correctness gives a terminating small-step run.** If the total-correctness Hoare
triple with precondition $P$, command $c$ and postcondition $Q$ is valid and a state $s$
satisfies $P$, then there is a state $t$ such that $c$, started in $s$, reaches
$\mathtt{skip}$ with state $t$ in finitely many small steps, and $t$ satisfies $Q$. -/
theorem terminates {pre post : Assertion} {command : Cmd}
    (htotal : TValid pre command post) {state : State} (hpre : pre state) :
    ∃ final, Terminates command state final ∧ post final := by
  obtain ⟨final, hstep, hpost⟩ := htotal hpre
  exact ⟨final, terminates_iff_bigStep.mpr hstep, hpost⟩

end TValid

/-- **Weakest precondition for total correctness.** For a command $c$ and a postcondition $Q$,
the weakest precondition $\mathrm{wp}(c, Q)$ is the assertion that holds at a state $s$ exactly
when there is a terminating big-step execution of $c$ from $s$ ending in a state that satisfies
$Q$. -/
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

/-- **Weakest-precondition unfolding of a while loop.** For a Boolean guard $b$, a loop body
$c$, a postcondition $Q$ and a state $s$, the state $s$ satisfies the total-correctness weakest
precondition $\mathrm{wp}(\mathtt{while}\ b\ \mathtt{do}\ c, Q)$ if and only if either $b$
evaluates to false in $s$ and $s$ satisfies $Q$, or $b$ evaluates to true in $s$ and $s$
satisfies $\mathrm{wp}(c, \mathrm{wp}(\mathtt{while}\ b\ \mathtt{do}\ c, Q))$. -/
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

/-- **Total-correctness weakest precondition implies the weakest liberal precondition.** For
every command $c$, postcondition $Q$ and state $s$, if $s$ satisfies the total-correctness
weakest precondition $\mathrm{wp}(c, Q)$, then $s$ satisfies the weakest liberal precondition
$\mathrm{wlp}(c, Q)$. -/
theorem le_wlp {command : Cmd} {post : Assertion} {state : State}
    (hwp : wp command post state) : wlp command post state := by
  obtain ⟨final, hstep, hpost⟩ := hwp
  intro otherFinal hotherStep
  rw [BigStep.deterministic hotherStep hstep]
  exact hpost

end wp

end Cslib.IMP
