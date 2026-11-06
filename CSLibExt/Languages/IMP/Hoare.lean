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

/-- **Assertion.** An assertion is a predicate on program states: it assigns a proposition to
each state. Assertions serve as the preconditions and postconditions of Hoare triples. -/
abbrev Assertion := State → Prop

namespace Assertion

/-- **Entailment of assertions.** An assertion $P$ entails an assertion $Q$ when every state
that satisfies $P$ also satisfies $Q$. -/
def Entails (left right : Assertion) : Prop :=
  ∀ ⦃state⦄, left state → right state

theorem entails_refl (assertion : Assertion) : assertion.Entails assertion :=
  fun _ h => h

theorem Entails.trans {first second third : Assertion}
    (hfirst : first.Entails second) (hsecond : second.Entails third) :
    first.Entails third := fun _ h => hsecond (hfirst h)

/-- **Substitution in an assertion.** Let $P$ be an assertion, $x$ a variable and $e$ an
arithmetic expression. The assertion $P[e/x]$ holds in a state $s$ exactly when $P$ holds in
the state obtained from $s$ by setting the value of $x$ to the value of $e$ in $s$. -/
def subst (post : Assertion) (name : Nat) (value : AExp) : Assertion :=
  fun state => post (Function.update state name (value.eval state))

end Assertion

/-- **Validity of a Hoare triple.** For assertions $P$ and $Q$ and a command $c$, the
partial-correctness Hoare triple $\lbrace P \rbrace\ c\ \lbrace Q \rbrace$ is valid when, for all
states $s$ and $t$, if $s$ satisfies $P$ and executing $c$ from $s$ terminates in $t$ under the
big-step semantics, then $t$ satisfies $Q$. -/
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

/-- **Invariant rule for while loops.** Let $I$ be an assertion, $b$ a Boolean expression and
$c$ a command. Write $I \wedge b$ for the assertion that $I$ holds and $b$ evaluates to true,
and $I \wedge \neg b$ for the assertion that $I$ holds and $b$ evaluates to false. If the
partial-correctness Hoare triple $\lbrace I \wedge b \rbrace\ c\ \lbrace I \rbrace$ is valid,
then so is the triple
$\lbrace I \rbrace\ \mathtt{while}\ b\ \mathtt{do}\ c\ \lbrace I \wedge \neg b \rbrace$. -/
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

/-- **Weakest liberal precondition.** For a command $c$ and an assertion $Q$, the weakest
liberal precondition of $c$ with respect to $Q$ is the assertion that holds in a state $s$
exactly when every state $t$ in which an execution of $c$ from $s$ terminates, under the
big-step semantics, satisfies $Q$.

It is liberal because no termination claim is made: a state from which $c$ has no terminating
execution satisfies it for every $Q$. -/
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

/-- **Weakest liberal precondition unfolding of a while loop.** Let $b$ be a Boolean expression,
$c$ a command and $Q$ an assertion. Write $\mathrm{wlp}(d, R)$ for the weakest liberal
precondition of a command $d$ with respect to an assertion $R$, and let $W$ be the loop
$\mathbf{while}\ b\ \mathbf{do}\ c$. Then $\mathrm{wlp}(W, Q)$ is the assertion that holds in a
state $s$ exactly when both of the following hold: if $b$ evaluates to false in $s$, then $Q$
holds in $s$; and if $b$ evaluates to true in $s$, then $\mathrm{wlp}(c, \mathrm{wlp}(W, Q))$
holds in $s$. -/
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

/-- **Loop invariants entail the weakest liberal precondition of the loop.** Let $I$ and $Q$
be assertions, $b$ a Boolean expression and $c$ a command. Suppose that every state satisfying
$I$ in which $b$ evaluates to true satisfies the weakest liberal precondition of $c$ with
respect to $I$, and that every state satisfying $I$ in which $b$ evaluates to false satisfies
$Q$. Then $I$ entails the weakest liberal precondition of the loop
$\mathtt{while}\ b\ \mathtt{do}\ c$ with respect to $Q$. -/
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
