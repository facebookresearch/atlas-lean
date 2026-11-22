/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Soundness and relative completeness of Hoare logic for IMP
-/
module

public import CSLibExt.Languages.IMP.HoareTotal
public import CSLibExt.Languages.IMP.Denotational
public import Cslib.Foundations.Logic.InferenceSystem

/-!
# Soundness and relative completeness of Hoare logic for IMP

`Hoare.lean` and `HoareTotal.lean` define semantic validity of Hoare triples
(`Valid`, `TValid`) and prove the proof rules as lemmas about validity. This
file adds the proof systems themselves as inductive derivability relations and
proves that derivability coincides with validity, for partial and for total
correctness.

* `Derivable`: skip, assignment (backwards substitution), sequencing,
  conditional, the invariant rule for `while`, and consequence.
* `TDerivable`: the same rules, with the `while` rule replaced by a variant
  rule: if every guarded body execution from the invariant at variant value
  `n` restores the invariant and drops the variant below `n`, the loop
  terminates.
* `Derivable.sound`, `derivable_wlp`, `Derivable.complete`,
  `derivable_iff_valid`, `derivable_iff_denote`, and the total-correctness
  counterparts `TDerivable.sound`, `tderivable_wp`, `TDerivable.complete`,
  `tderivable_iff_tvalid`, `tderivable_iff_denote`.
* `Triple`, with both systems registered as CSLib inference systems
  (`Cslib.Logic.InferenceSystem`): partial correctness as the default system
  and total correctness under the tag `TotalCorrectness`, following the
  judgement-plus-`HasInferenceSystem` pattern of upstream `Cslib.Logics.HML`.

## Relative completeness

Assertions are semantic predicates on states (`Assertion := State → Prop`),
and the consequence rule takes semantic entailment as a premise. Completeness
is therefore relative in Cook's sense: it holds given an oracle for the
assertion-level entailments, and expressiveness is automatic because the
weakest (liberal) precondition `wlp c Q` / `wp c Q` is itself an assertion.
This is the setting of Nipkow and Klein, *Concrete Semantics* (Springer, 2014),
Chapter 12, which proves soundness and completeness of Hoare logic for partial
and for total correctness with assertions as functions on states, using the
liberal weakest precondition (called `wp` there) and its total counterpart
(`wpt`). The expressiveness of a
first-order syntactic assertion language (Winskel, *The Formal Semantics of
Programming Languages*, Chapter 7, via Gödel's β-function) is not covered here.

The completeness proofs derive `{wlp c Q} c {Q}` and `{wp c Q} c {Q}` by
structural induction on `c`. For a total-correctness loop the variant is
`iterationCount`, the number of body iterations the loop performs before it
exits; `Iterates` counts them and is unique because IMP is deterministic.
-/

@[expose] public section

namespace Cslib.IMP

/-! ## Partial correctness -/

/-- **Derivability in Hoare logic for partial correctness.** Here an assertion is a predicate on
states, and an assertion $P$ entails an assertion $P'$ when every state satisfying $P$ satisfies
$P'$. For an assertion $P$ and a Boolean expression $b$, the assertion $P \land b$ holds in a
state when $P$ holds there and $b$ evaluates to true in it, and the assertion $P \land \lnot b$
holds in a state when $P$ holds there and $b$ evaluates to false in it. Derivability of
partial-correctness Hoare triples $\{P\}\,c\,\{Q\}$ is the least relation closed under the
following rules, where $P$, $P'$, $Q$, $Q'$, $R$ and $I$ are assertions, $c$, $c_1$ and $c_2$ are
commands, $x$ is a variable, $a$ is an arithmetic expression and $b$ is a Boolean expression.

* Skip: $\{Q\}\,\mathtt{skip}\,\{Q\}$.
* Assignment: $\{Q[a/x]\}\,x := a\,\{Q\}$, where $Q[a/x]$ holds in a state $s$ when $Q$ holds in
  the state obtained from $s$ by setting $x$ to the value of $a$ in $s$.
* Sequencing: from $\{P\}\,c_1\,\{R\}$ and $\{R\}\,c_2\,\{Q\}$ derive $\{P\}\,c_1; c_2\,\{Q\}$.
* Conditional: from $\{P \land b\}\,c_1\,\{Q\}$ and $\{P \land \lnot b\}\,c_2\,\{Q\}$ derive
  $\{P\}\,\mathtt{if}\ b\ \mathtt{then}\ c_1\ \mathtt{else}\ c_2\,\{Q\}$.
* While: from $\{I \land b\}\,c\,\{I\}$ derive
  $\{I\}\,\mathtt{while}\ b\ \mathtt{do}\ c\,\{I \land \lnot b\}$.
* Consequence: if $P$ entails $P'$, $\{P'\}\,c\,\{Q'\}$ is derivable and $Q'$ entails $Q$, then
  $\{P\}\,c\,\{Q\}$ is derivable. -/
inductive Derivable : Assertion → Cmd → Assertion → Prop
  | skip (post : Assertion) : Derivable post .skip post
  | assign (post : Assertion) (name : Nat) (value : AExp) :
      Derivable (post.subst name value) (.assign name value) post
  | seq {pre middle post : Assertion} {first second : Cmd}
      (hfirst : Derivable pre first middle) (hsecond : Derivable middle second post) :
      Derivable pre (.seq first second) post
  | ite {pre post : Assertion} {guard : BExp} {thenBranch elseBranch : Cmd}
      (hthen : Derivable (fun state => pre state ∧ guard.eval state = true)
        thenBranch post)
      (helse : Derivable (fun state => pre state ∧ guard.eval state = false)
        elseBranch post) :
      Derivable pre (.ite guard thenBranch elseBranch) post
  | whileLoop {invariant : Assertion} {guard : BExp} {body : Cmd}
      (hbody : Derivable (fun state => invariant state ∧ guard.eval state = true)
        body invariant) :
      Derivable invariant (.while guard body)
        (fun state => invariant state ∧ guard.eval state = false)
  | consequence {pre pre' post post' : Assertion} {command : Cmd}
      (hpre : pre.Entails pre') (hderiv : Derivable pre' command post')
      (hpost : post'.Entails post) :
      Derivable pre command post

namespace Derivable

/-- **Soundness of Hoare logic for partial correctness.** Every partial-correctness Hoare triple
$\{P\}\,c\,\{Q\}$ that is derivable in the partial-correctness proof system is valid: for all
states $s$ and $s'$, if $s$ satisfies $P$ and $c$ has a terminating big-step execution from $s$ to
$s'$, then $s'$ satisfies $Q$. -/
theorem sound {pre post : Assertion} {command : Cmd}
    (h : Derivable pre command post) : Valid pre command post := by
  induction h with
  | skip post => exact Valid.skip post
  | assign post name value => exact Valid.assign post name value
  | seq _ _ ihFirst ihSecond => exact Valid.seq ihFirst ihSecond
  | ite _ _ ihThen ihElse => exact Valid.ite ihThen ihElse
  | whileLoop _ ihBody => exact Valid.whileLoop ihBody
  | consequence hpre _ hpost ih => exact Valid.consequence hpre ih hpost

/-- **Precondition strengthening for partial correctness.** Let $P$, $P'$ and $Q$ be assertions
and $c$ a command. If $P$ entails $P'$ (every state satisfying $P$ satisfies $P'$) and the
partial-correctness triple $\{P'\}\,c\,\{Q\}$ is derivable in the partial-correctness proof
system, then so is $\{P\}\,c\,\{Q\}$. -/
theorem strengthen {pre pre' post : Assertion} {command : Cmd}
    (hpre : pre.Entails pre') (h : Derivable pre' command post) :
    Derivable pre command post :=
  .consequence hpre h (Assertion.entails_refl post)

end Derivable

/-- **The weakest liberal precondition gives a derivable triple.** For every command $c$ and
every assertion $Q$, the triple whose precondition is the weakest liberal precondition of $c$
with respect to $Q$, whose command is $c$ and whose postcondition is $Q$ is derivable in
partial-correctness Hoare logic. -/
theorem derivable_wlp : ∀ (command : Cmd) (post : Assertion),
    Derivable (wlp command post) command post
  | .skip, post => by
      rw [wlp.skip]
      exact .skip post
  | .assign name value, post => by
      rw [wlp.assign]
      exact .assign post name value
  | .seq first second, post => by
      rw [wlp.seq]
      exact .seq (derivable_wlp first _) (derivable_wlp second post)
  | .ite guard thenBranch elseBranch, post => by
      refine .ite (Derivable.strengthen ?_ (derivable_wlp thenBranch post))
        (Derivable.strengthen ?_ (derivable_wlp elseBranch post))
      · rintro state ⟨h, hguard⟩
        rw [wlp.ite] at h
        exact h.1 hguard
      · rintro state ⟨h, hguard⟩
        rw [wlp.ite] at h
        exact h.2 hguard
  | .while guard body, post => by
      have hbody : Derivable
          (fun state => wlp (.while guard body) post state ∧
            guard.eval state = true)
          body (wlp (.while guard body) post) := by
        refine Derivable.strengthen ?_ (derivable_wlp body _)
        rintro state ⟨h, hguard⟩
        rw [wlp.whileLoop] at h
        exact h.2 hguard
      refine .consequence (Assertion.entails_refl _) (.whileLoop hbody) ?_
      rintro state ⟨h, hguard⟩
      rw [wlp.whileLoop] at h
      exact h.1 hguard

namespace Derivable

/-- **Relative completeness of total-correctness Hoare logic.** For all assertions $P$ and $Q$
and every command $c$, if the total-correctness triple with precondition $P$, command $c$ and
postcondition $Q$ is valid, then it is derivable in total-correctness Hoare logic. -/
theorem complete {pre post : Assertion} {command : Cmd}
    (h : Valid pre command post) : Derivable pre command post :=
  strengthen (wlp.valid_iff.mp h) (derivable_wlp command post)

end Derivable

/-- **Partial-correctness Hoare logic as an inference system.** A Hoare triple, given by a
precondition $P$, a command $c$ and a postcondition $Q$, is derivable in the default inference
system on Hoare triples, which is partial-correctness Hoare logic, if and only if it is valid
for partial correctness. -/
theorem derivable_iff_valid {pre post : Assertion} {command : Cmd} :
    Derivable pre command post ↔ Valid pre command post :=
  ⟨Derivable.sound, Derivable.complete⟩

/-- **Partial-correctness Hoare logic matches the denotational semantics.** For all assertions
$P$ and $Q$ and every command $c$, the partial-correctness triple with precondition $P$, command
$c$ and postcondition $Q$ is derivable if and only if, for all states $s$ and $t$ such that $P$
holds at $s$ and the pair $(s, t)$ lies in the relational denotation of $c$, $Q$ holds at $t$. -/
theorem derivable_iff_denote {pre post : Assertion} {command : Cmd} :
    Derivable pre command post ↔
      ∀ ⦃initial final⦄, pre initial → Denote command initial final → post final := by
  rw [derivable_iff_valid]
  constructor
  · intro h initial final hpre hdenote
    exact h hpre (Denote.iff_bigStep.mp hdenote)
  · intro h initial final hpre hstep
    exact h hpre (Denote.iff_bigStep.mpr hstep)

/-! ## Loop iteration counts -/

/-- **Loop runs with a given number of iterations.** Let $b$ be a Boolean expression and $c$ a
command. For a natural number $n$ and states $s$, $s'$, the loop $\mathtt{while}\ b\ \mathtt{do}\ c$
runs from $s$ to $s'$ in $n$ iterations when, started in $s$, it exits in $s'$ after exactly $n$
executions of the body $c$. This is the least relation such that the loop runs from $s$ to $s$ in
$0$ iterations whenever $b$ evaluates to false in $s$, and the loop runs from $s$ to $s'$ in
$n + 1$ iterations whenever $b$ evaluates to true in $s$, the body $c$ has a terminating big-step
execution from $s$ to some state $t$, and the loop runs from $t$ to $s'$ in $n$ iterations. -/
inductive Iterates (guard : BExp) (body : Cmd) : Nat → State → State → Prop
  | exit {state : State} (hguard : guard.eval state = false) :
      Iterates guard body 0 state state
  | step {n : Nat} {initial middle final : State}
      (hguard : guard.eval initial = true) (hbody : BigStep body initial middle)
      (hrest : Iterates guard body n middle final) :
      Iterates guard body (n + 1) initial final

namespace Iterates

variable {guard : BExp} {body : Cmd}

/-- **Counted loop runs are big-step executions.** Let $b$ be a boolean expression, $c$ a
command, $n$ a natural number and $s$, $t$ states. If the loop
$\mathtt{while}\ b\ \mathtt{do}\ c$, started in $s$, exits in $t$ after exactly $n$
executions of the body $c$, then the loop $\mathtt{while}\ b\ \mathtt{do}\ c$ runs from $s$
to $t$ in the big-step semantics. -/
theorem bigStep {n : Nat} {initial final : State}
    (h : Iterates guard body n initial final) :
    BigStep (.while guard body) initial final := by
  induction h with
  | exit hguard => exact .whileFalse hguard
  | step hguard hbody _ ih => exact .whileTrue hguard hbody ih

/-- **Every terminating loop run has an iteration count.** Let $b$ be a Boolean expression, $c$ a
command and $s$, $s'$ states. If the loop $\mathtt{while}\ b\ \mathtt{do}\ c$ has a terminating
big-step execution from $s$ to $s'$, then there is a natural number $n$ such that the loop,
started in $s$, exits in $s'$ after exactly $n$ executions of the body $c$. -/
theorem exists_of_bigStep {initial final : State}
    (h : BigStep (.while guard body) initial final) :
    ∃ n, Iterates guard body n initial final := by
  generalize heq : Cmd.while guard body = command at h
  induction h generalizing guard body with
  | skip => cases heq
  | assign => cases heq
  | seq => cases heq
  | iteTrue => cases heq
  | iteFalse => cases heq
  | whileFalse hguard =>
      cases heq
      exact ⟨0, .exit hguard⟩
  | whileTrue hguard hbody _ _ ihLoop =>
      cases heq
      obtain ⟨n, hn⟩ := ihLoop rfl
      exact ⟨n + 1, .step hguard hbody hn⟩

/-- **Uniqueness of the loop iteration count.** Let $b$ be a boolean expression, $c$ a command
and $s$ a state. If the loop $\mathtt{while}\ b\ \mathtt{do}\ c$, started in $s$, exits in
a state $t$ after exactly $n$ executions of the body and also exits in a state $t'$ after
exactly $m$ executions of the body, then $n = m$. -/
theorem count_unique {n m : Nat} {initial first second : State}
    (hfirst : Iterates guard body n initial first)
    (hsecond : Iterates guard body m initial second) : n = m := by
  induction hfirst generalizing m second with
  | exit hguard =>
      cases hsecond with
      | exit => rfl
      | step hguard' => simp [hguard] at hguard'
  | step hguard hbody _ ih =>
      cases hsecond with
      | exit hguard' => simp [hguard] at hguard'
      | step _ hbody' hrest' =>
          have hmiddle := BigStep.deterministic hbody hbody'
          subst hmiddle
          rw [ih hrest']

end Iterates

open scoped Classical in
/-- **Loop iteration count.** Let $b$ be a Boolean expression, $c$ a command and $s$ a state. If
there are a natural number $n$ and a state $s'$ such that the loop
$\mathtt{while}\ b\ \mathtt{do}\ c$, started in $s$, exits in $s'$ after exactly $n$ executions of
the body $c$, then the iteration count of the loop from $s$ is such an $n$; otherwise it is $0$.

Such an $n$ is unique because IMP is deterministic, so the iteration count is the number of body
executions the loop performs from $s$ before exiting. -/
noncomputable def iterationCount (guard : BExp) (body : Cmd) (state : State) : Nat :=
  if h : ∃ n final, Iterates guard body n state final then Classical.choose h else 0

/-- **The iteration count of a terminating loop run.** Let $b$ be a Boolean expression, $c$ a
command, $n$ a natural number and $s$, $s'$ states. If the loop $\mathtt{while}\ b\ \mathtt{do}\ c$,
started in $s$, exits in $s'$ after exactly $n$ executions of the body $c$, then the iteration
count of the loop from $s$ is $n$. -/
theorem Iterates.iterationCount_eq {guard : BExp} {body : Cmd} {n : Nat}
    {initial final : State} (h : Iterates guard body n initial final) :
    iterationCount guard body initial = n := by
  have hex : ∃ n final, Iterates guard body n initial final := ⟨n, final, h⟩
  unfold iterationCount
  split
  · rename_i hex
    obtain ⟨_, hchosen⟩ := Classical.choose_spec hex
    exact hchosen.count_unique h
  · contradiction

/-- **The iteration count of a nonterminating loop is zero.** Let $b$ be a Boolean expression, $c$ a
command and $s$ a state. If the loop $\mathtt{while}\ b\ \mathtt{do}\ c$ has no terminating
big-step execution from $s$ to any state, then the iteration count of the loop from $s$ is
$0$. -/
theorem iterationCount_eq_zero {guard : BExp} {body : Cmd} {state : State}
    (h : ∀ final, ¬ BigStep (.while guard body) state final) :
    iterationCount guard body state = 0 := by
  unfold iterationCount
  split
  · rename_i hex
    obtain ⟨_, final, hn⟩ := hex
    exact absurd hn.bigStep (h final)
  · rfl

/-! ## Total correctness -/

/-- **Total-correctness Hoare logic.** Derivability of total-correctness Hoare triples
$\{P\}\,c\,\{Q\}$, for assertions $P$, $Q$ (predicates on states) and IMP commands $c$, is the
least relation closed under the following rules. In an assertion, $b$ for a boolean expression
means that $b$ evaluates to true and $\neg b$ that it evaluates to false. Skip:
$\{Q\}\,\mathtt{skip}\,\{Q\}$. Assignment: for a variable $x$ and an arithmetic expression $a$,
$\{Q[a/x]\}\,x := a\,\{Q\}$, where $Q[a/x]$ holds in a state $s$ iff $Q$ holds in $s$ updated at
$x$ to the value of $a$ in $s$. Sequencing: from $\{P\}\,c_1\,\{R\}$ and $\{R\}\,c_2\,\{Q\}$
derive $\{P\}\,c_1; c_2\,\{Q\}$. Conditional: from $\{P \wedge b\}\,c_1\,\{Q\}$ and
$\{P \wedge \neg b\}\,c_2\,\{Q\}$ derive
$\{P\}\,\mathtt{if}\ b\ \mathtt{then}\ c_1\ \mathtt{else}\ c_2\,\{Q\}$. Loop (variant rule): for an
assertion $I$ and a map $V$ from states to natural numbers, if for every natural number $n$ the
triple $\{I \wedge b \wedge V = n\}\,c\,\{I \wedge V < n\}$ is derivable, derive
$\{I\}\,\mathtt{while}\ b\ \mathtt{do}\ c\,\{I \wedge \neg b\}$. Consequence: if $P$ entails $P'$,
$\{P'\}\,c\,\{Q'\}$ is derivable and $Q'$ entails $Q$, derive $\{P\}\,c\,\{Q\}$, where entailment
is pointwise implication. -/
inductive TDerivable : Assertion → Cmd → Assertion → Prop
  | skip (post : Assertion) : TDerivable post .skip post
  | assign (post : Assertion) (name : Nat) (value : AExp) :
      TDerivable (post.subst name value) (.assign name value) post
  | seq {pre middle post : Assertion} {first second : Cmd}
      (hfirst : TDerivable pre first middle) (hsecond : TDerivable middle second post) :
      TDerivable pre (.seq first second) post
  | ite {pre post : Assertion} {guard : BExp} {thenBranch elseBranch : Cmd}
      (hthen : TDerivable (fun state => pre state ∧ guard.eval state = true)
        thenBranch post)
      (helse : TDerivable (fun state => pre state ∧ guard.eval state = false)
        elseBranch post) :
      TDerivable pre (.ite guard thenBranch elseBranch) post
  | whileVariant {invariant : Assertion} {variant : State → Nat} {guard : BExp}
      {body : Cmd}
      (hbody : ∀ n : Nat, TDerivable
        (fun state => invariant state ∧ guard.eval state = true ∧ variant state = n)
        body (fun state => invariant state ∧ variant state < n)) :
      TDerivable invariant (.while guard body)
        (fun state => invariant state ∧ guard.eval state = false)
  | consequence {pre pre' post post' : Assertion} {command : Cmd}
      (hpre : pre.Entails pre') (hderiv : TDerivable pre' command post')
      (hpost : post'.Entails post) :
      TDerivable pre command post

namespace TDerivable

/-- **Soundness of total-correctness Hoare logic.** For all assertions $P$ and $Q$ and every
command $c$, if the triple $\{P\}\,c\,\{Q\}$ is derivable in total-correctness Hoare logic, then
it is valid for total correctness: every state satisfying $P$ has a terminating big-step
execution of $c$ ending in a state that satisfies $Q$. -/
theorem sound {pre post : Assertion} {command : Cmd}
    (h : TDerivable pre command post) : TValid pre command post := by
  induction h with
  | skip post => exact TValid.skip post
  | assign post name value => exact TValid.assign post name value
  | seq _ _ ihFirst ihSecond => exact TValid.seq ihFirst ihSecond
  | ite _ _ ihThen ihElse => exact TValid.ite ihThen ihElse
  | @whileVariant invariant variant guard body _ ihBody =>
      refine TValid.whileVariant (variant := variant) ?_
      intro state hinvariant hguard
      obtain ⟨final, hstep, hinvariant', hlt⟩ :=
        ihBody (variant state) ⟨hinvariant, hguard, rfl⟩
      exact ⟨final, hstep, hinvariant', hlt⟩
  | consequence hpre _ hpost ih => exact TValid.consequence hpre ih hpost

/-- **Precondition strengthening for total correctness.** Let $P$, $P'$ and $Q$ be assertions and
$c$ a command. If $P$ entails $P'$ (every state satisfying $P$ satisfies $P'$) and the triple
$\{P'\}\,c\,\{Q\}$ is derivable in total-correctness Hoare logic, then so is
$\{P\}\,c\,\{Q\}$. -/
theorem strengthen {pre pre' post : Assertion} {command : Cmd}
    (hpre : pre.Entails pre') (h : TDerivable pre' command post) :
    TDerivable pre command post :=
  .consequence hpre h (Assertion.entails_refl post)

end TDerivable

/-- **The weakest-precondition triple is derivable in total-correctness Hoare logic.** For every
IMP command $c$ and every assertion $Q$ (a predicate on states), the triple
$\{\mathrm{wp}(c, Q)\}\,c\,\{Q\}$ is derivable in the total-correctness Hoare logic. Here
$\mathrm{wp}(c, Q)$ is the semantic weakest precondition: it holds in a state $s$ exactly when
there is a terminating execution of $c$ from $s$ ending in a state satisfying $Q$. -/
theorem tderivable_wp : ∀ (command : Cmd) (post : Assertion),
    TDerivable (wp command post) command post
  | .skip, post => by
      rw [wp.skip]
      exact .skip post
  | .assign name value, post => by
      rw [wp.assign]
      exact .assign post name value
  | .seq first second, post => by
      rw [wp.seq]
      exact .seq (tderivable_wp first _) (tderivable_wp second post)
  | .ite guard thenBranch elseBranch, post => by
      refine .ite (TDerivable.strengthen ?_ (tderivable_wp thenBranch post))
        (TDerivable.strengthen ?_ (tderivable_wp elseBranch post))
      · rintro state ⟨h, hguard⟩
        rw [wp.ite] at h
        exact h.1 hguard
      · rintro state ⟨h, hguard⟩
        rw [wp.ite] at h
        exact h.2 hguard
  | .while guard body, post => by
      have hbody : ∀ n : Nat, TDerivable
          (fun state => wp (.while guard body) post state ∧
            guard.eval state = true ∧ iterationCount guard body state = n)
          body
          (fun state => wp (.while guard body) post state ∧
            iterationCount guard body state < n) := by
        intro n
        refine TDerivable.strengthen ?_ (tderivable_wp body _)
        rintro state ⟨⟨final, hloop, hpost⟩, hguard, rfl⟩
        obtain ⟨k, hk⟩ := Iterates.exists_of_bigStep hloop
        cases hk with
        | exit hguard' => simp [hguard] at hguard'
        | step hguard' hbodyStep hrest =>
            refine ⟨_, hbodyStep, ⟨final, hrest.bigStep, hpost⟩, ?_⟩
            rw [hrest.iterationCount_eq,
              (Iterates.step hguard' hbodyStep hrest).iterationCount_eq]
            exact Nat.lt_succ_self _
      refine .consequence (Assertion.entails_refl _) (.whileVariant hbody) ?_
      rintro state ⟨⟨final, hloop, hpost⟩, hguard⟩
      rw [BigStep.while_iff] at hloop
      rcases hloop with ⟨_, rfl⟩ | ⟨hguard', _⟩
      · exact hpost
      · simp [hguard] at hguard'

namespace TDerivable

/-- **Total-correctness Hoare logic is relatively complete.** For all assertions $P$ and $Q$ and
every command $c$, if the total-correctness Hoare triple $\{P\}\,c\,\{Q\}$ is valid, then it is
derivable in total-correctness Hoare logic. -/
theorem complete {pre post : Assertion} {command : Cmd}
    (h : TValid pre command post) : TDerivable pre command post :=
  strengthen (wp.tvalid_iff.mp h) (tderivable_wp command post)

/-- **Total-correctness derivations give partial-correctness derivations.** For all assertions
$P$ and $Q$ and every command $c$, if the triple with precondition $P$, command $c$ and
postcondition $Q$ is derivable in total-correctness Hoare logic, then it is derivable in
partial-correctness Hoare logic. -/
theorem derivable {pre post : Assertion} {command : Cmd}
    (h : TDerivable pre command post) : Derivable pre command post :=
  Derivable.complete h.sound.valid

end TDerivable

/-- **Soundness and relative completeness of total-correctness Hoare logic.** For all assertions
$P$, $Q$ (predicates on states) and every IMP command $c$, the triple $\{P\}\,c\,\{Q\}$ is
derivable in the total-correctness Hoare logic if and only if it is totally valid. -/
theorem tderivable_iff_tvalid {pre post : Assertion} {command : Cmd} :
    TDerivable pre command post ↔ TValid pre command post :=
  ⟨TDerivable.sound, TDerivable.complete⟩

/-- **Total-correctness Hoare logic is sound and complete for the denotational semantics.** For
all assertions $P$, $Q$ (predicates on states) and every IMP command $c$, the triple
$\{P\}\,c\,\{Q\}$ is derivable in the total-correctness Hoare logic if and only if for every
state $s$ satisfying $P$ there is a state $s'$ such that $(s, s')$ lies in the relational
denotation of $c$ and $s'$ satisfies $Q$. -/
theorem tderivable_iff_denote {pre post : Assertion} {command : Cmd} :
    TDerivable pre command post ↔
      ∀ ⦃initial⦄, pre initial → ∃ final, Denote command initial final ∧ post final := by
  rw [tderivable_iff_tvalid]
  constructor
  · intro h initial hpre
    obtain ⟨final, hstep, hpost⟩ := h hpre
    exact ⟨final, Denote.iff_bigStep.mpr hstep, hpost⟩
  · intro h initial hpre
    obtain ⟨final, hdenote, hpost⟩ := h hpre
    exact ⟨final, Denote.iff_bigStep.mp hdenote, hpost⟩

/-! ## Hoare triples as CSLib inference systems -/

/-- **Hoare triples.** A Hoare triple $\{P\}\,c\,\{Q\}$ consists of a precondition $P$ and a
postcondition $Q$, both assertions (predicates on states), and an IMP command $c$. It is the
judgement form of both the partial-correctness and the total-correctness Hoare logic. -/
structure Triple where
  /-- The precondition. -/
  pre : Assertion
  /-- The command. -/
  command : Cmd
  /-- The postcondition. -/
  post : Assertion

/-- **Total-correctness tag for Hoare triples.** An empty type used only as a label: derivability
of Hoare triples in the total-correctness Hoare logic is registered as an inference system under
this tag, while partial-correctness derivability is the default inference system on Hoare
triples. -/
inductive TotalCorrectness : Type

/-- Partial-correctness derivability is the default inference system on Hoare
triples. -/
instance : Cslib.Logic.HasInferenceSystem Triple :=
  ⟨fun t => Derivable t.pre t.command t.post⟩

/-- Total-correctness derivability, under the tag `TotalCorrectness`. -/
instance : Cslib.Logic.InferenceSystem TotalCorrectness Triple :=
  ⟨fun t => TDerivable t.pre t.command t.post⟩

namespace Triple

/-- **Derivability in the default inference system on Hoare triples is validity.** For every
Hoare triple $\{P\}\,c\,\{Q\}$, the triple is derivable in the default inference system on Hoare
triples, which is partial-correctness Hoare logic, if and only if it is valid for partial
correctness. -/
theorem derivable_iff_valid (t : Triple) :
    Cslib.Logic.InferenceSystem.Derivable t ↔ Valid t.pre t.command t.post :=
  nonempty_prop.trans IMP.derivable_iff_valid

/-- **Total-correctness Hoare logic as an inference system.** A Hoare triple, given by a
precondition $P$, a command $c$ and a postcondition $Q$, is derivable in the inference system on
Hoare triples tagged total correctness, which is total-correctness Hoare logic, if and only if
it is valid for total correctness. -/
theorem derivableIn_totalCorrectness_iff_tvalid (t : Triple) :
    Cslib.Logic.InferenceSystem.DerivableIn TotalCorrectness t ↔
      TValid t.pre t.command t.post :=
  nonempty_prop.trans IMP.tderivable_iff_tvalid

end Triple

end Cslib.IMP
