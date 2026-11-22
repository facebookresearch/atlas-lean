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

/-- Derivable partial-correctness Hoare triples. The consequence rule takes
semantic entailments between assertions as premises. -/
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

/-- Soundness: every derivable triple is valid. -/
theorem sound {pre post : Assertion} {command : Cmd}
    (h : Derivable pre command post) : Valid pre command post := by
  induction h with
  | skip post => exact Valid.skip post
  | assign post name value => exact Valid.assign post name value
  | seq _ _ ihFirst ihSecond => exact Valid.seq ihFirst ihSecond
  | ite _ _ ihThen ihElse => exact Valid.ite ihThen ihElse
  | whileLoop _ ihBody => exact Valid.whileLoop ihBody
  | consequence hpre _ hpost ih => exact Valid.consequence hpre ih hpost

/-- Strengthen the precondition of a derivable triple. -/
theorem strengthen {pre pre' post : Assertion} {command : Cmd}
    (hpre : pre.Entails pre') (h : Derivable pre' command post) :
    Derivable pre command post :=
  .consequence hpre h (Assertion.entails_refl post)

end Derivable

/-- The weakest liberal precondition is derivable for every command and
postcondition. -/
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

/-- Relative completeness: every valid partial-correctness triple is
derivable. -/
theorem complete {pre post : Assertion} {command : Cmd}
    (h : Valid pre command post) : Derivable pre command post :=
  strengthen (wlp.valid_iff.mp h) (derivable_wlp command post)

end Derivable

/-- Partial-correctness derivability coincides with validity. -/
theorem derivable_iff_valid {pre post : Assertion} {command : Cmd} :
    Derivable pre command post ↔ Valid pre command post :=
  ⟨Derivable.sound, Derivable.complete⟩

/-- Partial-correctness derivability coincides with validity with respect to
the relational denotational semantics. -/
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

/-- `Iterates guard body n initial final` holds when the loop
`while guard do body`, started in `initial`, exits in `final` after exactly `n`
executions of the body. -/
inductive Iterates (guard : BExp) (body : Cmd) : Nat → State → State → Prop
  | exit {state : State} (hguard : guard.eval state = false) :
      Iterates guard body 0 state state
  | step {n : Nat} {initial middle final : State}
      (hguard : guard.eval initial = true) (hbody : BigStep body initial middle)
      (hrest : Iterates guard body n middle final) :
      Iterates guard body (n + 1) initial final

namespace Iterates

variable {guard : BExp} {body : Cmd}

/-- A loop run with a counted number of iterations is a big-step execution of
the loop. -/
theorem bigStep {n : Nat} {initial final : State}
    (h : Iterates guard body n initial final) :
    BigStep (.while guard body) initial final := by
  induction h with
  | exit hguard => exact .whileFalse hguard
  | step hguard hbody _ ih => exact .whileTrue hguard hbody ih

/-- Every terminating execution of a loop performs some number of
iterations. -/
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

/-- The iteration count of a loop run is determined by its initial state. -/
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
/-- The number of body iterations the loop `while guard do body` performs from
`state` before exiting, or `0` when the loop does not terminate from `state`. -/
noncomputable def iterationCount (guard : BExp) (body : Cmd) (state : State) : Nat :=
  if h : ∃ n final, Iterates guard body n state final then Classical.choose h else 0

/-- On a terminating loop run, `iterationCount` is the run's iteration
count. -/
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

/-- `iterationCount` is `0` from a state where the loop does not terminate. -/
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

/-- Derivable total-correctness Hoare triples. The `while` rule is the variant
rule: the body, started from the invariant with the guard true and the variant
equal to `n`, terminates in the invariant with the variant below `n`. -/
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

/-- Soundness: every derivable total-correctness triple is totally valid. -/
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

/-- Strengthen the precondition of a derivable total-correctness triple. -/
theorem strengthen {pre pre' post : Assertion} {command : Cmd}
    (hpre : pre.Entails pre') (h : TDerivable pre' command post) :
    TDerivable pre command post :=
  .consequence hpre h (Assertion.entails_refl post)

end TDerivable

/-- The weakest precondition is derivable for every command and
postcondition. -/
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

/-- Relative completeness: every totally valid triple is derivable in the
total-correctness system. -/
theorem complete {pre post : Assertion} {command : Cmd}
    (h : TValid pre command post) : TDerivable pre command post :=
  strengthen (wp.tvalid_iff.mp h) (tderivable_wp command post)

/-- A derivable total-correctness triple is a derivable partial-correctness
triple. -/
theorem derivable {pre post : Assertion} {command : Cmd}
    (h : TDerivable pre command post) : Derivable pre command post :=
  Derivable.complete h.sound.valid

end TDerivable

/-- Total-correctness derivability coincides with total validity. -/
theorem tderivable_iff_tvalid {pre post : Assertion} {command : Cmd} :
    TDerivable pre command post ↔ TValid pre command post :=
  ⟨TDerivable.sound, TDerivable.complete⟩

/-- Total-correctness derivability coincides with total validity with respect
to the relational denotational semantics. -/
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

/-- A Hoare triple `{pre} command {post}`, the judgement form of both Hoare
logics. -/
structure Triple where
  /-- The precondition. -/
  pre : Assertion
  /-- The command. -/
  command : Cmd
  /-- The postcondition. -/
  post : Assertion

/-- Tag for the total-correctness inference system on `Triple`. -/
inductive TotalCorrectness : Type

/-- Partial-correctness derivability is the default inference system on Hoare
triples. -/
instance : Cslib.Logic.HasInferenceSystem Triple :=
  ⟨fun t => Derivable t.pre t.command t.post⟩

/-- Total-correctness derivability, under the tag `TotalCorrectness`. -/
instance : Cslib.Logic.InferenceSystem TotalCorrectness Triple :=
  ⟨fun t => TDerivable t.pre t.command t.post⟩

namespace Triple

/-- A triple is derivable in the default (partial-correctness) system iff it
is valid. -/
theorem derivable_iff_valid (t : Triple) :
    Cslib.Logic.InferenceSystem.Derivable t ↔ Valid t.pre t.command t.post :=
  nonempty_prop.trans IMP.derivable_iff_valid

/-- A triple is derivable in the total-correctness system iff it is totally
valid. -/
theorem derivableIn_totalCorrectness_iff_tvalid (t : Triple) :
    Cslib.Logic.InferenceSystem.DerivableIn TotalCorrectness t ↔
      TValid t.pre t.command t.post :=
  nonempty_prop.trans IMP.tderivable_iff_tvalid

end Triple

end Cslib.IMP
