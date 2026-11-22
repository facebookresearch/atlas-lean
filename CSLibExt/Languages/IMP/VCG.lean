/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Verification conditions for IMP
-/
module

public import CSLibExt.Languages.IMP.HoareCompleteness

/-!
# Verification-condition generation for IMP

Nipkow and Klein, *Concrete Semantics*, Section 12.4. Commands whose loops are
annotated with invariants (`ACmd`) determine a precondition `ACmd.pre C Q` and
a verification condition `ACmd.vc C Q`, a proposition about assertions alone,
with no command left in it:

* `ACmd.vc_sound`: if the verification condition holds, the triple
  `{pre C Q} strip C {Q}` is derivable in the Hoare logic of
  `HoareCompleteness.lean` (and hence valid, `ACmd.vc_valid`).
* `ACmd.vc_complete`: every derivable triple `{P} c {Q}` has an annotation `C`
  of `c` whose verification condition holds and whose precondition is implied
  by `P`.
* `ACmd.vc_complete_of_valid`: with relative completeness, the same for every
  valid triple.

Assertions are semantic (predicates on states), so `pre` and `vc` are computed
semantically as in the book; `pre_entails_vc` is the monotonicity lemma both
proofs share.
-/

@[expose] public section

namespace Cslib.IMP

/-- Commands whose while loops carry an invariant. -/
inductive ACmd where
  | skip
  | assign (name : Nat) (value : AExp)
  | seq (first second : ACmd)
  | ite (guard : BExp) (thenBranch elseBranch : ACmd)
  | while (invariant : Assertion) (guard : BExp) (body : ACmd)

namespace ACmd

/-- Erase the annotations. -/
def strip : ACmd → Cmd
  | .skip => .skip
  | .assign name value => .assign name value
  | .seq first second => .seq first.strip second.strip
  | .ite guard thenBranch elseBranch => .ite guard thenBranch.strip elseBranch.strip
  | .while _ guard body => .while guard body.strip

/-- The precondition computed backwards from a postcondition; a loop's
precondition is its invariant. -/
def pre : ACmd → Assertion → Assertion
  | .skip, post => post
  | .assign name value, post => post.subst name value
  | .seq first second, post => first.pre (second.pre post)
  | .ite guard thenBranch elseBranch, post => fun state =>
      if guard.eval state = true then thenBranch.pre post state
      else elseBranch.pre post state
  | .while invariant _ _, _ => invariant

/-- The verification condition: for every loop, the invariant and the guard
imply the precondition of the body for the invariant, and the invariant and
the negated guard imply the postcondition. -/
def vc : ACmd → Assertion → Prop
  | .skip, _ => True
  | .assign _ _, _ => True
  | .seq first second, post => first.vc (second.pre post) ∧ second.vc post
  | .ite _ thenBranch elseBranch, post => thenBranch.vc post ∧ elseBranch.vc post
  | .while invariant guard body, post =>
      (∀ state, invariant state → guard.eval state = true → body.pre invariant state) ∧
      (∀ state, invariant state → guard.eval state = false → post state) ∧
      body.vc invariant

/-- Soundness: a true verification condition yields a derivable triple. -/
theorem vc_sound : ∀ (C : ACmd) (post : Assertion), C.vc post →
    Derivable (C.pre post) C.strip post
  | .skip, post, _ => .skip post
  | .assign name value, post, _ => .assign post name value
  | .seq first second, post, ⟨hfirst, hsecond⟩ =>
      .seq (vc_sound first _ hfirst) (vc_sound second post hsecond)
  | .ite guard thenBranch elseBranch, post, ⟨hthen, helse⟩ => by
      refine .ite (.consequence ?_ (vc_sound thenBranch post hthen)
        (Assertion.entails_refl post)) (.consequence ?_ (vc_sound elseBranch post helse)
        (Assertion.entails_refl post))
      · intro state ⟨hpre, hguard⟩
        simpa [pre, hguard] using hpre
      · intro state ⟨hpre, hguard⟩
        simpa [pre, hguard] using hpre
  | .while invariant guard body, post, ⟨hbody, hexit, hvc⟩ => by
      refine .consequence (Assertion.entails_refl invariant)
        (.whileLoop (.consequence ?_ (vc_sound body invariant hvc)
          (Assertion.entails_refl invariant))) ?_
      · intro state ⟨hinv, hguard⟩
        exact hbody state hinv hguard
      · intro state ⟨hinv, hguard⟩
        exact hexit state hinv hguard

/-- Soundness for validity. -/
theorem vc_valid {C : ACmd} {pre' post : Assertion} (hvc : C.vc post)
    (hpre : pre'.Entails (C.pre post)) : Valid pre' C.strip post :=
  (Derivable.strengthen hpre (vc_sound C post hvc)).sound

/-- Monotonicity: weakening the postcondition weakens the precondition and
preserves the verification condition. -/
theorem pre_entails_vc : ∀ (C : ACmd) {post post' : Assertion}, post.Entails post' →
    C.vc post → (C.pre post).Entails (C.pre post') ∧ C.vc post'
  | .skip, _, _, h, _ => ⟨h, trivial⟩
  | .assign _ _, _, _, h, _ => ⟨fun _ hs => h hs, trivial⟩
  | .seq first second, _, _, h, ⟨hfirst, hsecond⟩ =>
      let ⟨hpre₂, hvc₂⟩ := pre_entails_vc second h hsecond
      let ⟨hpre₁, hvc₁⟩ := pre_entails_vc first hpre₂ hfirst
      ⟨hpre₁, hvc₁, hvc₂⟩
  | .ite guard thenBranch elseBranch, _, _, h, ⟨hthen, helse⟩ => by
      obtain ⟨hpre₁, hvc₁⟩ := pre_entails_vc thenBranch h hthen
      obtain ⟨hpre₂, hvc₂⟩ := pre_entails_vc elseBranch h helse
      refine ⟨fun state hs => ?_, hvc₁, hvc₂⟩
      by_cases hguard : guard.eval state = true
      · simp only [pre, hguard, ↓reduceIte] at hs ⊢
        exact hpre₁ hs
      · simp only [pre, hguard] at hs ⊢
        exact hpre₂ hs
  | .while _ _ _, _, _, h, ⟨hbody, hexit, hvc⟩ =>
      ⟨Assertion.entails_refl _, hbody, fun state hinv hguard => h (hexit state hinv hguard), hvc⟩

/-- Completeness: every derivable triple has an annotation whose verification
condition holds and whose precondition follows from the triple's. -/
theorem vc_complete {pre' post : Assertion} {command : Cmd}
    (h : Derivable pre' command post) :
    ∃ C : ACmd, C.strip = command ∧ C.vc post ∧ pre'.Entails (C.pre post) := by
  induction h with
  | skip post => exact ⟨.skip, rfl, trivial, Assertion.entails_refl post⟩
  | assign post name value =>
      exact ⟨.assign name value, rfl, trivial, Assertion.entails_refl _⟩
  | seq _ _ ihFirst ihSecond =>
      obtain ⟨C₁, hs₁, hvc₁, hpre₁⟩ := ihFirst
      obtain ⟨C₂, hs₂, hvc₂, hpre₂⟩ := ihSecond
      obtain ⟨hmono, hvc₁'⟩ := pre_entails_vc C₁ hpre₂ hvc₁
      exact ⟨.seq C₁ C₂, by rw [strip, hs₁, hs₂], ⟨hvc₁', hvc₂⟩, hpre₁.trans hmono⟩
  | @ite pre' post guard _ _ _ _ ihThen ihElse =>
      obtain ⟨C₁, hs₁, hvc₁, hpre₁⟩ := ihThen
      obtain ⟨C₂, hs₂, hvc₂, hpre₂⟩ := ihElse
      refine ⟨.ite guard C₁ C₂, by rw [strip, hs₁, hs₂], ⟨hvc₁, hvc₂⟩, fun state hs => ?_⟩
      by_cases hguard : guard.eval state = true
      · simp only [pre, hguard, ↓reduceIte]
        exact hpre₁ ⟨hs, hguard⟩
      · simp only [pre, hguard]
        exact hpre₂ ⟨hs, by simpa using hguard⟩
  | @whileLoop invariant guard _ _ ih =>
      obtain ⟨C, hs, hvc, hpre⟩ := ih
      exact ⟨.while invariant guard C, by rw [strip, hs],
        ⟨fun state hinv hguard => hpre ⟨hinv, hguard⟩, fun _ hinv hguard => ⟨hinv, hguard⟩, hvc⟩,
        Assertion.entails_refl invariant⟩
  | consequence hpre _ hpost ih =>
      obtain ⟨C, hs, hvc, hpre'⟩ := ih
      obtain ⟨hmono, hvc'⟩ := pre_entails_vc C hpost hvc
      exact ⟨C, hs, hvc', (hpre.trans hpre').trans hmono⟩

/-- Completeness for validity, by relative completeness of the Hoare logic. -/
theorem vc_complete_of_valid {pre' post : Assertion} {command : Cmd}
    (h : Valid pre' command post) :
    ∃ C : ACmd, C.strip = command ∧ C.vc post ∧ pre'.Entails (C.pre post) :=
  vc_complete (derivable_iff_valid.mpr h)

end ACmd

end Cslib.IMP
