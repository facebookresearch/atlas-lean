/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Equivalence of big-step and small-step semantics for IMP
-/
module

public import CSLibExt.Languages.IMP.SmallStep
public import CSLibExt.Languages.IMP.Hoare

/-!
# Big-step and small-step equivalence

Terminating big-step executions correspond exactly to finite small-step
executions reaching `skip`. The key lemma for the hard direction is that a
single small step can be prepended to a big-step derivation.
-/

@[expose] public section

namespace Cslib.IMP

/-- Every big-step execution is a finite small-step execution. -/
theorem Terminates.of_bigStep {c : Cmd} {s s' : State} (h : BigStep c s s') :
    Terminates c s s' := by
  induction h with
  | skip => exact Terminates.skip _
  | assign => exact Terminates.assign _ _ _
  | seq _ _ ih1 ih2 => exact Terminates.seq ih1 ih2
  | iteTrue hg _ ih =>
      exact Relation.ReflTransGen.head (Step.iteTrue hg) ih
  | iteFalse hg _ ih =>
      exact Relation.ReflTransGen.head (Step.iteFalse hg) ih
  | whileFalse hg =>
      exact Relation.ReflTransGen.head (Step.whileStep _ _ _)
        (Relation.ReflTransGen.head (Step.iteFalse hg) Relation.ReflTransGen.refl)
  | whileTrue hg _ _ ihBody ihLoop =>
      exact Relation.ReflTransGen.head (Step.whileStep _ _ _)
        (Relation.ReflTransGen.head (Step.iteTrue hg) (Terminates.seq ihBody ihLoop))

/-- A single small step can be prepended to a big-step derivation. -/
theorem BigStep.of_step {x y : Config} {s' : State} (hstep : Step x y)
    (h : BigStep y.1 y.2 s') : BigStep x.1 x.2 s' := by
  revert h
  induction hstep generalizing s' with
  | assign =>
      intro h
      rw [BigStep.skip_iff] at h
      subst h
      exact .assign _ _ _
  | seqSkip =>
      intro h
      exact .seq (.skip _) h
  | seqStep _ ih =>
      intro h
      rw [BigStep.seq_iff] at h
      obtain ⟨m, h1, h2⟩ := h
      exact .seq (ih h1) h2
  | iteTrue hg =>
      intro h
      exact .iteTrue hg h
  | iteFalse hg =>
      intro h
      exact .iteFalse hg h
  | whileStep =>
      intro h
      rw [BigStep.ite_iff] at h
      rcases h with ⟨hg, hseq⟩ | ⟨hg, hskip⟩
      · rw [BigStep.seq_iff] at hseq
        obtain ⟨m, hb, hl⟩ := hseq
        exact .whileTrue hg hb hl
      · rw [BigStep.skip_iff] at hskip
        subst hskip
        exact .whileFalse hg

/-- Finitely many small steps can be prepended to a big-step derivation. -/
theorem BigStep.of_steps {x y : Config} {s' : State} (hsteps : Steps x y)
    (h : BigStep y.1 y.2 s') : BigStep x.1 x.2 s' := by
  induction hsteps using Relation.ReflTransGen.head_induction_on with
  | refl => exact h
  | head hstep _ ih => exact BigStep.of_step hstep ih

/-- Every terminating small-step execution is a big-step execution. -/
theorem BigStep.of_terminates {c : Cmd} {s s' : State} (h : Terminates c s s') :
    BigStep c s s' :=
  BigStep.of_steps h (.skip _)

/-- Small-step termination and big-step execution coincide. -/
theorem terminates_iff_bigStep {c : Cmd} {s s' : State} :
    Terminates c s s' ↔ BigStep c s s' :=
  ⟨BigStep.of_terminates, Terminates.of_bigStep⟩

/-- Small-step termination is deterministic. -/
theorem Terminates.deterministic {c : Cmd} {s s1 s2 : State}
    (h1 : Terminates c s s1) (h2 : Terminates c s s2) : s1 = s2 :=
  BigStep.deterministic (BigStep.of_terminates h1) (BigStep.of_terminates h2)

/-- Hoare validity can equivalently be stated with small-step termination. -/
theorem Valid.iff_terminates {pre post : Assertion} {c : Cmd} :
    Valid pre c post ↔
      ∀ ⦃s s' : State⦄, pre s → Terminates c s s' → post s' := by
  constructor
  · intro hv s s' hpre hterm
    exact hv hpre (BigStep.of_terminates hterm)
  · intro ht s s' hpre hbig
    exact ht hpre (Terminates.of_bigStep hbig)

end Cslib.IMP
