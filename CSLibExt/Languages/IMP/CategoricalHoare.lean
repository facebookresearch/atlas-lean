/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import CSLibExt.Languages.IMP.HoareCompleteness
public import MathlibExt.CategoryTheory.Monoidal.PowersetVerification
public import MathlibExt.CategoryTheory.Monoidal.VerificationFunctor

/-!
# IMP Hoare logic through categorical verification

An IMP command is interpreted by its existing big-step execution relation.
Powerset verification then gives exactly the existing partial-correctness
judgment, and hence the existing relatively complete IMP proof system.

A while command is finite-path feedback of a body that tests the guard, exits
when it is false, and otherwise executes the command and feeds its result back.
The equality with operational semantics is proved in both directions. It makes
the ordinary while-invariant rule an instance of categorical trace preservation.
No new program semantics or termination assumption is introduced.

Source: Arthan, Martin, Mathiesen and Oliva, *A General Framework for Sound and
Complete Floyd-Hoare Logics*, Section 4.3 and Figure 10,
https://arxiv.org/abs/0807.1016.
-/

@[expose] public section
namespace Cslib.IMP.CategoricalHoare
open CategoryTheory MonoidalCategory CategoryTheory.VerificationFunctor
open scoped MonoidalCategory

/-- IMP states as an object of the disjoint-union relation category. -/
abbrev states : SumRelCat := SumRelCat.of State

/-- The terminating execution relation of `c` (pairs related by `BigStep c`), viewed as a
morphism `states ⟶ states`. -/
def commandRel (c : Cmd) : states ⟶ states :=
  .ofRel {p | BigStep c p.1 p.2}

/-- The powerset verification triple of `commandRel c` from `P` to `Q` holds iff the IMP
Hoare triple `{P} c {Q}` is valid (`Valid P c Q`). -/
theorem triple_iff_valid (c : Cmd) (P Q : Assertion) :
    VerificationFunctor.Triple PowersetVerification.verification
      (commandRel c) {s | P s} {s | Q s} ↔
      Valid P c Q := by
  change (commandRel c).rel.image {s | P s} ⊆ {s | Q s} ↔ _
  constructor
  · intro h s t hP hc
    exact h ⟨s, hP, hc⟩
  · rintro h t ⟨s, hP, hc⟩
    exact h hP hc

/-- The IMP Hoare calculus derives `{P} c {Q}` (`IMP.Derivable P c Q`) iff the powerset
verification triple of `commandRel c` from `P` to `Q` holds. -/
theorem derivable_iff_triple (c : Cmd) (P Q : Assertion) :
    IMP.Derivable P c Q ↔
      VerificationFunctor.Triple PowersetVerification.verification
        (commandRel c) {s | P s} {s | Q s} :=
  IMP.derivable_iff_valid.trans (triple_iff_valid c P Q).symm

/-- Skip is the identity relation. -/
@[simp] theorem commandRel_skip : commandRel .skip = 𝟙 states := by
  apply SumRelCat.Hom.ext
  ext ⟨s, t⟩
  exact BigStep.skip_iff.trans eq_comm

/-- Sequential commands use categorical relational composition. -/
theorem commandRel_seq (c d : Cmd) : commandRel (.seq c d) = commandRel c ≫ commandRel d := by
  apply SumRelCat.Hom.ext
  ext ⟨s, t⟩
  exact BigStep.seq_iff

/-- Forget whether a state entered externally or through the feedback wire. -/
def controlState : Sum State State → State := Sum.elim id id

/-- A guarded loop body: from either input wire carrying `s`, it puts `s` on the exit wire when
the guard is false, and on the feedback wire each `t` that `c` reaches from `s` by a terminating
execution when the guard is true. -/
def loopBody (b : BExp) (c : Cmd) : states ⊗ states ⟶ states ⊗ states :=
  .ofRel {p | match p.2 with
    | .inl t => b.eval (controlState p.1) = false ∧ t = controlState p.1
    | .inr t => b.eval (controlState p.1) = true ∧ BigStep c (controlState p.1) t}

/-- Finite feedback executions and terminating while executions coincide,
including executions beginning on the hidden wire. -/
theorem loopBody_path_iff (b : BExp) (c : Cmd) (s : Sum State State) (t : State) :
    SumRelCat.FeedbackPath (loopBody b c) s t ↔
      BigStep (.while b c) (controlState s) t := by
  constructor
  · intro h
    induction h with
    | @output s t h =>
        change b.eval (controlState s) = false ∧ t = controlState s at h
        obtain ⟨hb, rfl⟩ := h
        exact .whileFalse hb
    | step h _ ih => exact .whileTrue h.1 h.2 ih
  · intro h
    obtain ⟨n, hn⟩ := Iterates.exists_of_bigStep h
    clear h
    generalize hs : controlState s = initial at hn
    induction hn generalizing s with
    | exit hb =>
        exact .output ⟨by simpa [hs] using hb, hs.symm⟩
    | @step n initial middle final hb hc _ ih =>
        exact .step ⟨by simpa [hs] using hb, by simpa [hs] using hc⟩
          (ih (Sum.inr middle) rfl)

/-- The operational while command is exactly categorical finite-path feedback. -/
theorem commandRel_while (b : BExp) (c : Cmd) :
    commandRel (.while b c) = SumRelCat.symmetricTrace.trace (loopBody b c) := by
  apply SumRelCat.Hom.ext
  ext ⟨s, t⟩
  exact (loopBody_path_iff b c (Sum.inl s) t).symm

/-- `{P} while b do c {Q}` is valid iff some `I` makes the categorical loop body satisfy the
powerset tensor triple from `(P, I)` to `(Q, I)`. -/
theorem while_valid_iff_invariant (b : BExp) (c : Cmd) (P Q : Assertion) :
    Valid P (.while b c) Q ↔ ∃ I : Set State,
      TensorTriple PowersetVerification.verification (loopBody b c) ({s | P s}, I)
        ({s | Q s}, I) := by
  rw [← triple_iff_valid, commandRel_while]
  exact triple_trace_iff _ PowersetVerification.preserves_trace _ _ _

/-- A usual preserved loop invariant supplies the categorical body specification. -/
theorem loopBody_invariant (b : BExp) (c : Cmd) (I : Assertion)
    (hbody : Valid (fun s => I s ∧ b.eval s = true) c I) :
    TensorTriple PowersetVerification.verification (loopBody b c) ({s | I s}, {s | I s})
      ({s | I s ∧ b.eval s = false}, {s | I s}) := by
  rw [TensorTriple, PowersetVerification.comparison_rel]
  rintro t ⟨s, hs, hst⟩
  have hI : I (controlState s) := by
    cases s <;> simpa [PowersetVerification.tensorOrderIso, controlState] using hs
  cases t with
  | inl t =>
      change b.eval (controlState s) = false ∧ t = controlState s at hst
      apply (PowersetVerification.tensorOrderIso_inl _ _ _ _).mpr
      obtain ⟨hb, rfl⟩ := hst
      exact ⟨hI, hb⟩
  | inr t =>
      exact (PowersetVerification.tensorOrderIso_inr _ _ _ _).mpr
        (hbody ⟨hI, hst.1⟩ hst.2)

end Cslib.IMP.CategoricalHoare
