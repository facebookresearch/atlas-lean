/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `290c48922e071d1e4267dd103a14e73b547adf60`.
Original formalization by Zeina Migeed (@migeed-z); ported with permission.
-/

module

public import CSLibExt.Computability.Languages.Congruences.Recognition
public import Mathlib.Data.Fintype.BigOperators

/-!
# The syntactic-monoid characterization of regular languages

Every DFA recognizes its language through its transition morphism.  A finite DFA therefore gives
a finite algebraic recognizer, and the universal property of the syntactic monoid makes the latter
finite.  Conversely, the canonical syntactic DFA is finite whenever the syntactic monoid is.
Together these directions prove the classical characterization: a language is regular exactly
when its syntactic monoid is finite.
-/

@[expose] public section

open scoped Computability

namespace Cslib.Language

universe u v

variable {Symbol : Type u} {State : Type v}

/-- The accepting transformations of a DFA are those sending its start state to an accepting
state. -/
def transitionAccept (M : DFA Symbol State) : Set (StateTransformation State) :=
  {f | f M.start ∈ M.accept}

@[simp]
theorem mem_transitionAccept_iff (M : DFA Symbol State) (f : StateTransformation State) :
    f ∈ transitionAccept M ↔ f M.start ∈ M.accept :=
  Iff.rfl

/-- The standard transition accepting set presents the general transition recognizer. -/
theorem recognizes_transitionAccept (M : DFA Symbol State) :
    Recognizes M.accepts (transitionMorphism M) (transitionAccept M) := by
  simpa only [transitionAccept] using recognizes_transitionMorphism M

/-- The transition-monoid image recognizes the same language as the ambient transformation
monoid. -/
theorem recognizes_toTransitionMonoid (M : DFA Symbol State) :
    Recognizes M.accepts (MonoidHom.mrangeRestrict (transitionMorphism M))
      {f : TransitionMonoid M | f.val ∈ transitionAccept M} := by
  intro x
  exact recognizes_transitionAccept M x

/-- A DFA with finite state space has a finite transformation monoid. -/
theorem finite_stateTransformation [Finite State] : Finite (StateTransformation State) := by
  classical
  let _ : Fintype State := Fintype.ofFinite State
  let _ : Fintype (StateTransformation State) :=
    Fintype.ofEquiv (State → State) stateTransformationEquiv.symm
  infer_instance

/-- The transition monoid of a finite-state DFA is finite. -/
theorem finite_transitionMonoid (M : DFA Symbol State) [Finite State] :
    Finite (TransitionMonoid M) := by
  let _ : Finite (StateTransformation State) := finite_stateTransformation
  exact Subtype.finite

/-- Regular languages have finite syntactic monoids. -/
theorem finite_syntacticMonoid_of_isRegular {L : Language Symbol} (hL : L.IsRegular) :
    Finite (SyntacticMonoid L) := by
  let _ : Finite (NerodeClass L) :=
    (isRegular_iff_finite_nerodeClass (L := L)).mp hL
  have hfinite := finite_syntacticMonoid_of_finite_dfa (nerodeDFA L)
  simpa only [accepts_nerodeDFA] using hfinite

/-- A language is regular exactly when its syntactic monoid is finite. -/
theorem isRegular_iff_finite_syntacticMonoid (L : Language Symbol) :
    L.IsRegular ↔ Finite (SyntacticMonoid L) :=
  ⟨finite_syntacticMonoid_of_isRegular, fun _ ↦ isRegular_of_finite_syntacticMonoid L⟩

/-- The syntactic monoid of a regular language can be represented as a quotient of the transition
monoid of any finite DFA recognizing it. -/
noncomputable def transitionMonoidToSyntactic (M : DFA Symbol State) :
    TransitionMonoid M →* SyntacticMonoid M.accepts :=
  recognizerImageToSyntactic (transitionMorphism M) (transitionAccept M)
    (recognizes_transitionAccept M)

@[simp]
theorem transitionMonoidToSyntactic_word (M : DFA Symbol State) (x : FreeMonoid Symbol) :
    transitionMonoidToSyntactic M (toTransitionMonoid M x) =
      syntacticMorphism M.accepts x :=
  recognizerImageToSyntactic_image (transitionMorphism M) (transitionAccept M)
    (recognizes_transitionAccept M) x

theorem transitionMonoidToSyntactic_surjective (M : DFA Symbol State) :
    Function.Surjective (transitionMonoidToSyntactic M) :=
  recognizerImageToSyntactic_surjective (transitionMorphism M) (transitionAccept M)
    (recognizes_transitionAccept M)

/-- For finite state spaces, the syntactic monoid has no more elements than the transition
monoid of any recognizing DFA. -/
theorem card_syntacticMonoid_le_card_transitionMonoid (M : DFA Symbol State)
    [Fintype (TransitionMonoid M)] [Fintype (SyntacticMonoid M.accepts)] :
    Fintype.card (SyntacticMonoid M.accepts) ≤ Fintype.card (TransitionMonoid M) :=
  Fintype.card_le_of_surjective _ (transitionMonoidToSyntactic_surjective M)

/-- A coarser numerical bound uses all endofunctions on the state space. -/
theorem card_syntacticMonoid_le_card_endofunction (M : DFA Symbol State)
    [Fintype State] [Fintype (SyntacticMonoid M.accepts)] :
    Fintype.card (SyntacticMonoid M.accepts) ≤ Fintype.card State ^ Fintype.card State := by
  classical
  let _ : Fintype (State → State) := by infer_instance
  let _ : Fintype (StateTransformation State) :=
    Fintype.ofEquiv (State → State) stateTransformationEquiv.symm
  let _ : Fintype (TransitionMonoid M) := Fintype.ofFinite _
  calc
    Fintype.card (SyntacticMonoid M.accepts) ≤ Fintype.card (TransitionMonoid M) :=
      card_syntacticMonoid_le_card_transitionMonoid M
    _ ≤ Fintype.card (StateTransformation State) := Fintype.card_subtype_le _
    _ = Fintype.card (State → State) := Fintype.card_congr stateTransformationEquiv
    _ = Fintype.card State ^ Fintype.card State := Fintype.card_fun

end Cslib.Language
