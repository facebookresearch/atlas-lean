/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `7f0f951227ee766bba21a6d5a5e56d9065fe85aa`.
Original formalization by Zeina Migeed (@migeed-z); ported with permission.
-/

module

public import CSLibExt.Computability.Languages.Congruences.Regularity

/-!
# Minimal DFAs and their transition monoids

For an accessible, state-separated DFA, two words have the same transition action exactly when
they are syntactically equivalent.  The embedding of the syntactic monoid into state
transformations therefore lands precisely in the transition monoid and is an isomorphism onto it.
This identifies the abstract syntactic monoid with the concrete transition monoid of every minimal
DFA presentation.
-/

@[expose] public section

open scoped Computability

namespace Cslib.Language

universe u v

variable {Symbol : Type u} {State : Type v}

/-- Restrict the syntactic action of a minimal DFA to its transition monoid. -/
def syntacticToTransitionMonoid (M : DFA Symbol State) (hacc : Accessible M)
    (hsep : StateSeparated M) : SyntacticMonoid M.accepts →* TransitionMonoid M :=
  (syntacticActionHom M hacc hsep).codRestrict (TransitionMonoid M) <| by
    intro q
    rw [← syntacticActionHom_range M hacc hsep]
    exact ⟨q, rfl⟩

@[simp]
theorem syntacticToTransitionMonoid_val (M : DFA Symbol State) (hacc : Accessible M)
    (hsep : StateSeparated M) (q : SyntacticMonoid M.accepts) :
    (syntacticToTransitionMonoid M hacc hsep q).val = syntacticActionHom M hacc hsep q :=
  rfl

@[simp]
theorem syntacticToTransitionMonoid_morphism (M : DFA Symbol State) (hacc : Accessible M)
    (hsep : StateSeparated M) (x : FreeMonoid Symbol) :
    syntacticToTransitionMonoid M hacc hsep (syntacticMorphism M.accepts x) =
      toTransitionMonoid M x := by
  apply Subtype.ext
  exact syntacticActionHom_mk M hacc hsep x

theorem syntacticToTransitionMonoid_injective (M : DFA Symbol State) (hacc : Accessible M)
    (hsep : StateSeparated M) : Function.Injective (syntacticToTransitionMonoid M hacc hsep) := by
  intro p q hpq
  apply syntacticActionHom_injective M hacc hsep
  exact congrArg Subtype.val hpq

theorem syntacticToTransitionMonoid_surjective (M : DFA Symbol State) (hacc : Accessible M)
    (hsep : StateSeparated M) : Function.Surjective (syntacticToTransitionMonoid M hacc hsep) := by
  intro f
  obtain ⟨x, rfl⟩ := toTransitionMonoid_surjective M f
  exact ⟨syntacticMorphism M.accepts x,
    syntacticToTransitionMonoid_morphism M hacc hsep x⟩

/-- The syntactic monoid is canonically isomorphic to the transition monoid of every accessible,
state-separated DFA recognizing the language. -/
noncomputable def syntacticMonoidEquivTransitionMonoid (M : DFA Symbol State)
    (hacc : Accessible M) (hsep : StateSeparated M) :
    SyntacticMonoid M.accepts ≃* TransitionMonoid M :=
  MulEquiv.ofBijective (syntacticToTransitionMonoid M hacc hsep)
    ⟨syntacticToTransitionMonoid_injective M hacc hsep,
      syntacticToTransitionMonoid_surjective M hacc hsep⟩

@[simp]
theorem syntacticMonoidEquivTransitionMonoid_apply (M : DFA Symbol State)
    (hacc : Accessible M) (hsep : StateSeparated M) (q : SyntacticMonoid M.accepts) :
    syntacticMonoidEquivTransitionMonoid M hacc hsep q =
      syntacticToTransitionMonoid M hacc hsep q :=
  rfl

@[simp]
theorem syntacticMonoidEquivTransitionMonoid_morphism (M : DFA Symbol State)
    (hacc : Accessible M) (hsep : StateSeparated M) (x : FreeMonoid Symbol) :
    syntacticMonoidEquivTransitionMonoid M hacc hsep (syntacticMorphism M.accepts x) =
      toTransitionMonoid M x :=
  syntacticToTransitionMonoid_morphism M hacc hsep x

/-- Minimal DFAs have a transition monoid with exactly as many elements as the syntactic monoid. -/
theorem card_syntacticMonoid_eq_card_transitionMonoid (M : DFA Symbol State)
    (hacc : Accessible M) (hsep : StateSeparated M)
    [Fintype (SyntacticMonoid M.accepts)] [Fintype (TransitionMonoid M)] :
    Fintype.card (SyntacticMonoid M.accepts) = Fintype.card (TransitionMonoid M) :=
  Fintype.card_congr (syntacticMonoidEquivTransitionMonoid M hacc hsep).toEquiv

/-- The quotient map from an arbitrary transition monoid becomes the inverse of the canonical
isomorphism when the DFA is accessible and state-separated. -/
theorem transitionMonoidToSyntactic_rightInverse (M : DFA Symbol State)
    (hacc : Accessible M) (hsep : StateSeparated M) :
    Function.LeftInverse (transitionMonoidToSyntactic M)
      (syntacticMonoidEquivTransitionMonoid M hacc hsep) := by
  intro q
  induction q using Con.induction_on with
  | _ x =>
    change transitionMonoidToSyntactic M
      (syntacticMonoidEquivTransitionMonoid M hacc hsep
        (syntacticMorphism M.accepts x)) = syntacticMorphism M.accepts x
    rw [syntacticMonoidEquivTransitionMonoid_morphism,
      transitionMonoidToSyntactic_word]

theorem transitionMonoidToSyntactic_leftInverse (M : DFA Symbol State)
    (hacc : Accessible M) (hsep : StateSeparated M) :
    Function.LeftInverse (syntacticMonoidEquivTransitionMonoid M hacc hsep)
      (transitionMonoidToSyntactic M) := by
  intro f
  obtain ⟨x, rfl⟩ := toTransitionMonoid_surjective M f
  rw [transitionMonoidToSyntactic_word,
    syntacticMonoidEquivTransitionMonoid_morphism]

/-- Consequently, on a minimal DFA the transition-monoid quotient map is injective. -/
theorem transitionMonoidToSyntactic_injective_of_minimal (M : DFA Symbol State)
  (hacc : Accessible M) (hsep : StateSeparated M) :
    Function.Injective (transitionMonoidToSyntactic M) :=
  (transitionMonoidToSyntactic_leftInverse M hacc hsep).injective

end Cslib.Language
