/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `1184e99236ece3db95d28d07b55998ccaebeec53`.
Original formalization by Zeina Migeed (@migeed-z); ported with permission.
-/

module

public import CSLibExt.Computability.Languages.Congruences.Contexts
public import CSLibExt.Computability.Languages.Congruences.Morphisms
public import CSLibExt.Computability.Languages.Congruences.SyntacticMinimal
public import CSLibExt.Computability.Languages.Congruences.TransitionMinimal
public import CSLibExt.Computability.Languages.Congruences.WordMorphisms

/-! # Tests for algebraic closure and minimal transition monoids -/

@[expose] public section

open scoped Computability

namespace Cslib.Language.AlgebraicClosureTests

universe u v

variable {Symbol : Type u} {State : Type v}

example (M : DFA Symbol State) (hacc : Accessible M) (hsep : StateSeparated M)
    (x : FreeMonoid Symbol) :
    syntacticMonoidEquivTransitionMonoid M hacc hsep (syntacticMorphism M.accepts x) =
      toTransitionMonoid M x :=
  syntacticMonoidEquivTransitionMonoid_morphism M hacc hsep x

example (M : DFA Symbol State) (hacc : Accessible M) (hsep : StateSeparated M)
    (q : SyntacticMonoid M.accepts) :
    transitionMonoidToSyntactic M
        (syntacticMonoidEquivTransitionMonoid M hacc hsep q) = q :=
  transitionMonoidToSyntactic_rightInverse M hacc hsep q

example (M : DFA Symbol State) (hacc : Accessible M) (hsep : StateSeparated M)
    (f : TransitionMonoid M) :
    syntacticMonoidEquivTransitionMonoid M hacc hsep
        (transitionMonoidToSyntactic M f) = f :=
  transitionMonoidToSyntactic_leftInverse M hacc hsep f

/-! Elaboration tests for the canonical minimal-DFA specializations.

The three `MulEquiv` specializations in `SyntacticMinimal.lean` are built by
transporting the general equivalence along `accepts` equalities. These examples
exercise the public API only: the `[simp]` morphism lemmas, stated in simp-normal
form at the coercion `(x : SyntacticMonoid _)`, rewrite the value on a
`syntacticMorphism` term to `toTransitionMonoid` without unfolding the transports
(`syntacticMorphism_apply` converts the term to the coercion), and the round-trip
examples use the specializations as equivalences. -/

example (L : Language Symbol) (x : FreeMonoid Symbol) :
    syntacticMonoidEquivTransitionMonoidToDFA L (syntacticMorphism L x) =
      toTransitionMonoid L.toDFA x :=
  by rw [syntacticMorphism_apply]; exact syntacticMonoidEquivTransitionMonoidToDFA_morphism L x

example (L : Language Symbol) (x : FreeMonoid Symbol) :
    syntacticMonoidEquivTransitionMonoidToDFA L (syntacticMorphism L x) =
      toTransitionMonoid L.toDFA x := by
  simp [syntacticMonoidEquivTransitionMonoidToDFA_morphism]

example (M : DFA Symbol State) (x : FreeMonoid Symbol) :
    syntacticMonoidEquivTransitionMonoidMinimizedDFA M (syntacticMorphism M.accepts x) =
      toTransitionMonoid (minimizedDFA M) x :=
  by rw [syntacticMorphism_apply]; exact syntacticMonoidEquivTransitionMonoidMinimizedDFA_morphism M x

example (M : DFA Symbol State) (x : FreeMonoid Symbol) :
    syntacticMonoidEquivTransitionMonoidMinimizedDFA M (syntacticMorphism M.accepts x) =
      toTransitionMonoid (minimizedDFA M) x := by
  simp [syntacticMonoidEquivTransitionMonoidMinimizedDFA_morphism]

example {Alpha : Type} (l : Language Alpha) (x : FreeMonoid Alpha) :
    syntacticMonoidEquivTransitionMonoidNerodeCongruenceDA l (syntacticMorphism l x) =
      toTransitionMonoid (Cslib.Automata.DA.FinAcc.toDFA l.NerodeCongruenceDA) x :=
  by rw [syntacticMorphism_apply]; exact syntacticMonoidEquivTransitionMonoidNerodeCongruenceDA_morphism l x

example {Alpha : Type} (l : Language Alpha) (x : FreeMonoid Alpha) :
    syntacticMonoidEquivTransitionMonoidNerodeCongruenceDA l (syntacticMorphism l x) =
      toTransitionMonoid (Cslib.Automata.DA.FinAcc.toDFA l.NerodeCongruenceDA) x := by
  simp [syntacticMonoidEquivTransitionMonoidNerodeCongruenceDA_morphism]

example (L : Language Symbol) (f : TransitionMonoid L.toDFA) :
    (syntacticMonoidEquivTransitionMonoidToDFA L)
        ((syntacticMonoidEquivTransitionMonoidToDFA L).symm f) = f := by
  exact (syntacticMonoidEquivTransitionMonoidToDFA L).apply_symm_apply f

example (M : DFA Symbol State) (x : FreeMonoid Symbol) :
    syntacticMonoidEquivTransitionMonoidMinimizedDFA M
        (syntacticMorphism M.accepts x) *
      syntacticMonoidEquivTransitionMonoidMinimizedDFA M (syntacticMorphism M.accepts 1) =
      toTransitionMonoid (minimizedDFA M) x := by
  rw [syntacticMorphism_apply, syntacticMorphism_apply,
    syntacticMonoidEquivTransitionMonoidMinimizedDFA_morphism,
    syntacticMonoidEquivTransitionMonoidMinimizedDFA_morphism]
  have h1 : toTransitionMonoid (minimizedDFA M) (1 : FreeMonoid Symbol) = 1 :=
    Subtype.ext (MonoidHom.map_one _)
  rw [h1, mul_one]

example (L : Language Bool) : contextQuotient L [] [] = L :=
  contextQuotient_nil_nil L

example (L : Language Bool) (right : List Bool) :
    contextQuotient L [] right = rightQuotient L right :=
  contextQuotient_nil_left L right

example (L : Language Bool) (left : List Bool) :
    contextQuotient L left [] = L.leftQuotient left :=
  contextQuotient_nil_right L left

example (L : Language Bool) (a b c d : List Bool) :
    contextQuotient (contextQuotient L a b) c d =
      contextQuotient L (a ++ c) (d ++ b) :=
  contextQuotient_contextQuotient L a b c d

example (L : Language Bool) [Finite (SyntacticMonoid L)] (left right : List Bool) :
    Finite (SyntacticMonoid (contextQuotient L left right)) :=
  finite_syntacticMonoid_contextQuotient L left right

example {L : Language Bool} (hL : L.IsRegular) (left right : List Bool) :
    (contextQuotient L left right).IsRegular :=
  IsRegular.contextQuotient hL left right

example (L : Language Bool) (x y : FreeMonoid Bool) :
    syntacticRel L x y ↔
      ∀ left right,
        FreeMonoid.toList x ∈ contextQuotient L left right ↔
          FreeMonoid.toList y ∈ contextQuotient L left right :=
  syntacticRel_iff_mem_contextQuotient L x y

example {L : Language Bool} (hL : L.IsRegular) (right : List Bool) :
    (rightQuotient L right).IsRegular :=
  IsRegular.rightQuotient' hL right

example {L : Language Bool} (hL : L.IsRegular) (pre : List Bool) :
    (L.leftQuotient pre).IsRegular :=
  IsRegular.leftQuotient hL pre

/-- The last letter read; accepts the words ending in `true`. -/
def endsTrueDFA : DFA Bool Bool :=
  ⟨fun _ b => b, false, {true}⟩

/-- The left quotient of its language by `[false]` is again regular. -/
example : (endsTrueDFA.accepts.leftQuotient [false]).IsRegular :=
  IsRegular.leftQuotient ⟨Bool, inferInstance, endsTrueDFA, rfl⟩ [false]

example (L : Language Bool) [Finite (SyntacticMonoid L)] (f : Nat → Bool) :
    Finite (SyntacticMonoid (alphabetPreimage f L)) :=
  finite_syntacticMonoid_alphabetPreimage f L

example {L : Language Bool} (hL : L.IsRegular) (f : Nat → Bool) :
    (alphabetPreimage f L).IsRegular :=
  IsRegular.alphabetPreimage hL f

example {L : Language Bool} (hL : L.IsRegular)
    (substitution : FreeMonoid Nat →* FreeMonoid Bool) :
    (wordMorphismPreimage substitution L).IsRegular :=
  IsRegular.wordMorphismPreimage hL substitution

example (L : Language Bool) (substitution : FreeMonoid Nat →* FreeMonoid Bool) :
    wordMorphismPreimage substitution L =
      wordMorphismPreimage substitution (wordMorphismPreimage (MonoidHom.id _) L) := by
  rw [wordMorphismPreimage_id]

end Cslib.Language.AlgebraicClosureTests
