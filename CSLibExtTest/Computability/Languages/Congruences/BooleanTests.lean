/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.Congruences.Boolean
public import CSLibExt.Computability.Languages.Congruences.Recognition

/-! # Client tests for Boolean closure of syntactic monoids -/

@[expose] public section

open scoped Computability

namespace Cslib.Language.BooleanTests

/-- Complementing a concrete language preserves syntactic equivalence. -/
example (x y : FreeMonoid Bool) :
    syntacticRel (({[true]} : Language Bool)ᶜ) x y ↔ syntacticRel {[true]} x y :=
  syntacticRel_compl_iff _ _ _

/-- Complementing a concrete language preserves reflexive syntactic equivalence. -/
example (x : FreeMonoid Bool) :
    syntacticRel (({[true]} : Language Bool)ᶜ) x x :=
  (syntacticRel_compl_iff _ _ _).mpr (syntacticRel_refl _ _)

/-- Complementing a concrete language leaves its syntactic congruence unchanged. -/
example : syntacticCon (({[true]} : Language Bool)ᶜ) = syntacticCon {[true]} :=
  syntacticCon_compl _

/-- The complement equivalence sends the syntactic class of a word to itself,
through the morphism rule. -/
example (x : FreeMonoid Bool) :
    syntacticMonoidComplEquiv ({[true]} : Language Bool)
        (syntacticMorphism (({[true]} : Language Bool)ᶜ) x) =
      syntacticMorphism {[true]} x :=
  syntacticMonoidComplEquiv_morphism _ _

/-- The complement equivalence is bijective on syntactic classes. -/
example (q : SyntacticMonoid (({[true]} : Language Bool)ᶜ)) :
    (syntacticMonoidComplEquiv ({[true]} : Language Bool)).symm
        ((syntacticMonoidComplEquiv ({[true]} : Language Bool)) q) = q :=
  MulEquiv.symm_apply_apply _ _

/-- Finite syntactic monoids are closed under complement, on a concrete language. -/
example [Finite (SyntacticMonoid ({[true]} : Language Bool))] :
    Finite (SyntacticMonoid (({[true]} : Language Bool)ᶜ)) :=
  (finite_syntacticMonoid_compl_iff _).mpr inferInstance

/-- Syntactic equivalence for each operand implies syntactic equivalence for
their intersection, union, and difference, on concrete languages. -/
example (x : FreeMonoid Bool) :
    syntacticRel ((({[true]} : Language Bool) ⊓ ({[false]} : Language Bool))) x x :=
  syntacticRel_inter (syntacticRel_refl _ _) (syntacticRel_refl _ _)

example (x : FreeMonoid Bool) :
    syntacticRel ((({[true]} : Language Bool) ⊔ ({[false]} : Language Bool))) x x :=
  syntacticRel_union (syntacticRel_refl _ _) (syntacticRel_refl _ _)

example (x : FreeMonoid Bool) :
    syntacticRel ((({[true]} : Language Bool) - ({[false]} : Language Bool))) x x :=
  syntacticRel_diff (syntacticRel_refl _ _) (syntacticRel_refl _ _)

/-- The common refinement of two syntactic congruences refines the congruence of
the intersection, union, and difference. -/
example : syntacticCon ({[true]} : Language Bool) ⊓ syntacticCon ({[false]} : Language Bool) ≤
    syntacticCon ((({[true]} : Language Bool) ⊓ ({[false]} : Language Bool))) :=
  syntacticCon_inf_le_inter _ _

example : syntacticCon ({[true]} : Language Bool) ⊓ syntacticCon ({[false]} : Language Bool) ≤
    syntacticCon ((({[true]} : Language Bool) ⊔ ({[false]} : Language Bool))) :=
  syntacticCon_inf_le_union _ _

example : syntacticCon ({[true]} : Language Bool) ⊓ syntacticCon ({[false]} : Language Bool) ≤
    syntacticCon ((({[true]} : Language Bool) - ({[false]} : Language Bool))) :=
  syntacticCon_inf_le_diff _ _

/-- The product of the syntactic recognizers recognizes the intersection, union,
and difference of two concrete languages. -/
example : Recognizes ((({[true]} : Language Bool) ⊓ ({[false]} : Language Bool)))
    ((syntacticMorphism {[true]}).prod (syntacticMorphism {[false]}))
    {p | p.1 ∈ syntacticAccept {[true]} ∧ p.2 ∈ syntacticAccept {[false]}} :=
  (recognizes_syntacticMorphism _).inter (recognizes_syntacticMorphism _)

example : Recognizes ((({[true]} : Language Bool) ⊔ ({[false]} : Language Bool)))
    ((syntacticMorphism {[true]}).prod (syntacticMorphism {[false]}))
    {p | p.1 ∈ syntacticAccept {[true]} ∨ p.2 ∈ syntacticAccept {[false]}} :=
  (recognizes_syntacticMorphism _).union (recognizes_syntacticMorphism _)

example : Recognizes ((({[true]} : Language Bool) - ({[false]} : Language Bool)))
    ((syntacticMorphism {[true]}).prod (syntacticMorphism {[false]}))
    {p | p.1 ∈ syntacticAccept {[true]} ∧ p.2 ∉ syntacticAccept {[false]}} :=
  (recognizes_syntacticMorphism _).diff (recognizes_syntacticMorphism _)

/-- Finite syntactic monoids are closed under intersection, union, and difference
of concrete languages. -/
example [Finite (SyntacticMonoid ({[true]} : Language Bool))]
    [Finite (SyntacticMonoid ({[false]} : Language Bool))] :
    Finite (SyntacticMonoid ((({[true]} : Language Bool) ⊓ ({[false]} : Language Bool)))) :=
  finite_syntacticMonoid_inter _ _

example [Finite (SyntacticMonoid ({[true]} : Language Bool))]
    [Finite (SyntacticMonoid ({[false]} : Language Bool))] :
    Finite (SyntacticMonoid ((({[true]} : Language Bool) ⊔ ({[false]} : Language Bool)))) :=
  finite_syntacticMonoid_union _ _

example [Finite (SyntacticMonoid ({[true]} : Language Bool))]
    [Finite (SyntacticMonoid ({[false]} : Language Bool))] :
    Finite (SyntacticMonoid ((({[true]} : Language Bool) - ({[false]} : Language Bool)))) :=
  finite_syntacticMonoid_diff _ _

#print axioms syntacticMonoidComplEquiv
#print axioms syntacticMonoidComplEquiv_morphism
#print axioms finite_syntacticMonoid_compl_iff
#print axioms finite_syntacticMonoid_inter
#print axioms finite_syntacticMonoid_union
#print axioms finite_syntacticMonoid_diff

end Cslib.Language.BooleanTests
