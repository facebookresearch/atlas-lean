/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.MorphismProperty.AdjointFamily

set_option autoImplicit false
noncomputable section
universe w s vC vD uC uD

open CategoryTheory

namespace MathlibExtTest.AdjointFamilyGenerators

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {S : Type s} (L : S → C ⥤ D) (R : S → D ⥤ C) (adj : ∀ a, L a ⊣ R a)
  (P : MorphismProperty C)

-- The actual old literal label family is retained as data, not just a class inclusion.
example : MorphismProperty.adjointFamilyGenerators L P =
    MorphismProperty.ofHoms (fun q : S × P.toSet => (L q.1).map q.2.1.hom) := rfl

example (a : S) {A B : C} (i : A ⟶ B) (hi : P i) :
    MorphismProperty.adjointFamilyGenerators L P ((L a).map i) :=
  MorphismProperty.map_mem_adjointFamilyGenerators L P a i hi

example {X Y : D} (f : X ⟶ Y)
    (hf : MorphismProperty.adjointFamilyGenerators L P f) :
    ∃ q : S × P.toSet, Arrow.mk f = Arrow.mk ((L q.1).map q.2.1.hom) :=
  (MorphismProperty.adjointFamilyGenerators_iff L P f).mp hf

example : MorphismProperty.adjointFamilyGenerators L P =
    ⨆ a : S, P.strictMap (L a) :=
  MorphismProperty.adjointFamilyGenerators_eq_iSup_strictMap L P

example [Small.{w} S] [P.IsSmall.{w}] :
    (MorphismProperty.adjointFamilyGenerators L P).IsSmall.{w} :=
  MorphismProperty.adjointFamilyGenerators_isSmall L P

example {X Y : D} (f : X ⟶ Y) :
    (MorphismProperty.adjointFamilyGenerators L P).rlp f ↔
      ∀ a : S, P.rlp ((R a).map f) :=
  MorphismProperty.adjointFamilyGenerators_rlp_iff L R adj P f

-- Genuine lifting of the caller's actual base member and target arrow.
example (a : S) {A B : C} (i : A ⟶ B) (hi : P i) {X Y : D} (f : X ⟶ Y)
    (hf : (MorphismProperty.adjointFamilyGenerators L P).rlp f) :
    HasLiftingProperty i ((R a).map f) :=
  ((MorphismProperty.adjointFamilyGenerators_rlp_iff L R adj P f).mp hf a) i hi

-- An empty evaluation index imposes no artificial Nonempty hypothesis.
example (L0 : PEmpty → C ⥤ D) (R0 : PEmpty → D ⥤ C)
    (a0 : ∀ a, L0 a ⊣ R0 a) {X Y : D} (f : X ⟶ Y) :
    (MorphismProperty.adjointFamilyGenerators L0 P).rlp f := by
  apply (MorphismProperty.adjointFamilyGenerators_rlp_iff L0 R0 a0 P f).mpr
  intro a
  exact PEmpty.elim a

-- Unequal Hom universes are explicit in both directions.
section IndependentHomUniverses
variable {C0 : Type 2} [Category.{0} C0] {D1 : Type 3} [Category.{1} D1]
  (L01 : PUnit → C0 ⥤ D1) (P0 : MorphismProperty C0)
example : MorphismProperty D1 := MorphismProperty.adjointFamilyGenerators L01 P0
end IndependentHomUniverses

section ReversedHomUniverses
variable {C1 : Type 3} [Category.{1} C1] {D0 : Type 2} [Category.{0} D0]
  (L10 : PUnit → C1 ⥤ D0) (P1 : MorphismProperty C1)
example : MorphismProperty D0 := MorphismProperty.adjointFamilyGenerators L10 P1
end ReversedHomUniverses

#check @MorphismProperty.adjointFamilyGenerators_rlp_iff
#check @MorphismProperty.adjointFamilyGenerators_isSmall
#print axioms MorphismProperty.adjointFamilyGenerators
#print axioms MorphismProperty.adjointFamilyGenerators_iff
#print axioms MorphismProperty.map_mem_adjointFamilyGenerators
#print axioms MorphismProperty.adjointFamilyGenerators_eq_iSup_strictMap
#print axioms MorphismProperty.adjointFamilyGenerators_isSmall
#print axioms MorphismProperty.adjointFamilyGenerators_rlp_iff

end MathlibExtTest.AdjointFamilyGenerators
