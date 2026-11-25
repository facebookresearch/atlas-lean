/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado

module

import Mathlib.AlgebraicTopology.SimplicialSet.CoherentIso
import Mathlib.CategoryTheory.Products.Basic
import MathlibExt.CategoryTheory.Functor.Isofibration

/-!
# Tests for functor isofibrations

Consumer checks for the public `IsIsofibration` / `isofibrations` API:
signature pins, identity and composition, the multiplicative /
respects-isomorphisms / retract instances on `isofibrations`,
isomorphisms in `Cat`, surjective equivalences, a product-projection
example proved from the public constructor, and an honest
non-isofibration: the inclusion of a point into the walking
isomorphism category `CategoryTheory.WalkingIso` (the codiscrete
category on two objects) is an equivalence of categories but not an
isofibration. This shows that essential
surjectivity alone does not imply the strict lifting property, and that
the surjectivity hypothesis in
`Functor.isIsofibration_of_isEquivalence_of_surjective` cannot be
dropped.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory

universe v₁ v₂ u₁ u₂ u

namespace MathlibExtTest.Isofibration

#check @CategoryTheory.Functor.IsIsofibration
#check @CategoryTheory.isofibrations
#check @CategoryTheory.isofibrations.mem_iff
#check @CategoryTheory.Functor.exists_iso_lift
#check @CategoryTheory.Functor.exists_lift_hom
#check @CategoryTheory.Functor.isIsofibration_of_full_faithful_of_surjective
#check @CategoryTheory.Functor.isIsofibration_of_isEquivalence_of_surjective
#check @CategoryTheory.isofibrations_of_isIso

section Signature

example : MorphismProperty Cat.{u, u} := CategoryTheory.isofibrations.{u}

example {X Y : Cat.{u, u}} (F : X ⟶ Y) :
    CategoryTheory.isofibrations F ↔ F.toFunctor.IsIsofibration :=
  CategoryTheory.isofibrations.mem_iff F

end Signature

section Generic

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

example : (𝟭 C).IsIsofibration := inferInstance

example (F : C ⥤ D) (G : D ⥤ C) [F.IsIsofibration] [G.IsIsofibration] :
    (F ⋙ G).IsIsofibration := inferInstance

example (F : C ⥤ D) [F.IsIsofibration] {X : C} {Y : D} (g : F.obj X ≅ Y) :
    ∃ (Y' : C) (f : X ≅ Y') (h : F.obj Y' = Y), F.mapIso f ≪≫ eqToIso h = g :=
  F.exists_iso_lift g

example (F : C ⥤ D) [F.IsEquivalence] (hF : Function.Surjective F.obj) :
    F.IsIsofibration :=
  F.isIsofibration_of_isEquivalence_of_surjective hF

example (e : C ≌ D) (hF : Function.Surjective e.functor.obj) :
    e.functor.IsIsofibration :=
  e.isIsofibration_functor_of_surjective hF

example (F : C ⥤ D) [F.IsIso] : F.IsIsofibration := inferInstance

example (e : IsoCat C D) : e.functor.IsIsofibration := inferInstance

end Generic

section CatProperty

example : MorphismProperty.IsMultiplicative (CategoryTheory.isofibrations.{u}) :=
  inferInstance

example : MorphismProperty.RespectsIso (CategoryTheory.isofibrations.{u}) :=
  inferInstance

example : MorphismProperty.IsStableUnderRetracts (CategoryTheory.isofibrations.{u}) :=
  inferInstance

example (X : Cat.{u, u}) : CategoryTheory.isofibrations (𝟙 X) :=
  CategoryTheory.isofibrations.id_mem X

example {X Y Z : Cat.{u, u}} {F : X ⟶ Y} {G : Y ⟶ Z}
    (hF : CategoryTheory.isofibrations F) (hG : CategoryTheory.isofibrations G) :
    CategoryTheory.isofibrations (F ≫ G) :=
  CategoryTheory.isofibrations.comp_mem hF hG

example {X Y : Cat.{u, u}} (F : X ⟶ Y) [IsIso F] :
    CategoryTheory.isofibrations F :=
  CategoryTheory.isofibrations_of_isIso F

example {C D : Type u} [Category.{u} C] [Category.{u} D] (F : C ⥤ D)
    [F.IsIsofibration] : CategoryTheory.isofibrations F.toCatHom :=
  CategoryTheory.isofibrations_toCatHom F

end CatProperty

section Projection

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- The first projection from a product of categories is an isofibration:
an isomorphism in the first factor lifts by keeping the second factor
fixed. -/
example : (CategoryTheory.Prod.fst C D).IsIsofibration where
  exists_lift := by
    intro X Y g
    exact ⟨(Y, X.2), Iso.prod g (Iso.refl X.2), rfl, by
      apply Iso.ext
      simp⟩

end Projection

/-- The two objects of `WalkingIso` are distinct: they are the
codiscrete points corresponding to `false` and `true`. -/
theorem walkingIso_zero_ne_one : WalkingIso.zero.{0} ≠ WalkingIso.one.{0} := by
  intro h
  have hbool := congrArg (fun z : WalkingIso.{0} => z.as.down) h
  change false = true at hbool
  contradiction

/-- The inclusion of the point `WalkingIso.zero` into the walking
isomorphism category `WalkingIso`. -/
def pointInclusion : Discrete PUnit ⥤ WalkingIso.{0} :=
  (Functor.const (Discrete PUnit)).obj WalkingIso.zero

instance : pointInclusion.Faithful where
  map_injective := by
    intro X Y f g _
    exact Subsingleton.elim f g

instance : pointInclusion.Full where
  map_surjective := by
    intro X Y f
    exact ⟨eqToHom (Subsingleton.elim X Y), Subsingleton.elim _ _⟩

instance : pointInclusion.EssSurj where
  mem_essImage _ := ⟨⟨PUnit.unit⟩, ⟨Codiscrete.iso _ _⟩⟩

instance : pointInclusion.IsEquivalence where

example : pointInclusion.IsEquivalence := inferInstance

/-- The point inclusion into the walking isomorphism category is an
equivalence of categories but not an isofibration: the isomorphism
`WalkingIso.iso : WalkingIso.zero ≅ WalkingIso.one` has no strict lift,
since every object in the strict image of `pointInclusion` on objects
is `WalkingIso.zero`. -/
theorem pointInclusion_not_isIsofibration : ¬ pointInclusion.IsIsofibration := by
  intro h
  obtain ⟨Y', _f, hobj, _hf⟩ :=
    h.exists_lift (X := ⟨PUnit.unit⟩) WalkingIso.iso
  change WalkingIso.zero = WalkingIso.one at hobj
  exact walkingIso_zero_ne_one hobj

#print axioms CategoryTheory.Functor.isIsofibration_comp
#print axioms pointInclusion_not_isIsofibration

end MathlibExtTest.Isofibration
