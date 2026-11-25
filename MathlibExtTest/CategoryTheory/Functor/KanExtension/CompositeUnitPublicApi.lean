/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua

import MathlibExt.CategoryTheory.Functor.KanExtension.CompositeUnit

/-! # Generic callers of the complete composite Kan unit -/

set_option autoImplicit false
noncomputable section
universe uC vC uD vD uE vE uV vV

open CategoryTheory CategoryTheory.Functor Limits MonoidalCategory
open CategoryTheory.Functor.KanExtension
open scoped ExternalProduct

namespace MathlibExtTest.CompositeKanUnit

section Composite

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {E : Type uE} [Category.{vE} E] {V : Type uV} [Category.{vV} V]
  (L₁ : C ⥤ D) (L₂ : D ⥤ E) (L : C ⥤ E) (e : L₁ ⋙ L₂ ≅ L)
  {F₀ : C ⥤ V} {F₁ : D ⥤ V} (F₂ : E ⥤ V)
  (α : F₀ ⟶ L₁ ⋙ F₁) (β : F₁ ⟶ L₂ ⋙ F₂)

/-- Construct the full left extension from its two supplied extension units. -/
def compositeExtension : L.LeftExtension F₀ :=
  Functor.LeftExtension.mk F₂ (kanCompositeUnit L₁ L₂ L e F₂ α β)

example (c : C) :
    (kanCompositeUnit L₁ L₂ L e F₂ α β).app c =
      α.app c ≫ β.app (L₁.obj c) ≫ F₂.map (e.hom.app c) :=
  kanCompositeUnit_app L₁ L₂ L e F₂ α β c

variable [F₁.IsLeftKanExtension α] [F₂.IsLeftKanExtension β]

private lemma composite_isLeftKan :
    F₂.IsLeftKanExtension (kanCompositeUnit L₁ L₂ L e F₂ α β) :=
  (Functor.isLeftKanExtension_iff_postcompose α L e β _ rfl).mp inferInstance

/-- The two given universal properties make the complete composite unit detect every target map. -/
theorem composite_maps_unique {G : E ⥤ V} (f g : F₂ ⟶ G)
    (h : kanCompositeUnit L₁ L₂ L e F₂ α β ≫ whiskerLeft L f =
      kanCompositeUnit L₁ L₂ L e F₂ α β ≫ whiskerLeft L g) : f = g := by
  let := composite_isLeftKan L₁ L₂ L e F₂ α β
  exact Functor.hom_ext_of_isLeftKanExtension F₂ (kanCompositeUnit L₁ L₂ L e F₂ α β) f g h

end Composite

section External

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  (j : C ⥤ D) {X Y : C ⥤ V} (X' Y' : D ⥤ V)
  (α : X ⟶ j ⋙ X') (β : Y ⟶ j ⋙ Y')

private lemma external_index_hom (a b : C) :
    (show j.prod (𝟭 C) ⋙ (𝟭 D).prod j ≅ j.prod j from
      Iso.refl (j.prod j)).hom.app (a, b) = 𝟙 (j.obj a, j.obj b) := rfl

/-- The pasted unit is constructed on both full input functors. -/
def externalExtension : (j.prod j).LeftExtension (X ⊠ Y) :=
  Functor.LeftExtension.mk (X' ⊠ Y') (externalCompositeUnit j X' Y' α β)

example (a b : C) :
    (externalCompositeUnit j X' Y' α β).app (a, b) = α.app a ⊗ₘ β.app b :=
  externalCompositeUnit_app j X' Y' α β (a, b)

variable [(X' ⊠ Y).IsLeftKanExtension (ExternalProduct.extensionUnitLeft X' α Y)]
  [(X' ⊠ Y').IsLeftKanExtension (ExternalProduct.extensionUnitRight Y' β X')]

private lemma external_isLeftKan :
    (X' ⊠ Y').IsLeftKanExtension (externalCompositeUnit j X' Y' α β) :=
  (Functor.isLeftKanExtension_iff_postcompose (L' := (𝟭 D).prod j)
    (ExternalProduct.extensionUnitLeft X' α Y) (j.prod j) (Iso.refl (j.prod j))
    (ExternalProduct.extensionUnitRight Y' β X') _ rfl).mp inferInstance

/-- The original left and right external extensions jointly detect every full map out of their target. -/
theorem external_maps_unique {Z : D × D ⥤ V} (f g : X' ⊠ Y' ⟶ Z)
    (h : externalCompositeUnit j X' Y' α β ≫ whiskerLeft (j.prod j) f =
      externalCompositeUnit j X' Y' α β ≫ whiskerLeft (j.prod j) g) : f = g := by
  let := external_isLeftKan j X' Y' α β
  exact Functor.hom_ext_of_isLeftKanExtension (X' ⊠ Y') (externalCompositeUnit j X' Y' α β) f g h

end External

section Identity

variable {C : Type uC} [Category.{vC} C] {V : Type uV} [Category.{vV} V]

/-- Pasting the actual identity units along the identity index comparison recovers the identity unit. -/
theorem composite_identity_unit (F : C ⥤ V) :
    kanCompositeUnit (𝟭 C) (𝟭 C) (𝟭 C) (Functor.leftUnitor (𝟭 C))
      F F.leftUnitor.inv F.leftUnitor.inv = F.leftUnitor.inv := by
  apply NatTrans.ext
  funext c
  rw [kanCompositeUnit_app]
  simp

end Identity

#print axioms compositeExtension
#print axioms composite_maps_unique
#print axioms externalExtension
#print axioms external_maps_unique
#print axioms composite_identity_unit
#print axioms external_index_hom
#print axioms CategoryTheory.Functor.KanExtension.externalCompositeUnit
#print axioms CategoryTheory.Functor.KanExtension.externalCompositeUnit_app
#print axioms external_isLeftKan
#print axioms CategoryTheory.Functor.KanExtension.kanCompositeUnit
#print axioms CategoryTheory.Functor.KanExtension.kanCompositeUnit_app
#print axioms composite_isLeftKan

end MathlibExtTest.CompositeKanUnit
