/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.CategoryTheory.Monoidal.ExternalProduct.KanExtension

/-!
# Units for composite left Kan extensions

Compose two extension units along a specified comparison of index functors. For external
products, the composite unit has components given by tensoring the two units. Mathlib's
`Functor.isLeftKanExtension_iff_postcompose` supplies the Kan universal property for either unit.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Functor Limits MonoidalCategory
open scoped ExternalProduct

namespace CategoryTheory.Functor.KanExtension

section ExternalComposite

universe u₁ u₂ u₃ v₁ v₂ v₃

variable {C : Type u₁} {D : Type u₂} {V : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} V] [MonoidalCategory V]
  (j : C ⥤ D) {X Y : C ⥤ V} (X' Y' : D ⥤ V)
  (α : X ⟶ j ⋙ X') (β : Y ⟶ j ⋙ Y')

/-- The original pasted external unit, with its full associator and index comparison. -/
def externalCompositeUnit : X ⊠ Y ⟶ j.prod j ⋙ X' ⊠ Y' :=
  ExternalProduct.extensionUnitLeft X' α Y ≫
    whiskerLeft (j.prod (𝟭 C)) (ExternalProduct.extensionUnitRight Y' β X') ≫
      (Functor.associator (j.prod (𝟭 C)) ((𝟭 D).prod j) (X' ⊠ Y')).inv ≫
        whiskerRight (Iso.refl (j.prod j)).hom (X' ⊠ Y')

/-- Every coefficient of the original pasted unit is the tensor of both original units. -/
theorem externalCompositeUnit_app (q : C × C) :
    (externalCompositeUnit j X' Y' α β).app q = α.app q.1 ⊗ₘ β.app q.2 := by
  simp only [externalCompositeUnit, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    Functor.associator_inv_app, Iso.refl_hom, NatTrans.id_app,
    externalProductBifunctor_map_app, Functor.leftUnitor_inv_app, Category.id_comp]
  simp only [Functor.comp_obj, Functor.prod_obj, Functor.id_obj]
  rw [(X' ⊠ Y').map_id]
  simp only [MonoidalCategory.whiskerLeft_id, id_whiskerRight, Category.comp_id, Category.id_comp,
    tensorHom_def]

end ExternalComposite

section KanComposite

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄

variable {C : Type u₁} {D : Type u₂} {E : Type u₃} {V : Type u₄}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} V]
  (L₁ : C ⥤ D) (L₂ : D ⥤ E) (L : C ⥤ E) (e : L₁ ⋙ L₂ ≅ L)
  {F₀ : C ⥤ V} {F₁ : D ⥤ V} (F₂ : E ⥤ V)
  (α : F₀ ⟶ L₁ ⋙ F₁) (β : F₁ ⟶ L₂ ⋙ F₂)

/-- The original composite Kan unit retains its complete index comparison. -/
def kanCompositeUnit : F₀ ⟶ L ⋙ F₂ :=
  α ≫ whiskerLeft L₁ β ≫ (Functor.associator L₁ L₂ F₂).inv ≫ whiskerRight e.hom F₂

/-- The full composite Kan unit has its original coefficient and index-map formula. -/
theorem kanCompositeUnit_app (c : C) :
    (kanCompositeUnit L₁ L₂ L e F₂ α β).app c =
      α.app c ≫ β.app (L₁.obj c) ≫ F₂.map (e.hom.app c) := by
  simp only [kanCompositeUnit, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    Functor.associator_inv_app, Category.id_comp]

end KanComposite

end CategoryTheory.Functor.KanExtension
