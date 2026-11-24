/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright (c) 2026 @toskua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj

/-! # Characteristic maps of the original Leibniz construction -/

@[expose] public section

noncomputable section

universe u₁ u₂ u₃ v₁ v₂ v₃

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor.PushoutObjObj

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃]
  {F : C₁ ⥤ C₂ ⥤ C₃}

section Left
variable {f₁ f₁' : Arrow C₁} {f₂ : Arrow C₂}
  (sq₁ : F.PushoutObjObj f₁.hom f₂.hom)
  (sq₂ : F.PushoutObjObj f₁'.hom f₂.hom) (a : f₁ ⟶ f₁')

/-- The first inclusion of an actual Leibniz map is its prescribed descendant. -/
@[reassoc]
theorem inl_mapArrowLeft :
    sq₁.inl ≫ (mapArrowLeft sq₁ sq₂ a).left =
      (F.map a.right).app f₂.left ≫ sq₂.inl := by
  exact sq₁.isPushout.inl_desc _ _ _

/-- The second inclusion of an actual Leibniz map is its prescribed descendant. -/
@[reassoc]
theorem inr_mapArrowLeft :
    sq₁.inr ≫ (mapArrowLeft sq₁ sq₂ a).left =
      (F.map a.left).app f₂.right ≫ sq₂.inr := by
  exact sq₁.isPushout.inr_desc _ _ _

end Left

section Right
variable {f₁ : Arrow C₁} {f₂ f₂' : Arrow C₂}
  (sq₁ : F.PushoutObjObj f₁.hom f₂.hom)
  (sq₂ : F.PushoutObjObj f₁.hom f₂'.hom) (a : f₂ ⟶ f₂')

/-- The first inclusion retains the whole map in the second Arrow parameter. -/
@[reassoc]
theorem inl_mapArrowRight :
    sq₁.inl ≫ (mapArrowRight sq₁ sq₂ a).left =
      (F.obj f₁.right).map a.left ≫ sq₂.inl := by
  exact sq₁.isPushout.inl_desc _ _ _

/-- The second inclusion retains the whole map in the second Arrow parameter. -/
@[reassoc]
theorem inr_mapArrowRight :
    sq₁.inr ≫ (mapArrowRight sq₁ sq₂ a).left =
      (F.obj f₁.left).map a.right ≫ sq₂.inr := by
  exact sq₁.isPushout.inr_desc _ _ _

/-- Flipping a given square retains the actual Leibniz Arrow map. -/
theorem mapArrowLeft_flip :
    mapArrowLeft sq₁.flip sq₂.flip a = mapArrowRight sq₁ sq₂ a := by
  apply Arrow.hom_ext
  · apply sq₁.hom_ext
    · exact (inr_mapArrowLeft sq₁.flip sq₂.flip a).trans
        (inl_mapArrowRight sq₁ sq₂ a).symm
    · exact (inl_mapArrowLeft sq₁.flip sq₂.flip a).trans
        (inr_mapArrowRight sq₁ sq₂ a).symm
  · rfl

end Right
end CategoryTheory.Functor.PushoutObjObj
