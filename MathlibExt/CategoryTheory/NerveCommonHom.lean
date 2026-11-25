/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-!
# Native nerve maps across object levels with a common Hom level

The source objects lie in `max uObj vObj`, the target objects in `uObj`,
and both Hom levels are `max vObj wHom`. Their original nerves therefore
have the same value universe. The maps retain the original categories and
apply the original functor to each composable-arrow chain.
-/

@[expose] public section

universe uObj vObj wHom

namespace CategoryTheory

open Opposite
open scoped Simplicial

section Maps

variable {A : Type (max uObj vObj)} [Category.{max vObj wHom} A]
  {B : Type uObj} [Category.{max vObj wHom} B]

/-- The original functor acts on chains without changing its object or Hom types. -/
def nerveMapCommonHom (F : A ⥤ B) : nerve A ⟶ nerve B where
  app _ := ↾fun X => (F.mapComposableArrows _).obj X

/-- The reverse object-level direction uses the same native chain map. -/
def nerveMapCommonHomUp (F : B ⥤ A) : nerve B ⟶ nerve A where
  app _ := ↾fun X => (F.mapComposableArrows _).obj X

/-- The up map acts on each original composable-arrow chain. -/
theorem nerveMapCommonHomUp_app (F : B ⥤ A) (Δ : SimplexCategoryᵒᵖ)
    (X : (nerve B).obj Δ) :
    (nerveMapCommonHomUp.{uObj, vObj, wHom} F).app Δ X =
      (F.mapComposableArrows Δ.unop.len).obj X := rfl

/-- The up map retains the original vertex through the given functor. -/
theorem nerveMapCommonHomUp_app_mk₀ (F : B ⥤ A) (x : B) :
    (nerveMapCommonHomUp.{uObj, vObj, wHom} F).app
        (op ⦋0⦌) (ComposableArrows.mk₀ x) = ComposableArrows.mk₀ (F.obj x) :=
  ComposableArrows.ext₀ rfl

/-- Down then up is the ordinary nerve map, including a different final category. -/
theorem nerveMapCommonHom_comp_up
    {D : Type (max uObj vObj)} [Category.{max vObj wHom} D]
    (F : A ⥤ B) (G : B ⥤ D) :
    nerveMapCommonHom.{uObj, vObj, wHom} F ≫
      nerveMapCommonHomUp.{uObj, vObj, wHom} G = nerveMap (F ⋙ G) := by
  ext Δ X
  rfl

/-- Up then down is the ordinary nerve map, including a different final category. -/
theorem nerveMapCommonHomUp_comp
    {D : Type uObj} [Category.{max vObj wHom} D] (F : B ⥤ A) (G : A ⥤ D) :
    nerveMapCommonHomUp.{uObj, vObj, wHom} F ≫
      nerveMapCommonHom.{uObj, vObj, wHom} G = nerveMap (F ⋙ G) := by
  ext Δ X
  rfl

/-- An ordinary map followed by the down map acts on the original composite chains. -/
theorem nerveMap_nerveMapCommonHom_comp
    {D : Type (max uObj vObj)} [Category.{max vObj wHom} D]
    (F : D ⥤ A) (G : A ⥤ B) :
    nerveMap F ≫ nerveMapCommonHom.{uObj, vObj, wHom} G =
      nerveMapCommonHom.{uObj, vObj, wHom} (F ⋙ G) := by
  ext Δ X
  rfl

/-- The down map followed by an ordinary map retains the original composite chains. -/
theorem nerveMapCommonHom_nerveMap_comp
    {D : Type uObj} [Category.{max vObj wHom} D] (F : A ⥤ B) (G : B ⥤ D) :
    nerveMapCommonHom.{uObj, vObj, wHom} F ≫ nerveMap G =
      nerveMapCommonHom.{uObj, vObj, wHom} (F ⋙ G) := by
  ext Δ X
  rfl

/-- An ordinary map followed by the up map retains the original composite chains. -/
theorem nerveMap_nerveMapCommonHomUp_comp
    {D : Type uObj} [Category.{max vObj wHom} D] (F : D ⥤ B) (G : B ⥤ A) :
    nerveMap F ≫ nerveMapCommonHomUp.{uObj, vObj, wHom} G =
      nerveMapCommonHomUp.{uObj, vObj, wHom} (F ⋙ G) := by
  ext Δ X
  rfl

/-- The up map followed by an ordinary map retains the original composite chains. -/
theorem nerveMapCommonHomUp_nerveMap_comp
    {D : Type (max uObj vObj)} [Category.{max vObj wHom} D]
    (F : B ⥤ A) (G : A ⥤ D) :
    nerveMapCommonHomUp.{uObj, vObj, wHom} F ≫ nerveMap G =
      nerveMapCommonHomUp.{uObj, vObj, wHom} (F ⋙ G) := by
  ext Δ X
  rfl

end Maps

section Compatibility

variable {C D : Type (max uObj vObj)}
  [Category.{max vObj wHom} C] [Category.{max vObj wHom} D]

/-- At coinciding object levels the downward map is the original ordinary nerve map. -/
theorem nerveMapCommonHom_eq_nerveMap (F : C ⥤ D) :
    nerveMapCommonHom.{max uObj vObj, vObj, wHom} F = nerveMap F := by
  ext Δ X
  rfl

/-- At coinciding object levels the upward map is the original ordinary nerve map. -/
theorem nerveMapCommonHomUp_eq_nerveMap (F : C ⥤ D) :
    nerveMapCommonHomUp.{max uObj vObj, vObj, wHom} F = nerveMap F := by
  ext Δ X
  rfl

end Compatibility

end CategoryTheory
