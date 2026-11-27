/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Limits.Shapes.ZeroObjectArrowTransport
public import Mathlib.CategoryTheory.Whiskering

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v u' v'
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- The actual initial-arrow functor uses the given original zero object and every source map. -/
def originalInitialArrowFunctor {Z : C} (hZ : IsZero Z) : C ⥤ Arrow C where
  obj X := Arrow.mk (hZ.to_ X)
  map f := Arrow.homMk (𝟙 Z) f (hZ.eq_of_src _ _)
  map_id X := by apply Arrow.hom_ext <;> simp
  map_comp f g := by apply Arrow.hom_ext <;> simp

/-- The actual terminal-arrow functor uses the same given original zero object. -/
def originalTerminalArrowFunctor {Z : C} (hZ : IsZero Z) : C ⥤ Arrow C where
  obj X := Arrow.mk (hZ.from_ X)
  map f := Arrow.homMk f (𝟙 Z) (hZ.eq_of_tgt _ _)
  map_id X := by apply Arrow.hom_ext <;> simp
  map_comp f g := by apply Arrow.hom_ext <;> simp

/-- All original initial-arrow maps commute with the given original zero comparison. -/
def originalInitialArrowFunctorIso (F : C ⥤ D) {Z : C} (hZ : IsZero Z)
    {Z' : D} (hZ' : IsZero Z') (c : F.obj Z ≅ Z') :
    originalInitialArrowFunctor hZ ⋙ F.mapArrow ≅ F ⋙ originalInitialArrowFunctor hZ' :=
  NatIso.ofComponents
    (fun X => originalInitialArrowIso F hZ'.isInitial c (hZ.to_ X) (hZ'.to_ (F.obj X)))
    (by
      intro X Y f
      apply Arrow.hom_ext
      · change F.map (𝟙 Z) ≫ c.hom = c.hom ≫ 𝟙 Z'
        rw [F.map_id, Category.id_comp, Category.comp_id]
      · change F.map f ≫ 𝟙 (F.obj Y) = 𝟙 (F.obj X) ≫ F.map f
        exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- All original terminal-arrow maps retain their full given source-zero comparison. -/
def originalTerminalArrowFunctorIso (F : C ⥤ D) {Z : C} (hZ : IsZero Z)
    {Z' : D} (hZ' : IsZero Z') (c : F.obj Z ≅ Z') :
    originalTerminalArrowFunctor hZ ⋙ F.mapArrow ≅ F ⋙ originalTerminalArrowFunctor hZ' :=
  NatIso.ofComponents
    (fun X => originalTerminalArrowIso F hZ'.isTerminal c (hZ.from_ X) (hZ'.from_ (F.obj X)))
    (by
      intro X Y f
      apply Arrow.hom_ext
      · change F.map f ≫ 𝟙 (F.obj Y) = 𝟙 (F.obj X) ≫ F.map f
        exact (Category.comp_id _).trans (Category.id_comp _).symm
      · change F.map (𝟙 Z) ≫ c.hom = c.hom ≫ 𝟙 Z'
        rw [F.map_id, Category.id_comp, Category.comp_id])

end CategoryTheory
