/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Three-stage adjunction composition

The Hom equivalence, unit, and counit of three composed adjunctions retain
all three given stages and independent object and morphism universes.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open CategoryTheory

namespace CategoryTheory.Adjunction.TripleComposition

universe uA vA uB vB uC vC uD vD
variable {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
  {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : B ⥤ C} {R₂ : C ⥤ B}
  {L₃ : C ⥤ D} {R₃ : D ⥤ C}
  (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃)

/-- The complete original forward composite Hom function at three actual adjunctions. -/
theorem forward (X : A) (Y : D) (f : (L₁ ⋙ L₂ ⋙ L₃).obj X ⟶ Y) :
    ((a₁.comp a₂).comp a₃).homEquiv X Y f =
      a₁.homEquiv X (R₂.obj (R₃.obj Y))
        (a₂.homEquiv (L₁.obj X) (R₃.obj Y) (a₃.homEquiv (L₂.obj (L₁.obj X)) Y f)) := by
  rw [Adjunction.comp_homEquiv, Adjunction.comp_homEquiv]
  rfl

/-- The complete original inverse composite Hom function keeps the three actual inverse
functions. -/
theorem inverse (X : A) (Y : D) (g : X ⟶ (R₃ ⋙ R₂ ⋙ R₁).obj Y) :
    (((a₁.comp a₂).comp a₃).homEquiv X Y).symm g =
      (a₃.homEquiv (L₂.obj (L₁.obj X)) Y).symm
        ((a₂.homEquiv (L₁.obj X) (R₃.obj Y)).symm
          ((a₁.homEquiv X (R₂.obj (R₃.obj Y))).symm g)) := by
  rw [Adjunction.comp_homEquiv, Adjunction.comp_homEquiv]
  rfl

/-- The whole composite unit uses all three original units. -/
theorem unit (X : A) :
    ((a₁.comp a₂).comp a₃).unit.app X =
      a₁.unit.app X ≫ R₁.map (a₂.unit.app (L₁.obj X)) ≫
        R₁.map (R₂.map (a₃.unit.app (L₂.obj (L₁.obj X)))) := by
  rw [Adjunction.comp_unit_app, Adjunction.comp_unit_app]
  exact Category.assoc _ _ _

/-- The whole composite counit uses all three original counits. -/
theorem counit (Y : D) :
    ((a₁.comp a₂).comp a₃).counit.app Y =
      L₃.map (L₂.map (a₁.counit.app (R₂.obj (R₃.obj Y)))) ≫
        L₃.map (a₂.counit.app (R₃.obj Y)) ≫ a₃.counit.app Y := by
  rw [Adjunction.comp_counit_app, Adjunction.comp_counit_app, Functor.map_comp]
  exact Category.assoc _ _ _

end CategoryTheory.Adjunction.TripleComposition
