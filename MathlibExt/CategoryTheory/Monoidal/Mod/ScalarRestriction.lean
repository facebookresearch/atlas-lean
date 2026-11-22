/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.Mod.MonoidalAdjunction
public import MathlibExt.CategoryTheory.Monoidal.Mod.ExtensionOfScalars

/-!
# Restricting scalars through a monoidal adjunction

First restrict along a scalar map out of the image monoid, then apply the
module lift of the monoidal adjunction. The composite action retains the
adjunction unit, scalar map, right tensorator, and original module action.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Functor Limits MonoidalCategory
open scoped ExternalProduct CategoryTheory.MonObj CategoryTheory.Obj

namespace CategoryTheory.Mod.MonoidalAdjunction

universe u₁ u₂ v₁ v₂

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [MonoidalCategory C] [MonoidalCategory D] {F : C ⥤ D} {R : D ⥤ C}
  [F.Monoidal] [R.LaxMonoidal] (a : F ⊣ R) [a.IsMonoidal]
  (A : C) [MonObj A] {B : D} [MonObj B] (p : F.obj A ⟶ B) [IsMonHom p]

/-- The two original restriction stages are fixed before the concrete module values. -/
def scalarRestriction : Mod D B ⥤ Mod C A :=
  Mod.ExtensionOfScalars.restriction p ⋙ Mod.MonoidalAdjunction.right a A

/-- The full original composite action uses the actual unit, scalar map and right-adjoint tensorator. -/
theorem scalarRestriction_action (M : Mod D B) :
    ((scalarRestriction a A p).obj M).mod.smul =
      ((a.unit.app A ≫ R.map p) ▷ R.obj M.X) ≫
        Functor.LaxMonoidal.μ R B M.X ≫ R.map M.mod.smul := by
  have h := Mod.MonoidalAdjunction.right_action a A
    ((Mod.ExtensionOfScalars.restriction p).obj M)
  change ((scalarRestriction a A p).obj M).mod.smul =
    (a.unit.app A ▷ R.obj M.X) ≫ Functor.LaxMonoidal.μ R (F.obj A) M.X ≫
      R.map ((p ▷ M.X) ≫ M.mod.smul) at h
  have hn := Functor.LaxMonoidal.μ_natural_left R p M.X
  calc
    _ = (a.unit.app A ▷ R.obj M.X) ≫ Functor.LaxMonoidal.μ R (F.obj A) M.X ≫
        R.map (p ▷ M.X) ≫ R.map M.mod.smul := by
      rw [h, R.map_comp]
    _ = (a.unit.app A ▷ R.obj M.X) ≫ (R.map p ▷ R.obj M.X) ≫
        Functor.LaxMonoidal.μ R B M.X ≫ R.map M.mod.smul := by
      rw [reassoc_of% hn]
    _ = _ := by rw [MonoidalCategory.comp_whiskerRight, Category.assoc]

end CategoryTheory.Mod.MonoidalAdjunction
