/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.Yoneda

/-!
# Right-comma comparison prefix

For `F : C ⥤ D` and `d : D`, the contravariant hom coefficient `commaCoeffR F d`
sends `op c` to `F.obj c ⟶ d`. Its opposite category of elements is explicitly
equivalent to the right comma category `CostructuredArrow F d`.

Nonclaims: no bar/nerve comparison, no naturality square, no opposite nerve bridge,
no contraction, no homotopy, and no KQ statement.
-/

@[expose] public section

open CategoryTheory Opposite

universe u₁ v₁ u₂ v₂

namespace CategoryTheory

namespace CategoryBar

/-- Contravariant hom coefficient for the right comma category. -/
noncomputable def commaCoeffR
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) (d : D) : Cᵒᵖ ⥤ Type v₂ :=
  F.op ⋙ yoneda.obj d

@[simp] theorem commaCoeffR_obj
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) (d : D) (c : C) :
    (commaCoeffR F d).obj (op c) = (F.obj c ⟶ d) :=
  rfl

@[simp] theorem commaCoeffR_map
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) (d : D) {c c' : C} (f : op c ⟶ op c')
    (h : F.obj c ⟶ d) :
    (ConcreteCategory.hom (X := (F.obj c ⟶ d)) (Y := (F.obj c' ⟶ d))
      ((commaCoeffR F d).map f)) h = F.map f.unop ≫ h :=
  rfl

/-- Coefficient map induced covariantly by postcomposition with `g`. -/
noncomputable def commaCoeffRMap
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) {d d' : D} (g : d ⟶ d') :
    commaCoeffR F d ⟶ commaCoeffR F d' :=
  Functor.whiskerLeft F.op (yoneda.map g)

set_option backward.isDefEq.respectTransparency.types false in
/-- The opposite category of elements of the right-comma coefficient is the right comma category. -/
noncomputable def commaElementsEquivR
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) (d : D) :
    (commaCoeffR F d).Elementsᵒᵖ ≌ CostructuredArrow F d where
  functor :=
    { obj := fun X => CostructuredArrow.mk X.unop.val
      map := fun {X Y} f => CostructuredArrow.homMk f.unop.hom.unop f.unop.map_val
      map_id := fun X => by
        apply CostructuredArrow.hom_ext
        simp
      map_comp := fun f g => by
        apply CostructuredArrow.hom_ext
        simp [CostructuredArrow.comp_left] }
  inverse :=
    { obj := fun Y =>
        (op ((commaCoeffR F d).elementsMk (op Y.left) Y.hom) :
          (commaCoeffR F d).Elementsᵒᵖ)
      map := fun {X Y} g =>
        Quiver.Hom.op
          (Functor.Elements.homMk
            (x := ((commaCoeffR F d).elementsMk (op Y.left) Y.hom))
            (y := ((commaCoeffR F d).elementsMk (op X.left) X.hom)) g.left.op
            (by
              change F.map g.left ≫ Y.hom = X.hom
              exact CostructuredArrow.w g))
      map_id := fun X => by
        apply Quiver.Hom.unop_inj
        apply Functor.Elements.hom_ext
        simp
      map_comp := fun f g => by
        apply Quiver.Hom.unop_inj
        apply Functor.Elements.hom_ext
        simp }
  unitIso :=
    NatIso.ofComponents (fun X => Iso.refl _) (by
      rintro X Y f
      apply Quiver.Hom.unop_inj
      apply Functor.Elements.hom_ext
      simp)
  counitIso :=
    NatIso.ofComponents (fun X => Iso.refl _) (by
      intro X Y f
      simp only [Iso.refl_hom, Functor.id_map, Functor.id_obj]
      rw [Category.comp_id, Category.id_comp]
      apply CostructuredArrow.hom_ext
      rfl)
  functor_unitIso_comp X := by
    obtain ⟨Y⟩ := X
    simp

end CategoryBar

end CategoryTheory
