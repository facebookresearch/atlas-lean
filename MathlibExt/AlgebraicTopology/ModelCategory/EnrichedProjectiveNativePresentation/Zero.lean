/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.Zero
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

/-!
# Actual original-presentation zero diagrams and complete Arrow comparisons

The given original carrier inverse transports the genuine native zero
diagram. Its actual counit compares both full zero Arrow functors with the
native ones, retaining the original arbitrary source map on each square.
-/

set_option autoImplicit false
noncomputable section
universe u v uC vC

open CategoryTheory CategoryTheory.Limits

namespace HomotopicalAlgebra.EnrichedProjective.NativePresentation.Zero

variable {A : Type} [EnrichedCategory PointedCGWH.{u, v} A]
variable {C : Type uC} [Category.{vC} C]

/-- The original supplied carrier inverse determines the source zero object. -/
def object (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) : C :=
  e.inverse.obj (Native.Diagrams.zeroDiagram (A := A))

/-- The original counit compares this same source zero with the native zero. -/
def comparisonIso (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    e.functor.obj (object e) ≅ Native.Diagrams.zeroDiagram (A := A) :=
  e.counitIso.app Native.Diagrams.zeroDiagram

/-- The actual mapped source zero is zero through that original counit. -/
theorem mapped_isZero (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    IsZero (e.functor.obj (object e)) :=
  Native.Diagrams.zeroDiagram_isZero.of_iso (comparisonIso e)

/-- The genuine original carrier equivalence reflects this actual zero object. -/
theorem isZero (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) : IsZero (object e) :=
  IsZero.of_full_of_faithful_of_isZero e.functor (object e) (mapped_isZero e)

/-- The initial-object witness induced by the same chosen source zero. -/
def isInitial (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) : IsInitial (object e) :=
  (isZero e).isInitial

/-- The terminal-object witness induced by the same chosen source zero. -/
def isTerminal (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) : IsTerminal (object e) :=
  (isZero e).isTerminal

theorem hasZeroObject (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) : HasZeroObject C :=
  (isZero e).hasZeroObject

/-- The original source zero-to-object map, without a new zero choice. -/
def toObject (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (X : C) : object e ⟶ X :=
  (isZero e).to_ X

/-- The original source object-to-zero map into that same actual zero. -/
def fromObject (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (X : C) : X ⟶ object e :=
  (isZero e).from_ X

theorem toObject_naturality (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A)
    {X Y : C} (f : X ⟶ Y) : toObject e X ≫ f = toObject e Y :=
  (isZero e).eq_of_src _ _

theorem fromObject_naturality (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A)
    {X Y : C} (f : X ⟶ Y) : f ≫ fromObject e Y = fromObject e X :=
  (isZero e).eq_of_tgt _ _

/-- The full source zero-to-object Arrow functor retains the original source map. -/
def fromZeroArrow (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) : C ⥤ Arrow C where
  obj X := Arrow.mk (toObject e X)
  map f := Arrow.homMk (𝟙 (object e)) f ((isZero e).eq_of_src _ _)
  map_id X := by apply Arrow.hom_ext <;> simp
  map_comp f g := by apply Arrow.hom_ext <;> simp

/-- The full source object-to-zero Arrow functor retains its other original map side. -/
def toZeroArrow (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) : C ⥤ Arrow C where
  obj X := Arrow.mk (fromObject e X)
  map f := Arrow.homMk f (𝟙 (object e)) ((isZero e).eq_of_tgt _ _)
  map_id X := by apply Arrow.hom_ext <;> simp
  map_comp f g := by apply Arrow.hom_ext <;> simp

theorem fromZeroArrow_map_left (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A)
    {X Y : C} (f : X ⟶ Y) : (fromZeroArrow e |>.map f).left = 𝟙 (object e) := rfl

theorem fromZeroArrow_map_right (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A)
    {X Y : C} (f : X ⟶ Y) : (fromZeroArrow e |>.map f).right = f := rfl

theorem toZeroArrow_map_left (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A)
    {X Y : C} (f : X ⟶ Y) : (toZeroArrow e |>.map f).left = f := rfl

theorem toZeroArrow_map_right (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A)
    {X Y : C} (f : X ⟶ Y) : (toZeroArrow e |>.map f).right = 𝟙 (object e) := rfl

/-- The original counit compares the complete mapped zero-to-object source arrow. -/
def fromZeroArrowObjIso (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (X : C) :
    e.functor.mapArrow.obj ((fromZeroArrow e).obj X) ≅
      Native.Diagrams.fromZeroArrow.obj (e.functor.obj X) :=
  Arrow.isoMk (comparisonIso e) (Iso.refl (e.functor.obj X))
    ((mapped_isZero e).eq_of_src _ _)

/-- The original counit compares the complete mapped object-to-zero source arrow. -/
def toZeroArrowObjIso (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (X : C) :
    e.functor.mapArrow.obj ((toZeroArrow e).obj X) ≅
      Native.Diagrams.toZeroArrow.obj (e.functor.obj X) :=
  Arrow.isoMk (Iso.refl (e.functor.obj X)) (comparisonIso e)
    (Native.Diagrams.zeroDiagram_isZero.eq_of_tgt _ _)

/-- Whole-functor counit comparison of the original source and native I input arrows. -/
def fromZeroArrowIso (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    fromZeroArrow e ⋙ e.functor.mapArrow ≅ e.functor ⋙ Native.Diagrams.fromZeroArrow :=
  NatIso.ofComponents (fromZeroArrowObjIso e) (by
    intro X Y f
    apply Arrow.hom_ext
    · change e.functor.map (𝟙 (object e)) ≫ (comparisonIso e).hom =
        (comparisonIso e).hom ≫ 𝟙 Native.Diagrams.zeroDiagram
      rw [e.functor.map_id, Category.id_comp, Category.comp_id]
    · change e.functor.map f ≫ 𝟙 (e.functor.obj Y) = 𝟙 (e.functor.obj X) ≫ e.functor.map f
      exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- Whole-functor counit comparison of the original source and native J input arrows. -/
def toZeroArrowIso (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    toZeroArrow e ⋙ e.functor.mapArrow ≅ e.functor ⋙ Native.Diagrams.toZeroArrow :=
  NatIso.ofComponents (toZeroArrowObjIso e) (by
    intro X Y f
    apply Arrow.hom_ext
    · change e.functor.map f ≫ 𝟙 (e.functor.obj Y) = 𝟙 (e.functor.obj X) ≫ e.functor.map f
      exact (Category.comp_id _).trans (Category.id_comp _).symm
    · change e.functor.map (𝟙 (object e)) ≫ (comparisonIso e).hom =
        (comparisonIso e).hom ≫ 𝟙 Native.Diagrams.zeroDiagram
      rw [e.functor.map_id, Category.id_comp, Category.comp_id])

theorem fromZeroArrowIso_hom_app_left (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A)
    (X : C) : ((fromZeroArrowIso e).hom.app X).left = e.counitIso.hom.app
      Native.Diagrams.zeroDiagram := rfl

theorem fromZeroArrowIso_hom_app_right (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A)
    (X : C) : ((fromZeroArrowIso e).hom.app X).right = 𝟙 (e.functor.obj X) := rfl

theorem toZeroArrowIso_hom_app_left (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A)
    (X : C) : ((toZeroArrowIso e).hom.app X).left = 𝟙 (e.functor.obj X) := rfl

theorem toZeroArrowIso_hom_app_right (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A)
    (X : C) : ((toZeroArrowIso e).hom.app X).right = e.counitIso.hom.app Native.Diagrams.zeroDiagram
      := rfl

end HomotopicalAlgebra.EnrichedProjective.NativePresentation.Zero
