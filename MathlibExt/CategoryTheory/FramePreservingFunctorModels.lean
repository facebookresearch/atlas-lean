/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.CategoryTheory.Whiskering

/-!
# Native functors preserving a displayed frame square

This generic diagram helper retains the actual functor, its underlying
object/arrow comparison and the entire frame compatibility square.
Applications supply the original sites, pullbacks and frame maps; the
helper adds no object carrier or geometric comparison of its own.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.FramePreservingFunctorModels

open _root_.CategoryTheory

universe uA uB uC uD uX uY vA vB vC vD vX vY

variable {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
  {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {X : Type uX} [Category.{vX} X] {Y : Type uY} [Category.{vY} Y]

/-- A native functor preserving both the original action and full frame diagram. -/
structure FrameMap (i : A ⥤ B) (r : A ⥤ C) (s : B ⥤ D) (t : C ⥤ D)
    (square : i ⋙ s ≅ r ⋙ t) (x : X ⥤ A) (y : Y ⥤ B)
    (targetX : X ⥤ C) (targetY : Y ⥤ D) (target : X ⥤ D)
    (frameX : x ⋙ r ≅ targetX) (frameY : y ⋙ s ≅ targetY)
    (regular : targetX ⋙ t ≅ target)
    (targetIdentification : ∀ F : X ⥤ Y, F ⋙ targetY ≅ target) where
  functor : X ⥤ Y
  onActions : functor ⋙ y ≅ x ⋙ i
  onFrames :
    (Functor.associator functor y s).hom ≫
        (Functor.isoWhiskerLeft functor frameY).hom ≫
          (targetIdentification functor).hom =
      (Functor.isoWhiskerRight onActions s).hom ≫
        (Functor.associator x i s).hom ≫ (Functor.isoWhiskerLeft x square).hom ≫
          (Functor.associator x r t).inv ≫ (Functor.isoWhiskerRight frameX t).hom ≫
            regular.hom

end MathlibExt.CategoryTheory.FramePreservingFunctorModels
