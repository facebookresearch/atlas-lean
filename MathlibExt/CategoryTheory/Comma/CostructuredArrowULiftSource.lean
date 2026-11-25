/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import MathlibExt.CategoryTheory.NerveULiftObject

/-!
# Whole original comma categories under an actual source-object lift

Every full original comma object and arrow is retained inside the
canonical ULift source tag. The actual original full inverse categorical
functors and their natural comparison maps preserve the same triangles.
-/

@[expose] public section


noncomputable section

universe uA uB v w

open CategoryTheory Opposite

attribute [local instance] CategoryTheory.uliftCategory

namespace CategoryTheory

variable {A : Type uA} {B : Type uB} [Category.{v} A] [Category.{v} B]

/-- The same entire original comma over a source-object lift has both full inverse functors. -/
def costructuredArrowULiftSourceEquivalence (F : A ⥤ B) (b : B) :
    CostructuredArrow (ULift.downFunctor.{v,uA,w} (C := A) ⋙ F) b ≌ ULift.{w}
      (CostructuredArrow F b) where
  functor :=
    { obj X := ULift.up (CostructuredArrow.mk (Y := X.left.down) X.hom)
      map f := CostructuredArrow.homMk f.left (CostructuredArrow.w f)
      map_id X := by apply CostructuredArrow.hom_ext; rfl
      map_comp f g := by apply CostructuredArrow.hom_ext; rfl }
  inverse :=
    { obj X := CostructuredArrow.mk (Y := ULift.up X.down.left) X.down.hom
      map f := CostructuredArrow.homMk f.left (CostructuredArrow.w f)
      map_id X := by apply CostructuredArrow.hom_ext; rfl
      map_comp f g := by apply CostructuredArrow.hom_ext; rfl }
  unitIso := NatIso.ofComponents (fun X => CostructuredArrow.eta X)
    (by intro X Y f; apply CostructuredArrow.hom_ext; exact (Category.comp_id _).trans
          (Category.id_comp _).symm)
  counitIso := NatIso.ofComponents (fun X =>
    (ULift.upFunctor (C := CostructuredArrow F b)).mapIso (CostructuredArrow.eta X.down).symm)
    (by intro X Y f; exact (Category.comp_id _).trans (Category.id_comp _).symm)
  functor_unitIso_comp X := by
    apply CostructuredArrow.hom_ext
    change 𝟙 X.left.down ≫ 𝟙 X.left.down = 𝟙 X.left.down
    exact Category.id_comp _

end CategoryTheory
