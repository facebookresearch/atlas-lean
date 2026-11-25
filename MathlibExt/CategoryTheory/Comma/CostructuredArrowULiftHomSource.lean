/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.NerveULiftHom
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-!
# Full original comma dictionary under source Hom universe lift

Every full original comma triangle is retained. The canonical source
Hom lift tags each original arrow, and both original inverse functors
lift or lower that same arrow without changing its object map.
-/

@[expose] public section


noncomputable section

universe uA uB vA vB w

open CategoryTheory

namespace CategoryTheory

variable {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]

/-- Both full original comma directions compare a source Hom-lift with the actual full
original comma Hom-lift. -/
def costructuredArrowULiftHomSourceEquivalence (F : A ⥤ B) (b : B) :
    CostructuredArrow (ULiftHom.down.{vA,uA,w} (C := A) ⋙ F) b ≌ ULiftHom.{w}
      (CostructuredArrow F b) where
  functor :=
    { obj X := ULiftHom.objUp (CostructuredArrow.mk (Y := X.left.objDown) X.hom)
      map f := ULift.up (CostructuredArrow.homMk f.left.down (CostructuredArrow.w f))
      map_id X := by apply ULift.ext; apply CostructuredArrow.hom_ext; rfl
      map_comp f g := by apply ULift.ext; apply CostructuredArrow.hom_ext; rfl }
  inverse :=
    { obj X := CostructuredArrow.mk (Y := ULiftHom.objUp X.objDown.left) X.objDown.hom
      map f := CostructuredArrow.homMk (ULift.up f.down.left) (CostructuredArrow.w f.down)
      map_id X := by apply CostructuredArrow.hom_ext; rfl
      map_comp f g := by apply CostructuredArrow.hom_ext; rfl }
  unitIso := NatIso.ofComponents (fun X => CostructuredArrow.eta X)
    (by intro X Y f; apply CostructuredArrow.hom_ext; exact (Category.comp_id _).trans
          (Category.id_comp _).symm)
  counitIso := NatIso.ofComponents (fun X =>
    (ULiftHom.up.{vA,max uA vB,w} (C := CostructuredArrow F b)).mapIso
      (CostructuredArrow.eta X.objDown).symm)
    (by intro X Y f; apply ULift.ext; exact (Category.comp_id _).trans (Category.id_comp _).symm)
  functor_unitIso_comp X := by
    apply ULift.ext
    apply CostructuredArrow.hom_ext
    exact Category.id_comp _

end CategoryTheory
