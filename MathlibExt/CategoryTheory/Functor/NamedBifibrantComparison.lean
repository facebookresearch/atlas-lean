/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.CategoryTheory.Functor.BifibrantComparison

set_option autoImplicit false
noncomputable section
universe u v u' v'
open CategoryTheory

namespace CategoryTheory
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- Both given composite comparisons retain the actual named bifibrant functors and all maps. -/
def originalNamedBifibrantComparison (Q R B : C ⥤ C) (Q' R' B' : D ⥤ D) (F : C ⥤ D)
    (cQ : Q ⋙ F ≅ F ⋙ Q') (cR : R ⋙ F ≅ F ⋙ R')
    (cB : B ≅ Q ⋙ R) (cB' : B' ≅ Q' ⋙ R') : B ⋙ F ≅ F ⋙ B' :=
  Functor.isoWhiskerRight cB F ≪≫ originalBifibrantComparison Q R Q' R' F cQ cR ≪≫
    Functor.isoWhiskerLeft F cB'.symm

/-- The actual named bifibrant forward component retains all original comparison factors. -/
theorem originalNamedBifibrantComparison_hom_app
    (Q R B : C ⥤ C) (Q' R' B' : D ⥤ D) (F : C ⥤ D)
    (cQ : Q ⋙ F ≅ F ⋙ Q') (cR : R ⋙ F ≅ F ⋙ R')
    (cB : B ≅ Q ⋙ R) (cB' : B' ≅ Q' ⋙ R') (X : C) :
    (originalNamedBifibrantComparison Q R B Q' R' B' F cQ cR cB cB').hom.app X =
      F.map (cB.hom.app X) ≫
        ((cR.hom.app (Q.obj X) ≫ R'.map (cQ.hom.app X)) ≫ cB'.inv.app (F.obj X)) := rfl

/-- The actual inverse retains the same named and composite factors in reverse order. -/
theorem originalNamedBifibrantComparison_inv_app
    (Q R B : C ⥤ C) (Q' R' B' : D ⥤ D) (F : C ⥤ D)
    (cQ : Q ⋙ F ≅ F ⋙ Q') (cR : R ⋙ F ≅ F ⋙ R')
    (cB : B ≅ Q ⋙ R) (cB' : B' ≅ Q' ⋙ R') (X : C) :
    (originalNamedBifibrantComparison Q R B Q' R' B' F cQ cR cB cB').inv.app X =
      (cB'.hom.app (F.obj X) ≫
        (R'.map (cQ.inv.app X) ≫ cR.inv.app (Q.obj X))) ≫ F.map (cB.inv.app X) := rfl

end CategoryTheory
