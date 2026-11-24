/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.CategoryTheory.MorphismProperty.Factorization.MiddleComparison
import Mathlib.CategoryTheory.MorphismProperty.Factorization

set_option autoImplicit false
noncomputable section
universe u v u' v'
open CategoryTheory
open CategoryTheory.MorphismProperty

namespace CategoryTheory
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- The original right-factor equation retains its whole Arrow and middle comparison. -/
theorem originalRightFactorCompatibility (F : C ⥤ D) (Z : Arrow D ⥤ D)
    (Z' : Arrow C ⥤ C) (p : Z ⟶ Arrow.rightFunc) (p' : Z' ⟶ Arrow.rightFunc)
    (A : C ⥤ Arrow C) (A' : D ⥤ Arrow D)
    (cZ : Z' ⋙ F ≅ F.mapArrow ⋙ Z) (cA : A ⋙ F.mapArrow ≅ F ⋙ A')
    (hcZ : ∀ a, cZ.hom.app a ≫ p.app (F.mapArrow.obj a) = F.map (p'.app a))
    (X : C) :
    (originalMiddleComparison F Z Z' A A' cZ cA).hom.app X ≫ p.app (A'.obj (F.obj X)) =
      F.map (p'.app (A.obj X)) ≫ (cA.hom.app X).right := by
  change (cZ.hom.app (A.obj X) ≫ Z.map (cA.hom.app X)) ≫
      p.app (A'.obj (F.obj X)) = _
  have h := p.naturality (cA.hom.app X)
  change Z.map (cA.hom.app X) ≫ p.app (A'.obj (F.obj X)) =
    p.app (F.mapArrow.obj (A.obj X)) ≫ (cA.hom.app X).right at h
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => cZ.hom.app (A.obj X) ≫ f) h).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun f => f ≫ (cA.hom.app X).right) (hcZ (A.obj X)))))

/-- The original left-factor equation retains the entire original Arrow-left comparison map. -/
theorem originalLeftFactorCompatibility (F : C ⥤ D) (Z : Arrow D ⥤ D)
    (Z' : Arrow C ⥤ C) (i : Arrow.leftFunc ⟶ Z) (i' : Arrow.leftFunc ⟶ Z')
    (A : C ⥤ Arrow C) (A' : D ⥤ Arrow D)
    (cZ : Z' ⋙ F ≅ F.mapArrow ⋙ Z) (cA : A ⋙ F.mapArrow ≅ F ⋙ A')
    (hcZ : ∀ a, F.map (i'.app a) ≫ cZ.hom.app a = i.app (F.mapArrow.obj a)) (X : C) :
    F.map (i'.app (A.obj X)) ≫
        (originalMiddleComparison F Z Z' A A' cZ cA).hom.app X =
      (cA.hom.app X).left ≫ i.app (A'.obj (F.obj X)) := by
  change F.map (i'.app (A.obj X)) ≫
    (cZ.hom.app (A.obj X) ≫ Z.map (cA.hom.app X)) = _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ Z.map (cA.hom.app X)) (hcZ (A.obj X))).trans
      (i.naturality (cA.hom.app X)).symm)

end CategoryTheory
