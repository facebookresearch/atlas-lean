/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalPointedJoyalHomEquivalence
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalPointedCoherentHom
import MathlibExt.AlgebraicTopology.SimplicialObject.CosimplicialHomInputEquivalence

/-!
# The SAME full cosimplicial pointed Hom dictionary

The existing complete pointed copy/forget Hom equivalence retains
all original generated source objects and operators. Both full scalar
Hom directions commute with every original cosimplicial restriction.
-/

noncomputable section

universe u

open CategoryTheory Opposite

namespace CategoryTheory.CoherentRealization.OriginalFixedFrontContraction

/-- Both full original cosimplicial Hom directions are the existing actual pointed copy/forget dictionary. -/
def pointedCosimplicialHomIso (F : CosimplicialObject PointedJoyal.{u}) (X : OriginalPointed.Category.{u}) :
    F.op ⋙ yoneda.obj (pointedCopyFunctor.obj X) ≅
      CosimplicialObject.homSpace (F ⋙ pointedRawFunctor) X :=
  NatIso.ofComponents (fun q => (pointedRawHomEquiv (F.obj q.unop) X).toIso)
    (by intro q r θ; apply ConcreteCategory.hom_ext; intro g; apply Under.UnderMorphism.ext; rfl)

/-- Every same original cosimplicial restriction commutes with both complete original Hom dictionary directions. -/
theorem pointedCosimplicialHomIso_restriction
    {F G : CosimplicialObject PointedJoyal.{u}} (α : F ⟶ G) (X : OriginalPointed.Category.{u}) :
    Functor.whiskerRight (NatTrans.op α) (yoneda.obj (pointedCopyFunctor.obj X)) ≫
        (pointedCosimplicialHomIso F X).hom =
      (pointedCosimplicialHomIso G X).hom ≫
        Functor.whiskerRight (NatTrans.op (Functor.whiskerRight α pointedRawFunctor)) (yoneda.obj X) := by
  apply SSet.hom_ext
  intro q
  apply ConcreteCategory.hom_ext
  intro g
  apply Under.UnderMorphism.ext
  rfl

end CategoryTheory.CoherentRealization.OriginalFixedFrontContraction
