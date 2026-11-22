/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalPointedCosimplicialHomIso
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalReedyPointedHomIso
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalRightMappingReedyTargetClasses

/-!
# The SAME original plain pointed Reedy Hom restriction is weak

The actual generated Reedy map retains the full original pointed
sources and scalar Hom maps. Its genuine original relative-matching
trivial fibration and both full copy/forget dictionaries prove weakness
at every original quasicategory target. No comparison outcome is input.
-/

noncomputable section

universe u

open CategoryTheory Opposite HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

attribute [local instance] JoyalSSet.modelCategory

namespace CategoryTheory.CoherentRealization.OriginalFixedFrontContraction

/-- The SAME entire original plain pointed fixed-front diagram. -/
def plainFixedFrontDiagram : CosimplicialObject OriginalPointed.Category.{u} :=
  pointedJoyalDiagram ⋙ pointedRawFunctor

/-- The SAME original generated Reedy map retains the full original pointed quotient and replacement objects. -/
def plainReedyMap : plainFixedFrontDiagram.{u} ⟶ plainReedyDiagram.{u} :=
  Functor.whiskerRight reedyReplacementMap pointedRawFunctor

/-- The SAME actual original plain Hom restriction along its generated full Reedy map. -/
def plainReedyHomRestriction (X : OriginalPointed.Category.{u}) :
    CosimplicialObject.homSpace plainReedyDiagram X ⟶
      CosimplicialObject.homSpace plainFixedFrontDiagram X :=
  Functor.whiskerRight (NatTrans.op plainReedyMap) (yoneda.obj X)

/-- Every complete original scalar Hom map restricts by the same entire generated original pointed map. -/
theorem plainReedyHomRestriction_app (X : OriginalPointed.Category.{u})
    (n : SimplexCategory) (g : plainReedyDiagram.obj n ⟶ X) :
    (plainReedyHomRestriction X).app (op n) g = plainReedyMap.app n ≫ g := rfl

/-- The same original named-target comparison is exactly restriction along the same full original generated Reedy
map. -/
theorem reedyHomTransformation_eq_restriction (X : PointedJoyal.{u}) :
    OriginalRawRightMapping.reedyHomTransformation.app X =
      Functor.whiskerRight (NatTrans.op reedyReplacementMap) (yoneda.obj X) := by
  apply SSet.hom_ext
  intro q
  apply ConcreteCategory.hom_ext
  intro g
  apply Under.UnderMorphism.ext
  rfl

/-- The SAME actual original plain pointed Reedy Hom restriction is weak at every original quasicategory target. -/
theorem plainReedyHomRestriction_weak (X : OriginalPointed.Category.{u}) [SSet.Quasicategory X.right] :
    SSet.realizationWeakEquivalences (plainReedyHomRestriction X) := by
  let JX := pointedCopyFunctor.obj X
  let _ : IsFibrant JX := (isFibrant_under_iff _ JX).mpr
    ((JoyalSSet.isFibrant_iff_quasicategory JX.right).mpr
      (show SSet.Quasicategory JX.right.toSSet from ‹SSet.Quasicategory X.right›))
  have hJ := (OriginalRawRightMapping.reedyHomTransformation_trivialFibration JX).2
  have hRestriction : SSet.realizationWeakEquivalences
      (Functor.whiskerRight (NatTrans.op reedyReplacementMap) (yoneda.obj JX)) :=
    reedyHomTransformation_eq_restriction JX ▸ hJ
  have hSquare := pointedCosimplicialHomIso_restriction reedyReplacementMap X
  have hComposite := SSet.realizationWeakEquivalences.comp_mem _ _ hRestriction
    (SSet.realizationWeakEquivalences.of_isIso (pointedCosimplicialHomIso pointedJoyalDiagram X).hom)
  exact SSet.realizationWeakEquivalences.of_precomp _ _
    (SSet.realizationWeakEquivalences.of_isIso (pointedCosimplicialHomIso reedyReplacement X).hom)
    (hSquare ▸ hComposite)

end CategoryTheory.CoherentRealization.OriginalFixedFrontContraction
