/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalRightMappingArbitraryPointedHom
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalRightMappingReedyTargetClasses
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalPointedFibrantGadgetMappingPoint

/-!
# Genuine original Reedy Hom point weakness at every fibrant mapping gadget

The actual copied original target is genuinely fibrant. The full
original generated restriction is a Kan trivial fibration to its same
fixed-front Hom diagram. The exact original right-mapping Iso and
independent genuine gadget point condition then prove the actual Reedy
Hom point map weak. All original maps and scalar operators are retained.
-/

noncomputable section

universe u

open CategoryTheory Opposite HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

attribute [local instance] JoyalSSet.modelCategory

namespace CategoryTheory.CoherentRealization.OriginalRawRightMapping

open OriginalFixedFrontContraction

/-- The same actual Reedy Hom diagram at the entire original pointed gadget target. -/
def gadgetReedyHom (X : OriginalPointed.FibrantMappingGadgets.{u}) : SSet.{u} :=
  reedyHomFunctor.obj (pointedCopyFunctor.obj X.obj.obj)

/-- The full original generated restriction into the same original gadget right-mapping space. -/
def gadgetReedyRightComparison (X : OriginalPointed.FibrantMappingGadgets.{u}) :
    gadgetReedyHom X ⟶ SSet.mappingSpaceRight X.obj.obj.right
      (OriginalPointed.source X.obj.obj) (OriginalPointed.target X.obj.obj) :=
  reedyHomTransformation.app (pointedCopyFunctor.obj X.obj.obj) ≫ (arbitraryPointedHomIso X.obj.obj).inv

/-- The actual original Reedy Hom restriction at every genuine fibrant gadget is weak. -/
theorem gadgetReedyRightComparison_weak (X : OriginalPointed.FibrantMappingGadgets.{u}) :
    SSet.realizationWeakEquivalences (gadgetReedyRightComparison X) := by
  let _ : IsFibrant (pointedCopyFunctor.obj X.obj.obj) :=
    (isFibrant_under_iff _ _).mpr ((JoyalSSet.isFibrant_iff_quasicategory _).mpr X.property)
  have h := (reedyHomTransformation_trivialFibration (pointedCopyFunctor.obj X.obj.obj)).2
  exact SSet.realizationWeakEquivalences.comp_mem _ _ h
    (SSet.realizationWeakEquivalences.of_isIso (arbitraryPointedHomIso X.obj.obj).inv)

/-- The same full actual original Reedy Hom at every genuinely fibrant gadget has weak point projection. -/
theorem gadgetReedyHom_point_weak (X : OriginalPointed.FibrantMappingGadgets.{u}) :
    SSet.realizationWeakEquivalences (SSet.stdSimplex.isTerminalObj₀.from (gadgetReedyHom X)) := by
  have h := SSet.realizationWeakEquivalences.comp_mem _ _ (gadgetReedyRightComparison_weak X)
    (OriginalPointed.fibrantGadgetRightMapping_point_weak X)
  have he : gadgetReedyRightComparison X ≫ SSet.stdSimplex.isTerminalObj₀.from
      (SSet.mappingSpaceRight X.obj.obj.right (OriginalPointed.source X.obj.obj) (OriginalPointed.target X.obj.obj)) =
      SSet.stdSimplex.isTerminalObj₀.from (gadgetReedyHom X) := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  exact he ▸ h

end CategoryTheory.CoherentRealization.OriginalRawRightMapping
