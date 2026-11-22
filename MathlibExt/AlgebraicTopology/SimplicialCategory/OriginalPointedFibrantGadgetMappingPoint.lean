/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalPointedFibrantGadgets
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalRightMappingReedyWeak

/-!
# Genuine original mapping point properties of every full fibrant gadget

The same original unit is categorical weak between actual original
quasicategories. Its full original right-map therefore is weak. The
independent replacement point property descends to the same original
right-mapping space, without assuming the original raw comparison.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalPointed

/-- The same full actual right-mapping unit of every genuinely fibrant original gadget. -/
def fibrantGadgetRightUnit (X : FibrantMappingGadgets.{u}) :
    SSet.mappingSpaceRight X.obj.obj.right (source X.obj.obj) (target X.obj.obj) ⟶
      replacementRightMapping X.obj.obj :=
  SSet.mappingSpaceRight.map _ _ _ (replacementUnit.app X.obj.obj).right ≫
    (SSet.PointedRightMappingSpace.endpointIso (source_map (replacementUnit.app X.obj.obj))
      (target_map (replacementUnit.app X.obj.obj))).hom

/-- The same actual right-mapping unit of the full original fibrant gadget is genuinely weak. -/
theorem fibrantGadgetRightUnit_weak (X : FibrantMappingGadgets.{u}) :
    SSet.realizationWeakEquivalences (fibrantGadgetRightUnit X) := by
  let _ : SSet.Quasicategory ((𝟭 Category.{u}).obj X.obj.obj).right := by
    change SSet.Quasicategory X.obj.obj.right
    exact X.property
  let _ : SSet.Quasicategory (replacementFunctor.obj X.obj.obj).right := replacement_quasicategory X.obj.obj
  exact SSet.realizationWeakEquivalences.comp_mem _ _
    ((replacementUnit_categorical X.obj.obj).rightMappingSpaceMap_weak (source X.obj.obj) (target X.obj.obj))
    (SSet.realizationWeakEquivalences.of_isIso
      (SSet.PointedRightMappingSpace.endpointIso (source_map (replacementUnit.app X.obj.obj))
        (target_map (replacementUnit.app X.obj.obj))).hom)

/-- The same full original right-mapping point map of every genuinely fibrant gadget is weak. -/
theorem fibrantGadgetRightMapping_point_weak (X : FibrantMappingGadgets.{u}) :
    SSet.realizationWeakEquivalences (SSet.stdSimplex.isTerminalObj₀.from
      (SSet.mappingSpaceRight X.obj.obj.right (source X.obj.obj) (target X.obj.obj))) := by
  have h := SSet.realizationWeakEquivalences.comp_mem _ _ (fibrantGadgetRightUnit_weak X) X.obj.property.2
  have he : fibrantGadgetRightUnit X ≫ SSet.stdSimplex.isTerminalObj₀.from (replacementRightMapping X.obj.obj) =
      SSet.stdSimplex.isTerminalObj₀.from
        (SSet.mappingSpaceRight X.obj.obj.right (source X.obj.obj) (target X.obj.obj)) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  exact he ▸ h

end CategoryTheory.CoherentRealization.OriginalPointed
