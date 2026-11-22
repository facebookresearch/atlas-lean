/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalPointedMappingGadgets

/-!
# Actual canonical replacement closure of the original mapping gadgets

The same original raw Hom unit is weak. The full original replacement
right map is categorical weak between actual quasicategory carriers,
so its original right-mapping functor is weak. Both independent point
conditions are retained by the actual original replacement object.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalPointed

/-- The same actual canonical replacement right-mapping unit between genuine original quasicategories. -/
def replacementRightMappingUnit (X : Category.{u}) :
    replacementRightMapping X ⟶ replacementRightMapping (replacementFunctor.obj X) :=
  SSet.mappingSpaceRight.map _ _ _ (replacementUnit.app (replacementFunctor.obj X)).right ≫
    (SSet.PointedRightMappingSpace.endpointIso (source_map (replacementUnit.app (replacementFunctor.obj X)))
      (target_map (replacementUnit.app (replacementFunctor.obj X)))).hom

/-- The same actual full original replacement right-mapping unit is genuinely weak. -/
theorem replacementRightMappingUnit_weak (X : Category.{u}) :
    SSet.realizationWeakEquivalences (replacementRightMappingUnit X) := by
  let _ : SSet.Quasicategory ((𝟭 Category.{u}).obj (replacementFunctor.obj X)).right := by
    change SSet.Quasicategory (replacementFunctor.obj X).right
    exact replacement_quasicategory X
  let _ : SSet.Quasicategory (replacementFunctor.obj (replacementFunctor.obj X)).right :=
    replacement_quasicategory (replacementFunctor.obj X)
  exact SSet.realizationWeakEquivalences.comp_mem _ _
    ((replacementUnit_categorical (replacementFunctor.obj X)).rightMappingSpaceMap_weak
      (source (replacementFunctor.obj X)) (target (replacementFunctor.obj X)))
    (SSet.realizationWeakEquivalences.of_isIso
      (SSet.PointedRightMappingSpace.endpointIso (source_map (replacementUnit.app (replacementFunctor.obj X)))
        (target_map (replacementUnit.app (replacementFunctor.obj X)))).hom)

/-- Both independent original gadget point conditions are preserved by the same actual canonical replacement. -/
theorem mappingGadgetProperty_replacement (X : Category.{u}) (hX : mappingGadgetProperty X) :
    mappingGadgetProperty (replacementFunctor.obj X) := by
  constructor
  · have he : homMap (replacementUnit.app X) ≫ SSet.stdSimplex.isTerminalObj₀.from
        (homObject (replacementFunctor.obj X)) = SSet.stdSimplex.isTerminalObj₀.from (homObject X) :=
      SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    exact SSet.realizationWeakEquivalences.of_precomp (homMap (replacementUnit.app X)) _
      (replacementUnit_hom_weak X) (he.symm ▸ hX.1)
  · have he : replacementRightMappingUnit X ≫ SSet.stdSimplex.isTerminalObj₀.from
        (replacementRightMapping (replacementFunctor.obj X)) =
          SSet.stdSimplex.isTerminalObj₀.from (replacementRightMapping X) := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    exact SSet.realizationWeakEquivalences.of_precomp (replacementRightMappingUnit X) _
      (replacementRightMappingUnit_weak X) (he.symm ▸ hX.2)

end CategoryTheory.CoherentRealization.OriginalPointed
