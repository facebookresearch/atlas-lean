/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalPointedOrdinalGadgets

/-!
# Actual right-mapping point weakness of original ordinal-source replacements

The canonical replacement preserves both whole original boundary maps.
Its actual ordinal extension reads back those exact endpoints and is
categorical weak. The established original right-mapping preservation
and literal full ordinal point iso prove genuine point weakness.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalPointed

open OriginalRawRightMapping

/-- The same actual ordinal extension retains its whole original replacement source endpoint. -/
theorem ordinalComparisonExtension_source (X : Category.{u}) (h : OrdinalComparison X) :
    source (replacementFunctor.obj X) ≫ ordinalComparisonExtension X h = simplexVertex h.dimension 0 := by
  have hs := source_map (replacementUnit.app X)
  exact (congrArg (fun f => f ≫ ordinalComparisonExtension X h) hs).symm.trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun f => source X ≫ f) (ordinalComparisonExtension_unit X h)).trans h.source))

/-- The same actual ordinal extension retains its whole original replacement target endpoint. -/
theorem ordinalComparisonExtension_target (X : Category.{u}) (h : OrdinalComparison X) :
    target (replacementFunctor.obj X) ≫ ordinalComparisonExtension X h =
      simplexVertex h.dimension (Fin.last h.dimension) := by
  have hs := target_map (replacementUnit.app X)
  exact (congrArg (fun f => f ≫ ordinalComparisonExtension X h) hs).symm.trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun f => target X ≫ f) (ordinalComparisonExtension_unit X h)).trans h.target))

/-- The same actual full original replacement right-mapping map into its ordinal space. -/
def ordinalReplacementRightMap (X : Category.{u}) (h : OrdinalComparison X) :
    SSet.mappingSpaceRight (replacementFunctor.obj X).right (source (replacementFunctor.obj X))
      (target (replacementFunctor.obj X)) ⟶
        SSet.mappingSpaceRight (Δ[h.dimension] : SSet.{u}) (simplexVertex h.dimension 0)
          (simplexVertex h.dimension (Fin.last h.dimension)) :=
  SSet.mappingSpaceRight.map _ _ _ (ordinalComparisonExtension X h) ≫
    (SSet.PointedRightMappingSpace.endpointIso (ordinalComparisonExtension_source X h)
      (ordinalComparisonExtension_target X h)).hom

/-- The same full original ordinal replacement right-mapping map is weak. -/
theorem ordinalReplacementRightMap_weak (X : Category.{u}) (h : OrdinalComparison X) :
    SSet.realizationWeakEquivalences (ordinalReplacementRightMap X h) := by
  let _ := replacement_quasicategory X
  exact SSet.realizationWeakEquivalences.comp_mem _ _
    ((ordinalComparisonExtension_categorical X h).rightMappingSpaceMap_weak
      (source (replacementFunctor.obj X)) (target (replacementFunctor.obj X)))
    (SSet.realizationWeakEquivalences.of_isIso
      (SSet.PointedRightMappingSpace.endpointIso (ordinalComparisonExtension_source X h)
        (ordinalComparisonExtension_target X h)).hom)

/-- The same original full ordinal-source replacement right-mapping point map is genuinely weak. -/
theorem ordinalReplacementRightMapping_point_weak (X : Category.{u}) (h : OrdinalComparison X) :
    SSet.realizationWeakEquivalences (SSet.stdSimplex.isTerminalObj₀.from
      (SSet.mappingSpaceRight (replacementFunctor.obj X).right
        (source (replacementFunctor.obj X)) (target (replacementFunctor.obj X)))) := by
  have hw := SSet.realizationWeakEquivalences.comp_mem _ _ (ordinalReplacementRightMap_weak X h)
    (simplexMappingPoint_weak (0 : Fin (h.dimension + 1)) (Fin.last h.dimension) (Fin.zero_le _))
  have he : ordinalReplacementRightMap X h ≫ SSet.stdSimplex.isTerminalObj₀.from
      (SSet.mappingSpaceRight (Δ[h.dimension] : SSet.{u}) (simplexVertex h.dimension 0)
        (simplexVertex h.dimension (Fin.last h.dimension))) =
      SSet.stdSimplex.isTerminalObj₀.from
        (SSet.mappingSpaceRight (replacementFunctor.obj X).right
          (source (replacementFunctor.obj X)) (target (replacementFunctor.obj X))) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  exact he ▸ hw

end CategoryTheory.CoherentRealization.OriginalPointed
