/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalPlainReedyRestriction
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFixedFrontReedyOrdinalComparison
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalPointedMappingGadgets
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalPointedGadgetInputs

/-!
# Every SAME original fixed-front degree is an actual mapping gadget

The original pointed constant-front augmentation followed by its
actual zero-quotient isomorphism is categorical weak and retains both
original ordinal endpoints. The proved ordinal source geometry gives
both independent original coefficient point properties. All full
original operators and input maps are retained.
-/

noncomputable section

universe u

open CategoryTheory Opposite MorphismProperty

namespace CategoryTheory.CoherentRealization.OriginalFixedFrontContraction

/-- The SAME original fixed-front degree maps by its actual augmentation to the original walking arrow. -/
def fixedFrontWalkingMap (n : SimplexCategory) : plainFixedFrontDiagram.{u}.obj n ⟶ walkingArrowPointed.{u} :=
  pointedAugmentation.app n ≫ pointedZeroIso.hom

/-- The actual entire original fixed-front augmentation gives genuine original ordinal comparison data with both same
endpoints. -/
def fixedFrontOrdinalComparison (n : SimplexCategory) :
    OriginalPointed.OrdinalComparison (plainFixedFrontDiagram.{u}.obj n) where
  dimension := 1
  map := (fixedFrontWalkingMap n).right
  categorical := RespectsIso.postcomp SSet.categoricalEquivalences zeroObjectIso.hom
    (pointedAugmentation.app n).right (pointedAugmentation_right_categoricalEquivalence n)
  source := (OriginalPointed.source_map (fixedFrontWalkingMap n)).trans walkingArrowPointed_source
  target := (OriginalPointed.target_map (fixedFrontWalkingMap n)).trans walkingArrowPointed_target

/-- Every same original complete fixed-front degree is a genuine original mapping gadget. -/
theorem fixedFrontDegree_mappingGadget (n : SimplexCategory) :
    OriginalPointed.mappingGadgetProperty (plainFixedFrontDiagram.{u}.obj n) :=
  OriginalPointed.mappingGadgetProperty_of_ordinal _ (fixedFrontOrdinalComparison n)

/-- The full original fixed-front diagram retains every original object and operator in the actual full gadget
category. -/
def fixedFrontGadgetDiagram : CosimplicialObject OriginalPointed.MappingGadgets.{u} where
  obj n := ⟨plainFixedFrontDiagram.obj n, fixedFrontDegree_mappingGadget n⟩
  map θ := ObjectProperty.homMk (plainFixedFrontDiagram.map θ)
  map_id n := by apply ObjectProperty.hom_ext; exact plainFixedFrontDiagram.map_id n
  map_comp θ ψ := by apply ObjectProperty.hom_ext; exact plainFixedFrontDiagram.map_comp θ ψ

/-- Every same original complete fixed-front input retains its whole original map in the full gadget category. -/
def fixedFrontIntoGadgetInputs (X : OriginalPointed.Category.{u}) :
    CostructuredArrow plainFixedFrontDiagram X ⥤ CostructuredArrow OriginalPointed.gadgetInclusion X :=
  CostructuredArrow.pre fixedFrontGadgetDiagram OriginalPointed.gadgetInclusion X

end CategoryTheory.CoherentRealization.OriginalFixedFrontContraction
