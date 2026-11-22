/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFixedFrontReedyWeakAugmentation
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalPointedCoherentHomFunctor
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalNecklaceRawCoefficientContractible

/-!
# Actual raw endpoint Hom point weakness of the same original Reedy degrees

The genuine original pointed augmentation gives the same actual
categorical weak projection of each generated degree. Original
coherent Hom weak preservation retains both original endpoints. The
original zero quotient is the walking arrow, whose full Hom is the
same native interval coefficient point. No degree fibrancy is inferred
from a weak map.
-/

noncomputable section

universe u

open CategoryTheory Opposite MorphismProperty
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFixedFrontContraction

/-- The same complete original Reedy degree with its original pointed boundary, forgetting only the carrier
designation. -/
def rawReedyDegree (n : SimplexCategory) : OriginalPointed.Category.{u} :=
  pointedRawFunctor.obj (reedyReplacement.obj n)

/-- The original pointed zero quotient, retaining both actual original quotient endpoints. -/
def rawZeroPointed : OriginalPointed.Category.{u} := pointedObject.{u} 0

/-- Every same generated projection retains the original full zero-quotient target. -/
def rawReedyProjection (n : SimplexCategory) : rawReedyDegree.{u} n ⟶ rawZeroPointed.{u} :=
  pointedRawFunctor.map (reedyReplacementProjection.app n)

/-- The same actual raw endpoint Hom map of every generated projection is weak, with no inferred degree fibrancy. -/
theorem rawReedyProjection_hom_weak (n : SimplexCategory) :
    SSet.realizationWeakEquivalences (OriginalPointed.homMap (rawReedyProjection.{u} n)) :=
  OriginalPointed.homMap_weak _ (reedyReplacementProjection_app_categorical n)

end CategoryTheory.CoherentRealization.OriginalFixedFrontContraction
