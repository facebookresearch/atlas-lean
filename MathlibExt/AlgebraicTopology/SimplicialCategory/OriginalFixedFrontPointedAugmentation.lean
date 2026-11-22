/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFixedFrontPointedDiagram

/-!
# The SAME original pointed fixed-front augmentation

The full original constant-front maps give a natural augmentation in
Under(∂Δ[1]) to the SAME zero quotient. Its underlying maps are the
original checked categorical equivalences, with both original endpoint
equations retained.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFixedFrontContraction

/-- The SAME full original fixed-front augmentation retaining both original endpoints. -/
def pointedAugmentation :
    pointedCosimplicialObject.{u} ⟶ (Functor.const SimplexCategory).obj (pointedObject.{u} 0) where
  app n := pointedMap (SimplexCategory.const n ⦋0⦌ 0)
  naturality n m θ := by
    apply Under.UnderMorphism.ext
    change FixedFrontOperators.map θ ≫ toZero m.len = toZero n.len ≫ 𝟙 (FixedFrontCollapse.object.{u} 0)
    exact (toZero_operator θ).trans (Category.comp_id _).symm

/-- Every original pointed augmentation degree retains the SAME actual constant-front map. -/
theorem pointedAugmentation_right (n : SimplexCategory) :
    (pointedAugmentation.{u}.app n).right = toZero n.len := rfl

/-- Every SAME original pointed augmentation degree has its genuinely weak underlying original quotient map. -/
theorem pointedAugmentation_right_categoricalEquivalence (n : SimplexCategory) :
    SSet.categoricalEquivalences (pointedAugmentation.{u}.app n).right :=
  toZero_categoricalEquivalence n.len

end CategoryTheory.CoherentRealization.OriginalFixedFrontContraction
