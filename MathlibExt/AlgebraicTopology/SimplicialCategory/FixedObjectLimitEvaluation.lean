/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectLimits

/-!
# Original Hom evaluation preserves the actual enriched limits

The constructed enriched limit has the literal scalar limit Hom and
the same projection maps. The original evaluation cone is therefore
genuinely limiting. This includes the actual terminal object and every
small scalar limit supported by the original simplicial-set universe.
-/

noncomputable section
universe u v
open CategoryTheory Limits

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.HomLimit

variable {O : Type u} {J : Type v} [SmallCategory J] [HasLimitsOfShape J SSet.{u}]
  (F : J ⥤ FixedObjects O)

/-- The original evaluated enriched limit cone is the same actual scalar Hom limit cone. -/
def evaluatedIsLimit (x y : O) : IsLimit ((evaluation x y).mapCone (cone F)) := by
  apply IsLimit.ofIsoLimit (limit.isLimit (homDiagram F x y))
  refine Cone.ext (Iso.refl _) ?_
  intro j
  change 𝟙 _ ≫ homMap (projection F j) x y = limit.π (homDiagram F x y) j
  exact (Category.id_comp _).trans (homMap_projection F j x y)

/-- Every original fixed-label Hom evaluation preserves this entire genuine enriched limit. -/
instance evaluationPreservesLimit (x y : O) : PreservesLimit F (evaluation x y) :=
  preservesLimit_of_preserves_limit_cone (isLimit F) (evaluatedIsLimit F x y)

/-- Actual original Hom evaluation preserves all limits of the supported scalar indexing shape. -/
instance evaluationPreservesLimitsOfShape (x y : O) : PreservesLimitsOfShape J (evaluation x
  y) where
  preservesLimit {K} := evaluationPreservesLimit K x y

end CategoryTheory.SimplicialEnrichment.FixedObjects.HomLimit
