/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CarrierLimitUniversal

/-!
# Actual small varying-object enriched limits and their object readback

The complete original compatible-object/full-Hom universal property
constructs every supported small enriched limit. The SAME original
object-forgetting functor preserves these limits by the actual original
vertex equivalence of their whole cones. This supplies finite limits
for the original global Bergner model prerequisites without assuming
a changing-object model structure.
-/

noncomputable section
universe u v
open CategoryTheory Limits

namespace CategoryTheory.SimplicialEnrichment.CarrierLimit
open FixedObjects

variable {J : Type v} [SmallCategory J] (F : J ⥤ Carrier.{u})
variable [HasLimit (F ⋙ forgetObjects)] [HasLimitsOfShape J SSet.{u}]

/-- The original object cone of the actual full enriched limit is genuinely the SAME
original object limit. -/
def objectConeIsLimit : IsLimit (forgetObjects.mapCone (cone F)) := by
  apply IsLimit.ofIsoLimit (limit.isLimit (F ⋙ forgetObjects))
  refine Cone.ext (verticesEquiv (fixedObject F)).toIso ?_
  intro j
  apply ConcreteCategory.hom_ext
  intro x
  exact projection_obj F j x

/-- The SAME original object-forgetting functor preserves the complete genuine enriched limit. -/
instance forgetObjectsPreservesLimit : PreservesLimit F forgetObjects :=
  preservesLimit_of_preserves_limit_cone (isLimit F) (objectConeIsLimit F)

/-- Original object and scalar limits give genuine changing-object enriched limits of the
full supported shape. -/
instance hasLimitsOfShape [HasLimitsOfShape J (Type u)] : HasLimitsOfShape J Carrier.{u} where
  has_limit F := ⟨⟨cone F, isLimit F⟩⟩

/-- Original object forgetting preserves every entire enriched limit of the supported
indexing shape. -/
instance forgetObjectsPreservesLimitsOfShape [HasLimitsOfShape J (Type u)] :
    PreservesLimitsOfShape J forgetObjects.{u} where
  preservesLimit {F} := forgetObjectsPreservesLimit F

/-- Every small diagram has its genuinely constructed original varying-object enriched limit. -/
instance hasSmallLimits : HasLimitsOfSize.{u, u} Carrier.{u} where
  has_limits_of_shape _J _ := inferInstance

/-- The SAME original object-forgetting functor preserves all small enriched limits. -/
instance forgetObjectsPreservesSmallLimits : PreservesLimitsOfSize.{u, u} forgetObjects.{u} where
  preservesLimitsOfShape := inferInstance

/-- The actual original global enriched carrier has all finite limits required by the
model-category axioms. -/
theorem hasFiniteLimits_original : HasFiniteLimits Carrier.{u} := inferInstance

end CategoryTheory.SimplicialEnrichment.CarrierLimit
