/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CarrierLimitUniversal

/-!
# Small limits of simplicial enrichments

A limit consists of compatible objects together with the corresponding
Hom limits. Object forgetting preserves these limits. In particular,
the category of simplicial enrichments has finite limits.
-/

noncomputable section
universe u v
open CategoryTheory Limits

namespace CategoryTheory.SimplicialEnrichment.CarrierLimit
open FixedObjects

variable {J : Type v} [SmallCategory J] (F : J ⥤ Carrier.{u})
variable [HasLimit (F ⋙ forgetObjects)] [HasLimitsOfShape J SSet.{u}]

/-- The object cone of the full enriched limit is genuinely the same
object limit. -/
def objectConeIsLimit : IsLimit (forgetObjects.mapCone (cone F)) := by
  apply IsLimit.ofIsoLimit (limit.isLimit (F ⋙ forgetObjects))
  refine Cone.ext (verticesEquiv (fixedObject F)).toIso ?_
  intro j
  apply ConcreteCategory.hom_ext
  intro x
  exact projection_obj F j x

/-- The same object-forgetting functor preserves the complete enriched limit. -/
instance forgetObjectsPreservesLimit : PreservesLimit F forgetObjects :=
  preservesLimit_of_preserves_limit_cone (isLimit F) (objectConeIsLimit F)

/-- Object and scalar limits give changing-object enriched limits of the
full supported shape. -/
instance hasLimitsOfShape [HasLimitsOfShape J (Type u)] : HasLimitsOfShape J Carrier.{u} where
  has_limit F := ⟨⟨cone F, isLimit F⟩⟩

/-- Object forgetting preserves every enriched limit of the supported
indexing shape. -/
instance forgetObjectsPreservesLimitsOfShape [HasLimitsOfShape J (Type u)] :
    PreservesLimitsOfShape J forgetObjects.{u} where
  preservesLimit {F} := forgetObjectsPreservesLimit F

/-- Every small diagram has its genuinely constructed varying-object enriched limit. -/
instance hasSmallLimits : HasLimitsOfSize.{u, u} Carrier.{u} where
  has_limits_of_shape _J _ := inferInstance

/-- The same object-forgetting functor preserves all small enriched limits. -/
instance forgetObjectsPreservesSmallLimits : PreservesLimitsOfSize.{u, u} forgetObjects.{u} where
  preservesLimitsOfShape := inferInstance

/-- The global enriched carrier has all finite limits required by the
model-category axioms. -/
theorem hasFiniteLimits_original : HasFiniteLimits Carrier.{u} := inferInstance

end CategoryTheory.SimplicialEnrichment.CarrierLimit
