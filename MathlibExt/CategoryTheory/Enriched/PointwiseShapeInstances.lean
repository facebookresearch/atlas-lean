/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module
public import MathlibExt.CategoryTheory.Enriched.PointwiseLimit
public import MathlibExt.CategoryTheory.Enriched.PointwiseColimit

@[expose] public section
set_option autoImplicit false
noncomputable section
universe uA uV vV uJ vJ
namespace CategoryTheory.EnrichedFunctorCat
open Limits
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]
  {J : Type uJ} [Category.{vJ} J]

/-- Genuine enriched diagrams have all limits of an actual base diagram shape. -/
instance hasLimitsOfShape [HasLimitsOfShape J V] :
    HasLimitsOfShape J (EnrichedFunctorCat V A) where
  has_limit K := PointwiseLimit.hasLimit K

/-- Evaluation preserves every actual pointwise limit of that base shape. -/
instance evaluationPreservesLimitsOfShape [HasLimitsOfShape J V] (a : A) :
    PreservesLimitsOfShape J (evaluation (V := V) a) where
  preservesLimit := PointwiseLimit.evaluation_preservesLimit _ a

/-- Genuine enriched diagrams have all colimits of an actual base diagram shape. -/
instance hasColimitsOfShape [HasColimitsOfShape J V] :
    HasColimitsOfShape J (EnrichedFunctorCat V A) where
  has_colimit K := PointwiseColimit.hasColimit K

/-- Evaluation preserves every actual pointwise colimit of that base shape. -/
instance evaluationPreservesColimitsOfShape [HasColimitsOfShape J V] (a : A) :
    PreservesColimitsOfShape J (evaluation (V := V) a) where
  preservesColimit := PointwiseColimit.evaluation_preservesColimit _ a

end CategoryTheory.EnrichedFunctorCat
