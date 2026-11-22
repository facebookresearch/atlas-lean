/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import MathlibExt.CategoryTheory.Enriched.PointwiseShapeInstances

/-!
# Size-indexed pointwise limits of enriched functors

For a braided monoidal closed category V and a V-enriched category A, limits and colimits of
enriched functors A ⟶ V are computed pointwise whenever the corresponding size-indexed
limits or colimits exist in V. Evaluation preserves them with the same index and morphism
universes.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe uA uV vV uJ vJ

namespace CategoryTheory.EnrichedFunctorCat
open Limits
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]

/-- Genuine enriched functors retain the actual base size of available limits. -/
instance hasLimitsOfSize [HasLimitsOfSize.{vJ, uJ} V] :
    HasLimitsOfSize.{vJ, uJ} (EnrichedFunctorCat V A) where
  has_limits_of_shape _ := inferInstance

/-- Evaluation preserves all genuine enriched limits of that same actual size. -/
instance evaluationPreservesLimitsOfSize [HasLimitsOfSize.{vJ, uJ} V] (a : A) :
    PreservesLimitsOfSize.{vJ, uJ} (evaluation (V := V) a) where
  preservesLimitsOfShape := fun {_} => inferInstance

/-- Genuine enriched functors retain the actual base size of available colimits. -/
instance hasColimitsOfSize [HasColimitsOfSize.{vJ, uJ} V] :
    HasColimitsOfSize.{vJ, uJ} (EnrichedFunctorCat V A) where
  has_colimits_of_shape _ := inferInstance

/-- Evaluation preserves all genuine enriched colimits of that same actual size. -/
instance evaluationPreservesColimitsOfSize [HasColimitsOfSize.{vJ, uJ} V] (a : A) :
    PreservesColimitsOfSize.{vJ, uJ} (evaluation (V := V) a) where
  preservesColimitsOfShape := fun {_} => inferInstance

end CategoryTheory.EnrichedFunctorCat
