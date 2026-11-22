/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import MathlibExt.CategoryTheory.Enriched.PointwiseShapeInstances
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits

/-!
# Finite limits and colimits of enriched functors

For braided monoidal closed coefficients `V` and an enriched category `A`,
finite limits in `V` give finite limits in `EnrichedFunctorCat V A`.
Finite colimits in `V` likewise give finite colimits in this enriched
functor category, using the pointwise shape constructions.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe uA uV vV
namespace CategoryTheory.EnrichedFunctorCat
open Limits
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]

/-- Actual base finite limits supply genuine enriched finite limits. -/
instance hasFiniteLimits [HasFiniteLimits V] :
    HasFiniteLimits (EnrichedFunctorCat V A) where
  out _ := inferInstance

/-- Actual base finite colimits supply genuine enriched finite colimits. -/
instance hasFiniteColimits [HasFiniteColimits V] :
    HasFiniteColimits (EnrichedFunctorCat V A) where
  out _ := inferInstance

end CategoryTheory.EnrichedFunctorCat
