/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module
public import MathlibExt.CategoryTheory.Enriched.PointwiseSizeInstances

set_option autoImplicit false
noncomputable section
universe uA uV vV uJ vJ
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.EnrichedFunctorCat.PointwiseSizeInstancesTests
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]
  {J : Type uJ} [Category.{vJ} J]

section Limits
variable [HasLimitsOfSize.{vJ, uJ} V]
example : HasLimitsOfSize.{vJ, uJ} (EnrichedFunctorCat V A) := inferInstance
example (a : A) : PreservesLimitsOfSize.{vJ, uJ} (evaluation (V := V) a) := inferInstance
example (K : J ⥤ EnrichedFunctorCat V A) : HasLimit K := inferInstance
end Limits

section Colimits
variable [HasColimitsOfSize.{vJ, uJ} V]
example : HasColimitsOfSize.{vJ, uJ} (EnrichedFunctorCat V A) := inferInstance
example (a : A) : PreservesColimitsOfSize.{vJ, uJ} (evaluation (V := V) a) := inferInstance
example (K : J ⥤ EnrichedFunctorCat V A) : HasColimit K := inferInstance
end Colimits

#check @CategoryTheory.EnrichedFunctorCat.hasLimitsOfSize
#check @CategoryTheory.EnrichedFunctorCat.evaluationPreservesLimitsOfSize
#check @CategoryTheory.EnrichedFunctorCat.hasColimitsOfSize
#check @CategoryTheory.EnrichedFunctorCat.evaluationPreservesColimitsOfSize

#print axioms CategoryTheory.EnrichedFunctorCat.hasLimitsOfSize
#print axioms CategoryTheory.EnrichedFunctorCat.evaluationPreservesLimitsOfSize
#print axioms CategoryTheory.EnrichedFunctorCat.hasColimitsOfSize
#print axioms CategoryTheory.EnrichedFunctorCat.evaluationPreservesColimitsOfSize
end CategoryTheory.EnrichedFunctorCat.PointwiseSizeInstancesTests
