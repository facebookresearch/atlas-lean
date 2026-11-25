/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module
public import MathlibExt.CategoryTheory.Enriched.PointwiseShapeInstances

set_option autoImplicit false
noncomputable section
universe uA uV vV uJ vJ

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.EnrichedFunctorCat.PointwiseShapeInstancesTests

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]
  {J : Type uJ} [Category.{vJ} J]

section Limits
variable [HasLimitsOfShape J V]

example : HasLimitsOfShape J (EnrichedFunctorCat V A) := inferInstance
example (K : J ⥤ EnrichedFunctorCat V A) : HasLimit K := inferInstance
example (a : A) : PreservesLimitsOfShape J (evaluation (V := V) a) := inferInstance
example (K : J ⥤ EnrichedFunctorCat V A) (a : A) :
    PreservesLimit K (evaluation a) := inferInstance

end Limits

section Colimits
variable [HasColimitsOfShape J V]

example : HasColimitsOfShape J (EnrichedFunctorCat V A) := inferInstance
example (K : J ⥤ EnrichedFunctorCat V A) : HasColimit K := inferInstance
example (a : A) : PreservesColimitsOfShape J (evaluation (V := V) a) := inferInstance
example (K : J ⥤ EnrichedFunctorCat V A) (a : A) :
    PreservesColimit K (evaluation a) := inferInstance

end Colimits

#check @CategoryTheory.EnrichedFunctorCat.hasLimitsOfShape
#check @CategoryTheory.EnrichedFunctorCat.evaluationPreservesLimitsOfShape
#check @CategoryTheory.EnrichedFunctorCat.hasColimitsOfShape
#check @CategoryTheory.EnrichedFunctorCat.evaluationPreservesColimitsOfShape

#print axioms CategoryTheory.EnrichedFunctorCat.hasLimitsOfShape
#print axioms CategoryTheory.EnrichedFunctorCat.evaluationPreservesLimitsOfShape
#print axioms CategoryTheory.EnrichedFunctorCat.hasColimitsOfShape
#print axioms CategoryTheory.EnrichedFunctorCat.evaluationPreservesColimitsOfShape

end CategoryTheory.EnrichedFunctorCat.PointwiseShapeInstancesTests
