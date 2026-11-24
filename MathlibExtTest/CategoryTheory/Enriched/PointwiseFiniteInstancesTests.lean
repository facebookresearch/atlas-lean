/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module
public import MathlibExt.CategoryTheory.Enriched.PointwiseFiniteInstances

set_option autoImplicit false
noncomputable section
universe uA uV vV
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.EnrichedFunctorCat.PointwiseFiniteInstancesTests
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]

example [HasFiniteLimits V] : HasFiniteLimits (EnrichedFunctorCat V A) := inferInstance
example [HasFiniteLimits V] (F G : EnrichedFunctorCat V A) : HasBinaryProduct F G :=
  inferInstance
example [HasFiniteLimits V] : HasTerminal (EnrichedFunctorCat V A) := inferInstance
example [HasFiniteColimits V] : HasFiniteColimits (EnrichedFunctorCat V A) := inferInstance
example [HasFiniteColimits V] (F G : EnrichedFunctorCat V A) : HasBinaryCoproduct F G :=
  inferInstance
example [HasFiniteColimits V] : HasInitial (EnrichedFunctorCat V A) := inferInstance

#check @CategoryTheory.EnrichedFunctorCat.hasFiniteLimits
#check @CategoryTheory.EnrichedFunctorCat.hasFiniteColimits

#print axioms CategoryTheory.EnrichedFunctorCat.hasFiniteLimits
#print axioms CategoryTheory.EnrichedFunctorCat.hasFiniteColimits
end CategoryTheory.EnrichedFunctorCat.PointwiseFiniteInstancesTests
