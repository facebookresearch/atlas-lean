/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module
public import MathlibExt.CategoryTheory.Enriched.LocallySmall

set_option autoImplicit false
noncomputable section
universe w uA uV vV
open CategoryTheory
open scoped CategoryTheory.MonoidalClosed

namespace CategoryTheory.EnrichedFunctorCat.LocallySmallTests
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]
  [Small.{w} A] [LocallySmall.{w} V]

example : LocallySmall.{w} (EnrichedFunctorCat V A) := inferInstance
example (F G : EnrichedFunctorCat V A) : Small.{w} (F ⟶ G) := inferInstance
example (F G : EnrichedFunctorCat V A) :
    Small.{w} (∀ a : A, F.toEnrichedFunctor.obj a ⟶ G.toEnrichedFunctor.obj a) :=
  inferInstance

#check @CategoryTheory.EnrichedFunctorCat.locallySmall
#print axioms CategoryTheory.EnrichedFunctorCat.locallySmall
end CategoryTheory.EnrichedFunctorCat.LocallySmallTests
