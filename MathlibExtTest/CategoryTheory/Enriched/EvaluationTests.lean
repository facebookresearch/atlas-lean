/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.Evaluation

set_option autoImplicit false
noncomputable section
universe uA uV vV

namespace MathlibExtTest.EnrichedEvaluation

open CategoryTheory
open scoped MonoidalClosed

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]

example (a : A) : EnrichedFunctorCat V A ⥤ V := EnrichedFunctorCat.evaluation a

example (a : A) (F : EnrichedFunctorCat V A) :
    (EnrichedFunctorCat.evaluation a).obj F = F.toEnrichedFunctor.obj a := rfl

example (a : A) {F G : EnrichedFunctorCat V A} (f : F ⟶ G) :
    (EnrichedFunctorCat.evaluation a).map f = EnrichedFunctorCat.component f a := rfl

example (a : A) (F : EnrichedFunctorCat V A) :
    (EnrichedFunctorCat.evaluation a).map (𝟙 F) = 𝟙 (F.toEnrichedFunctor.obj a) :=
  (EnrichedFunctorCat.evaluation a).map_id F

example (a : A) {F G H : EnrichedFunctorCat V A} (f : F ⟶ G) (g : G ⟶ H) :
    (EnrichedFunctorCat.evaluation a).map (f ≫ g) =
      EnrichedFunctorCat.component f a ≫ EnrichedFunctorCat.component g a :=
  (EnrichedFunctorCat.evaluation a).map_comp f g

#check @EnrichedFunctorCat.evaluation
#print axioms EnrichedFunctorCat.evaluation
#print axioms EnrichedFunctorCat.evaluation_obj
#print axioms EnrichedFunctorCat.evaluation_map

end MathlibExtTest.EnrichedEvaluation
