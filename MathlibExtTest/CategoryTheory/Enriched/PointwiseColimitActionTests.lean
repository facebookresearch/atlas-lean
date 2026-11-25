/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module
public import MathlibExt.CategoryTheory.Enriched.PointwiseColimitAction

set_option autoImplicit false
noncomputable section
universe uA uV vV uJ vJ
namespace MathlibExtTest.EnrichedPointwiseColimitAction
open CategoryTheory Limits MonoidalCategory
open scoped MonoidalClosed
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]
  {J : Type uJ} [Category.{vJ} J]
  (K : J ⥤ EnrichedFunctorCat V A)
example (a b : A)
    [HasColimit (K ⋙ EnrichedFunctorCat.evaluation a)]
    [HasColimit (K ⋙ EnrichedFunctorCat.evaluation b)] (j : J) :
    (colimit.ι (K ⋙ EnrichedFunctorCat.evaluation a) j ▷ (a ⟶[V] b)) ≫
      EnrichedFunctorCat.PointwiseColimit.action K a b =
    MonoidalClosed.uncurry ((K.obj j).toEnrichedFunctor.map a b) ≫
      colimit.ι (K ⋙ EnrichedFunctorCat.evaluation b) j :=
  EnrichedFunctorCat.PointwiseColimit.injection_action K a b j
example (a b : A) [HasColimit (K ⋙ EnrichedFunctorCat.evaluation b)] :
    Cocone ((K ⋙ EnrichedFunctorCat.evaluation a) ⋙ tensorRight (a ⟶[V] b)) :=
  EnrichedFunctorCat.PointwiseColimit.actionCocone K a b

example (a b : A)
    [HasColimit (K ⋙ EnrichedFunctorCat.evaluation a)]
    [HasColimit (K ⋙ EnrichedFunctorCat.evaluation b)]
    (f : colimit (K ⋙ EnrichedFunctorCat.evaluation a) ⊗ (a ⟶[V] b) ⟶
      colimit (K ⋙ EnrichedFunctorCat.evaluation b))
    (hf : ∀ j : J,
      (colimit.ι (K ⋙ EnrichedFunctorCat.evaluation a) j ▷ (a ⟶[V] b)) ≫ f =
        MonoidalClosed.uncurry ((K.obj j).toEnrichedFunctor.map a b) ≫
          colimit.ι (K ⋙ EnrichedFunctorCat.evaluation b) j) :
    f = EnrichedFunctorCat.PointwiseColimit.action K a b :=
  EnrichedFunctorCat.PointwiseColimit.action_eq K a b f hf

#check @EnrichedFunctorCat.PointwiseColimit.actionCocone
#check @EnrichedFunctorCat.PointwiseColimit.action
#check @EnrichedFunctorCat.PointwiseColimit.injection_action
#check @EnrichedFunctorCat.PointwiseColimit.action_eq
#print axioms EnrichedFunctorCat.PointwiseColimit.actionCocone
#print axioms EnrichedFunctorCat.PointwiseColimit.action_eq

#print axioms EnrichedFunctorCat.PointwiseColimit.action
#print axioms EnrichedFunctorCat.PointwiseColimit.injection_action
end MathlibExtTest.EnrichedPointwiseColimitAction
