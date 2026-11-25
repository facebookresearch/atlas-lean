/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module
public import MathlibExt.CategoryTheory.Enriched.PointwiseLimitAction
set_option autoImplicit false
noncomputable section
universe uA uV vV uJ vJ
namespace MathlibExtTest.EnrichedPointwiseLimitAction
open CategoryTheory Limits MonoidalCategory
open scoped MonoidalClosed
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]
  {J : Type uJ} [Category.{vJ} J]
  (K : J ⥤ EnrichedFunctorCat V A)

example (a b : A) [HasLimit (K ⋙ EnrichedFunctorCat.evaluation a)] :
    Cone (K ⋙ EnrichedFunctorCat.evaluation b) :=
  EnrichedFunctorCat.PointwiseLimit.actionCone K a b

example (a b : A) [HasLimit (K ⋙ EnrichedFunctorCat.evaluation a)]
    [HasLimit (K ⋙ EnrichedFunctorCat.evaluation b)] (j : J) :
    EnrichedFunctorCat.PointwiseLimit.action K a b ≫
        limit.π (K ⋙ EnrichedFunctorCat.evaluation b) j =
      (limit.π (K ⋙ EnrichedFunctorCat.evaluation a) j ▷ (a ⟶[V] b)) ≫
        MonoidalClosed.uncurry ((K.obj j).toEnrichedFunctor.map a b) :=
  EnrichedFunctorCat.PointwiseLimit.action_projection K a b j

example (a b : A) [HasLimit (K ⋙ EnrichedFunctorCat.evaluation a)]
    [HasLimit (K ⋙ EnrichedFunctorCat.evaluation b)]
    (f : limit (K ⋙ EnrichedFunctorCat.evaluation a) ⊗ (a ⟶[V] b) ⟶
      limit (K ⋙ EnrichedFunctorCat.evaluation b))
    (hf : ∀ j, f ≫ limit.π (K ⋙ EnrichedFunctorCat.evaluation b) j =
      (limit.π (K ⋙ EnrichedFunctorCat.evaluation a) j ▷ (a ⟶[V] b)) ≫
        MonoidalClosed.uncurry ((K.obj j).toEnrichedFunctor.map a b)) :
    f = EnrichedFunctorCat.PointwiseLimit.action K a b :=
  EnrichedFunctorCat.PointwiseLimit.action_eq K a b f hf

#check @CategoryTheory.EnrichedFunctorCat.PointwiseLimit.actionCone
#print axioms CategoryTheory.EnrichedFunctorCat.PointwiseLimit.actionCone
#check @CategoryTheory.EnrichedFunctorCat.PointwiseLimit.action
#print axioms CategoryTheory.EnrichedFunctorCat.PointwiseLimit.action
#check @CategoryTheory.EnrichedFunctorCat.PointwiseLimit.action_projection
#print axioms CategoryTheory.EnrichedFunctorCat.PointwiseLimit.action_projection
#check @CategoryTheory.EnrichedFunctorCat.PointwiseLimit.action_eq
#print axioms CategoryTheory.EnrichedFunctorCat.PointwiseLimit.action_eq
end MathlibExtTest.EnrichedPointwiseLimitAction
