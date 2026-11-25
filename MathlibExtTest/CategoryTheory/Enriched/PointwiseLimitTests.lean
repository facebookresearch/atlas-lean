/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module
public import MathlibExt.CategoryTheory.Enriched.PointwiseLimit
set_option autoImplicit false
noncomputable section
universe uA uV vV uJ vJ
namespace MathlibExtTest.EnrichedPointwiseLimit
open CategoryTheory Limits MonoidalCategory
open scoped MonoidalClosed
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]
  {J : Type uJ} [Category.{vJ} J]
  (K : J ⥤ EnrichedFunctorCat V A)

example (a : A) [HasLimit (K ⋙ EnrichedFunctorCat.evaluation a)] :
    (limit (K ⋙ EnrichedFunctorCat.evaluation a) ◁ eId V a) ≫
      EnrichedFunctorCat.PointwiseLimit.action K a a =
        (ρ_ (limit (K ⋙ EnrichedFunctorCat.evaluation a))).hom :=
  EnrichedFunctorCat.PointwiseLimit.action_id K a

example (a b c : A) [HasLimit (K ⋙ EnrichedFunctorCat.evaluation a)]
    [HasLimit (K ⋙ EnrichedFunctorCat.evaluation b)]
    [HasLimit (K ⋙ EnrichedFunctorCat.evaluation c)] :
    (limit (K ⋙ EnrichedFunctorCat.evaluation a) ◁ eComp V a b c) ≫
      EnrichedFunctorCat.PointwiseLimit.action K a c =
      (α_ (limit (K ⋙ EnrichedFunctorCat.evaluation a)) (a ⟶[V] b) (b ⟶[V] c)).inv ≫
        (EnrichedFunctorCat.PointwiseLimit.action K a b ▷ (b ⟶[V] c)) ≫
          EnrichedFunctorCat.PointwiseLimit.action K b c :=
  EnrichedFunctorCat.PointwiseLimit.action_comp K a b c

variable [∀ a : A, HasLimit (K ⋙ EnrichedFunctorCat.evaluation a)]
example : IsLimit (EnrichedFunctorCat.PointwiseLimit.cone K) :=
  EnrichedFunctorCat.PointwiseLimit.isLimit K
example (a : A) : IsLimit ((EnrichedFunctorCat.evaluation a).mapCone
    (EnrichedFunctorCat.PointwiseLimit.cone K)) :=
  EnrichedFunctorCat.PointwiseLimit.evaluatedIsLimit K a
example (j : J) (a : A) :
    EnrichedFunctorCat.component (EnrichedFunctorCat.PointwiseLimit.projection K j) a =
      limit.π (K ⋙ EnrichedFunctorCat.evaluation a) j :=
  EnrichedFunctorCat.PointwiseLimit.projection_component K j a
example (q : Cone K) (a : A) :
    EnrichedFunctorCat.component (EnrichedFunctorCat.PointwiseLimit.lift K q) a =
      limit.lift (K ⋙ EnrichedFunctorCat.evaluation a) ((EnrichedFunctorCat.evaluation a).mapCone q) :=
  EnrichedFunctorCat.PointwiseLimit.lift_component K q a
example : HasLimit K := EnrichedFunctorCat.PointwiseLimit.hasLimit K
example (a : A) : PreservesLimit K (EnrichedFunctorCat.evaluation a) :=
  EnrichedFunctorCat.PointwiseLimit.evaluation_preservesLimit K a
#check @CategoryTheory.EnrichedFunctorCat.PointwiseLimit.action_id
#print axioms CategoryTheory.EnrichedFunctorCat.PointwiseLimit.action_id
#check @CategoryTheory.EnrichedFunctorCat.PointwiseLimit.action_comp
#print axioms CategoryTheory.EnrichedFunctorCat.PointwiseLimit.action_comp
#check @CategoryTheory.EnrichedFunctorCat.PointwiseLimit.object
#print axioms CategoryTheory.EnrichedFunctorCat.PointwiseLimit.object
#check @CategoryTheory.EnrichedFunctorCat.PointwiseLimit.projection
#print axioms CategoryTheory.EnrichedFunctorCat.PointwiseLimit.projection
#check @CategoryTheory.EnrichedFunctorCat.PointwiseLimit.projection_component
#print axioms CategoryTheory.EnrichedFunctorCat.PointwiseLimit.projection_component
#check @CategoryTheory.EnrichedFunctorCat.PointwiseLimit.cone
#print axioms CategoryTheory.EnrichedFunctorCat.PointwiseLimit.cone
#check @CategoryTheory.EnrichedFunctorCat.PointwiseLimit.lift
#print axioms CategoryTheory.EnrichedFunctorCat.PointwiseLimit.lift
#check @CategoryTheory.EnrichedFunctorCat.PointwiseLimit.lift_component
#print axioms CategoryTheory.EnrichedFunctorCat.PointwiseLimit.lift_component
#check @CategoryTheory.EnrichedFunctorCat.PointwiseLimit.isLimit
#print axioms CategoryTheory.EnrichedFunctorCat.PointwiseLimit.isLimit
#check @CategoryTheory.EnrichedFunctorCat.PointwiseLimit.evaluatedIsLimit
#print axioms CategoryTheory.EnrichedFunctorCat.PointwiseLimit.evaluatedIsLimit
#check @CategoryTheory.EnrichedFunctorCat.PointwiseLimit.hasLimit
#print axioms CategoryTheory.EnrichedFunctorCat.PointwiseLimit.hasLimit
#check @CategoryTheory.EnrichedFunctorCat.PointwiseLimit.evaluation_preservesLimit
#print axioms CategoryTheory.EnrichedFunctorCat.PointwiseLimit.evaluation_preservesLimit
end MathlibExtTest.EnrichedPointwiseLimit
