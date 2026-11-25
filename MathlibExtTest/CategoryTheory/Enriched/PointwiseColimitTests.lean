/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module
public import MathlibExt.CategoryTheory.Enriched.PointwiseColimit
set_option autoImplicit false
noncomputable section
universe uA uV vV uJ vJ
namespace MathlibExtTest.EnrichedPointwiseColimit
open CategoryTheory Limits MonoidalCategory
open scoped MonoidalClosed
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]
  {J : Type uJ} [Category.{vJ} J]
  (K : J ⥤ EnrichedFunctorCat V A)
-- The primitive action laws require only the displayed endpoints.
example (a : A) [HasColimit (K ⋙ EnrichedFunctorCat.evaluation a)] :
    (colimit (K ⋙ EnrichedFunctorCat.evaluation a) ◁ eId V a) ≫
      EnrichedFunctorCat.PointwiseColimit.action K a a =
        (ρ_ (colimit (K ⋙ EnrichedFunctorCat.evaluation a))).hom :=
  EnrichedFunctorCat.PointwiseColimit.action_id K a
example (a b c : A)
    [HasColimit (K ⋙ EnrichedFunctorCat.evaluation a)]
    [HasColimit (K ⋙ EnrichedFunctorCat.evaluation b)]
    [HasColimit (K ⋙ EnrichedFunctorCat.evaluation c)] :
    (colimit (K ⋙ EnrichedFunctorCat.evaluation a) ◁ eComp V a b c) ≫
      EnrichedFunctorCat.PointwiseColimit.action K a c =
        (α_ (colimit (K ⋙ EnrichedFunctorCat.evaluation a)) (a ⟶[V] b) (b ⟶[V] c)).inv ≫
          (EnrichedFunctorCat.PointwiseColimit.action K a b ▷ (b ⟶[V] c)) ≫
            EnrichedFunctorCat.PointwiseColimit.action K b c :=
  EnrichedFunctorCat.PointwiseColimit.action_comp K a b c

variable [∀ a : A, HasColimit (K ⋙ EnrichedFunctorCat.evaluation a)]

example : IsColimit (EnrichedFunctorCat.PointwiseColimit.cocone K) :=
  EnrichedFunctorCat.PointwiseColimit.isColimit K
example (a : A) : IsColimit
    ((EnrichedFunctorCat.evaluation a).mapCocone
      (EnrichedFunctorCat.PointwiseColimit.cocone K)) :=
  EnrichedFunctorCat.PointwiseColimit.evaluatedIsColimit K a
example (j : J) (a : A) :
    EnrichedFunctorCat.component (EnrichedFunctorCat.PointwiseColimit.injection K j) a =
      colimit.ι (K ⋙ EnrichedFunctorCat.evaluation a) j :=
  EnrichedFunctorCat.PointwiseColimit.injection_component K j a
example (q : Cocone K) (a : A) :
    EnrichedFunctorCat.component (EnrichedFunctorCat.PointwiseColimit.desc K q) a =
      colimit.desc (K ⋙ EnrichedFunctorCat.evaluation a)
        ((EnrichedFunctorCat.evaluation a).mapCocone q) :=
  EnrichedFunctorCat.PointwiseColimit.desc_component K q a
example : HasColimit K := EnrichedFunctorCat.PointwiseColimit.hasColimit K
example (a : A) : PreservesColimit K (EnrichedFunctorCat.evaluation a) :=
  EnrichedFunctorCat.PointwiseColimit.evaluation_preservesColimit K a

#check @CategoryTheory.EnrichedFunctorCat.PointwiseColimit.action_id
#print axioms CategoryTheory.EnrichedFunctorCat.PointwiseColimit.action_id
#check @CategoryTheory.EnrichedFunctorCat.PointwiseColimit.action_comp
#print axioms CategoryTheory.EnrichedFunctorCat.PointwiseColimit.action_comp
#check @CategoryTheory.EnrichedFunctorCat.PointwiseColimit.object
#print axioms CategoryTheory.EnrichedFunctorCat.PointwiseColimit.object
#check @CategoryTheory.EnrichedFunctorCat.PointwiseColimit.injection
#print axioms CategoryTheory.EnrichedFunctorCat.PointwiseColimit.injection
#check @CategoryTheory.EnrichedFunctorCat.PointwiseColimit.injection_component
#print axioms CategoryTheory.EnrichedFunctorCat.PointwiseColimit.injection_component
#check @CategoryTheory.EnrichedFunctorCat.PointwiseColimit.cocone
#print axioms CategoryTheory.EnrichedFunctorCat.PointwiseColimit.cocone
#check @CategoryTheory.EnrichedFunctorCat.PointwiseColimit.desc
#print axioms CategoryTheory.EnrichedFunctorCat.PointwiseColimit.desc
#check @CategoryTheory.EnrichedFunctorCat.PointwiseColimit.desc_component
#print axioms CategoryTheory.EnrichedFunctorCat.PointwiseColimit.desc_component
#check @CategoryTheory.EnrichedFunctorCat.PointwiseColimit.isColimit
#print axioms CategoryTheory.EnrichedFunctorCat.PointwiseColimit.isColimit
#check @CategoryTheory.EnrichedFunctorCat.PointwiseColimit.evaluatedIsColimit
#print axioms CategoryTheory.EnrichedFunctorCat.PointwiseColimit.evaluatedIsColimit
#check @CategoryTheory.EnrichedFunctorCat.PointwiseColimit.hasColimit
#print axioms CategoryTheory.EnrichedFunctorCat.PointwiseColimit.hasColimit
#check @CategoryTheory.EnrichedFunctorCat.PointwiseColimit.evaluation_preservesColimit
#print axioms CategoryTheory.EnrichedFunctorCat.PointwiseColimit.evaluation_preservesColimit
end MathlibExtTest.EnrichedPointwiseColimit
