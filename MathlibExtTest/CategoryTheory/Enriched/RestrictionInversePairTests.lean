/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.RestrictionInversePair

@[expose] public section
set_option autoImplicit false
noncomputable section
universe uV vV uA uB uC

open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace RestrictionInversePairTests

section Composition

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A] {B : Type uB} [EnrichedCategory V B]
  {C : Type uC} [EnrichedCategory V C]

open EnrichedFunctorCat EnrichedFunctorCat.RestrictionInversePair

example (F : EnrichedFunctor V A B) (G : EnrichedFunctor V B C) :
    restriction G ⋙ restriction F = restriction (F.comp V G) := restriction_comp F G

example : restriction (EnrichedFunctor.id V A) = 𝟭 (EnrichedFunctorCat V A) :=
  restriction_id

end Composition

section InversePair

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A] {B : Type uB} [EnrichedCategory V B]
  (F : EnrichedFunctor V A B) (G : EnrichedFunctor V B A)
  (hFG : F.comp V G = EnrichedFunctor.id V A)
  (hGF : G.comp V F = EnrichedFunctor.id V B)

open EnrichedFunctorCat EnrichedFunctorCat.RestrictionInversePair

example : restriction G ⋙ restriction F = 𝟭 (EnrichedFunctorCat V A) :=
  sourceRecovery F G hFG

example : restriction F ⋙ restriction G = 𝟭 (EnrichedFunctorCat V B) :=
  targetRecovery F G hGF

example : 𝟭 (EnrichedFunctorCat V A) ≅ restriction G ⋙ restriction F :=
  unitNatIso F G hFG

example : restriction F ⋙ restriction G ≅ 𝟭 (EnrichedFunctorCat V B) :=
  counitNatIso F G hGF

example : EnrichedFunctorCat V A ≌ EnrichedFunctorCat V B :=
  diagramEquivalence F G hFG hGF

example (X : EnrichedFunctorCat V A) :
    (restriction G).map ((unitNatIso F G hFG).hom.app X) ≫
      (counitNatIso F G hGF).hom.app ((restriction G).obj X) = 𝟙 _ :=
  source_triangle F G hFG hGF X

example (X : EnrichedFunctorCat V B) :
    (unitNatIso F G hFG).hom.app ((restriction F).obj X) ≫
      (restriction F).map ((counitNatIso F G hGF).hom.app X) = 𝟙 _ :=
  target_triangle F G hFG hGF X

example : (diagramEquivalence F G hFG hGF).functor = restriction G :=
  equivalence_functor F G hFG hGF

example : (diagramEquivalence F G hFG hGF).inverse = restriction F :=
  equivalence_inverse F G hFG hGF

example : HEq (diagramEquivalence F G hFG hGF).unitIso (unitNatIso F G hFG) :=
  equivalence_unit F G hFG hGF

example : HEq (diagramEquivalence F G hFG hGF).counitIso (counitNatIso F G hGF) :=
  equivalence_counit F G hFG hGF

end InversePair

end RestrictionInversePairTests
