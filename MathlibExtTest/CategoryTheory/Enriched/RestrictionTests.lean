/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module
public import MathlibExt.CategoryTheory.Enriched.Restriction
set_option autoImplicit false
noncomputable section
universe uA uB uV vV
open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedFunctorCat
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]
  {B : Type uB} [EnrichedCategory V B]
  (j : EnrichedFunctor V A B)

example (F : EnrichedFunctorCat V B) :
    (restrictionObject j F).toEnrichedFunctor = j.comp V F.toEnrichedFunctor := rfl
example (F : EnrichedFunctorCat V B) (a b : A) :
    ((restriction j).obj F).toEnrichedFunctor.map a b =
      j.map a b ≫ F.toEnrichedFunctor.map (j.obj a) (j.obj b) := restriction_fullMap j F a b
example {F G : EnrichedFunctorCat V B} (t : F ⟶ G) (a : A) :
    component ((restriction j).map t) a = component t (j.obj a) := restrictionMap_component j t a
example (F : EnrichedFunctorCat V B) :
    (restriction j).map (𝟙 F) = 𝟙 ((restriction j).obj F) := (restriction j).map_id F
example {F G H : EnrichedFunctorCat V B} (t : F ⟶ G) (s : G ⟶ H) :
    (restriction j).map (t ≫ s) = (restriction j).map t ≫ (restriction j).map s :=
  (restriction j).map_comp t s

end CategoryTheory.EnrichedFunctorCat
