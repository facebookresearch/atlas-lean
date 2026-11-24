/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module

import MathlibExt.CategoryTheory.Enriched.ScalarTensor

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe uA uB uV vV
open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedFunctor.ScalarTensorTests

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]

example (M : V) (F : EnrichedFunctor V A V) (a : A) :
    (EnrichedFunctor.tensorLeft M F).obj a = M ⊗ F.obj a := rfl

example (M : V) (F : EnrichedFunctor V A V) (a b : A) :
    (EnrichedFunctor.tensorLeft M F).map a b =
      MonoidalClosed.curry ((α_ M (F.obj a) (a ⟶[V] b)).hom ≫
        M ◁ MonoidalClosed.uncurry (F.map a b)) := rfl

example (M : V) (F : EnrichedFunctor V A V) (a b : A) :
    MonoidalClosed.uncurry ((EnrichedFunctor.tensorLeft M F).map a b) =
      (α_ M (F.obj a) (a ⟶[V] b)).hom ≫ M ◁ MonoidalClosed.uncurry (F.map a b) :=
  EnrichedFunctor.tensorLeft_map_uncurry M F a b

end CategoryTheory.EnrichedFunctor.ScalarTensorTests

namespace CategoryTheory.EnrichedFunctorCat.ScalarTensorTests

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]
  {B : Type uB} [EnrichedCategory V B]

example (M : V) {F G : EnrichedFunctorCat V A} (f : F ⟶ G) (a : A) :
    component ((EnrichedFunctorCat.tensorLeft M).map f) a = M ◁ component f a :=
  tensorLeftMap_component M f a

example (M : V) (F : EnrichedFunctorCat V A) :
    (EnrichedFunctorCat.tensorLeft M).map (𝟙 F) = 𝟙 (tensorLeftObject M F) :=
  (EnrichedFunctorCat.tensorLeft M).map_id F

example (M : V) {F G H : EnrichedFunctorCat V A} (f : F ⟶ G) (g : G ⟶ H) :
    (EnrichedFunctorCat.tensorLeft M).map (f ≫ g) =
      (EnrichedFunctorCat.tensorLeft M).map f ≫ (EnrichedFunctorCat.tensorLeft M).map g :=
  (EnrichedFunctorCat.tensorLeft M).map_comp f g

example {M N : V} (h : M ⟶ N) (F : EnrichedFunctorCat V A) (a : A) :
    component (scalarTensorMap h F) a = h ▷ F.toEnrichedFunctor.obj a :=
  scalarTensorMap_component h F a

example {M N : V} (h : M ⟶ N) {F G : EnrichedFunctorCat V A} (f : F ⟶ G) :
    tensorLeftMap M f ≫ scalarTensorMap h G =
      scalarTensorMap h F ≫ tensorLeftMap N f :=
  scalarTensorMap_diagram_naturality h f

example {M N P : V} (h : M ⟶ N) (k : N ⟶ P) (F : EnrichedFunctorCat V A) :
    scalarTensorMap (h ≫ k) F = scalarTensorMap h F ≫ scalarTensorMap k F :=
  scalarTensorMap_comp h k F

example (M : V) (j : EnrichedFunctor V A B) (Y : EnrichedFunctorCat V B) :
    tensorLeftObject M (restrictionObject j Y) ≅ restrictionObject j (tensorLeftObject M Y) :=
  tensorLeftRestrictionIso M j Y

example (M : V) (j : EnrichedFunctor V A B) (Y : EnrichedFunctorCat V B) (a : A) :
    component (tensorLeftRestrictionIso M j Y).hom a =
      𝟙 (M ⊗ Y.toEnrichedFunctor.obj (j.obj a)) :=
  tensorLeftRestrictionIso_hom_component M j Y a

example (M : V) (j : EnrichedFunctor V A B) (Y : EnrichedFunctorCat V B) (a : A) :
    component (tensorLeftRestrictionIso M j Y).inv a =
      𝟙 (M ⊗ Y.toEnrichedFunctor.obj (j.obj a)) :=
  tensorLeftRestrictionIso_inv_component M j Y a

example (M : V) (j : EnrichedFunctor V A B) {Y Y' : EnrichedFunctorCat V B} (f : Y ⟶ Y') :
    tensorLeftMap M (restrictionMap j f) ≫ (tensorLeftRestrictionIso M j Y').hom =
      (tensorLeftRestrictionIso M j Y).hom ≫ restrictionMap j (tensorLeftMap M f) :=
  tensorLeftRestrictionIso_naturality M j f

example {M N : V} (h : M ⟶ N) (j : EnrichedFunctor V A B) (Y : EnrichedFunctorCat V B) :
    scalarTensorMap h (restrictionObject j Y) ≫ (tensorLeftRestrictionIso N j Y).hom =
      (tensorLeftRestrictionIso M j Y).hom ≫ restrictionMap j (scalarTensorMap h Y) :=
  tensorLeftRestrictionIso_scalar_naturality h j Y

end CategoryTheory.EnrichedFunctorCat.ScalarTensorTests
