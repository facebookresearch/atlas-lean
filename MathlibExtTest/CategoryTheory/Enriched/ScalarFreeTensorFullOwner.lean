/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.ScalarFreeTensor
public import Batteries.Tactic.Lint

@[expose] public section

open CategoryTheory MonoidalCategory EnrichedFunctorCat
open scoped MonoidalClosed

universe uV vV uA

namespace MathlibExtTest.ScalarFreeTensorFullOwner

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]

example (a : A) (X : V) : Free.object a X =
    tensorLeftObject X (Free.representableObject a) :=
  Free.object_eq_scalarRepresentable a X

example (M X : V) (a : A) :
    (Free.scalarFreeIso M X a).hom ≫ (Free.scalarFreeIso M X a).inv =
      𝟙 (tensorLeftObject M (Free.object a X)) :=
  (Free.scalarFreeIso M X a).hom_inv_id

example (M X : V) (a : A) :
    (Free.scalarFreeIso M X a).inv ≫ (Free.scalarFreeIso M X a).hom =
      𝟙 (Free.object a (M ⊗ X)) :=
  (Free.scalarFreeIso M X a).inv_hom_id

example (M X : V) (a b : A) :
    component (Free.scalarFreeIso M X a).hom b = (α_ M X (a ⟶[V] b)).inv :=
  Free.scalarFreeIso_hom_component M X a b

example (M X : V) (a b : A) :
    component (Free.scalarFreeIso M X a).inv b = (α_ M X (a ⟶[V] b)).hom :=
  Free.scalarFreeIso_inv_component M X a b

example (M X : V) (a b c : A) :
    MonoidalClosed.uncurry
        ((tensorLeftObject M (Free.object a X)).toEnrichedFunctor.map b c) ≫
      (α_ M X (a ⟶[V] c)).inv =
    ((α_ M X (a ⟶[V] b)).inv ⊗ₘ 𝟙 (b ⟶[V] c)) ≫
      MonoidalClosed.uncurry ((Free.object a (M ⊗ X)).toEnrichedFunctor.map b c) :=
  Free.scalarFreeIso_hom_fullHom M X a b c

example (M X : V) (a b c : A) :
    MonoidalClosed.uncurry ((Free.object a (M ⊗ X)).toEnrichedFunctor.map b c) ≫
      (α_ M X (a ⟶[V] c)).hom =
    ((α_ M X (a ⟶[V] b)).hom ⊗ₘ 𝟙 (b ⟶[V] c)) ≫
      MonoidalClosed.uncurry
        ((tensorLeftObject M (Free.object a X)).toEnrichedFunctor.map b c) :=
  Free.scalarFreeIso_inv_fullHom M X a b c

example (M : V) (a : A) {X Y : V} (f : X ⟶ Y) :
    tensorLeftMap M (Free.coefficientMap a f) ≫ (Free.scalarFreeIso M Y a).hom =
      (Free.scalarFreeIso M X a).hom ≫ Free.coefficientMap a (M ◁ f) :=
  Free.scalarFreeIso_coefficient M a f

example {M N : V} (h : M ⟶ N) (X : V) (a : A) :
    scalarTensorMap h (Free.object a X) ≫ (Free.scalarFreeIso N X a).hom =
      (Free.scalarFreeIso M X a).hom ≫ Free.coefficientMap a (h ▷ X) :=
  Free.scalarFreeIso_scalar h X a

example (M : V) (a : A) :
    Free.functor a ⋙ EnrichedFunctorCat.tensorLeft M ≅
      MonoidalCategory.tensorLeft M ⋙ Free.functor a :=
  Free.scalarFreeNatIso M a

example {a a' : A} (e : 𝟙_ V ⟶ (a ⟶[V] a')) (X : V) (b : A) :
    component (Free.sourceMap e X) b = X ◁ Free.sourceHomMap e b :=
  Free.sourceMap_component e X b

example (M X : V) {a a' : A} (e : 𝟙_ V ⟶ (a ⟶[V] a')) :
    tensorLeftMap M (Free.sourceMap e X) ≫ (Free.scalarFreeIso M X a).hom =
      (Free.scalarFreeIso M X a').hom ≫ Free.sourceMap e (M ⊗ X) :=
  Free.scalarFreeIso_source M X e

example (M X : V) {a a' : A} (e : 𝟙_ V ⟶ (a ⟶[V] a')) :
    Free.sourceMap e (M ⊗ X) ≫ (Free.scalarFreeIso M X a).inv =
      (Free.scalarFreeIso M X a').inv ≫ tensorLeftMap M (Free.sourceMap e X) :=
  Free.scalarFreeIso_inv_source M X e

example {a a' : A} (e : 𝟙_ V ⟶ (a ⟶[V] a')) (X : V) (b c : A) :
    Free.action a' X b c ≫ (X ◁ Free.sourceHomMap e c) =
      ((X ◁ Free.sourceHomMap e b) ⊗ₘ 𝟙 (b ⟶[V] c)) ≫ Free.action a X b c :=
  Free.sourceMap_fullHom e X b c

end MathlibExtTest.ScalarFreeTensorFullOwner
