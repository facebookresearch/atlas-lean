/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua

import MathlibExt.CategoryTheory.Enriched.FreeHomTransport

set_option autoImplicit false
noncomputable section
universe uV vV uA uB
open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedFunctorCat.FreeHomTransportClients

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A] {B : Type uB} [EnrichedCategory V B]
  (G : EnrichedFunctor V B A) (a b c : B) (X : V)

-- An arbitrary enriched index functor supplies a map, with no Hom-invertibility premise.
abbrev expectedCanonicalMap : Free.object a X ⟶ FreeHomTransport.restrictedFree G a X :=
  FreeHomTransport.map G a X

example : component (FreeHomTransport.map G a X) b = X ◁ G.map a b :=
  FreeHomTransport.map_component G a X b

example : MonoidalClosed.uncurry ((Free.object a X).toEnrichedFunctor.map b c) ≫
      (X ◁ G.map a c) =
    ((X ◁ G.map a b) ⊗ₘ 𝟙 (b ⟶[V] c)) ≫
      MonoidalClosed.uncurry ((FreeHomTransport.restrictedFree G a X).toEnrichedFunctor.map b c) :=
  FreeHomTransport.map_natural G a X b c

example (F : EnrichedFunctorCat V A) (f : X ⟶ F.toEnrichedFunctor.obj (G.obj a)) :
    FreeHomTransport.map G a X ≫ restrictionMap G (Free.extend (G.obj a) X F f) =
      Free.extend a X (restrictionObject G F) f := FreeHomTransport.map_extend G a X F f

example (F : EnrichedFunctorCat V A) (q : Free.object (G.obj a) X ⟶ F) :
    Free.evaluate a X (restrictionObject G F) (FreeHomTransport.map G a X ≫ restrictionMap G q) =
      Free.evaluate (G.obj a) X F q := FreeHomTransport.evaluate_map G a X F q

-- A lawful enriched functor alone does not forge an Iso of its complete Hom objects.
#check_failure FreeHomTransport.iso G a X

section Isomorphisms

variable [∀ a b : B, IsIso (G.map a b)]

abbrev expectedFreeIso : FreeHomTransport.restrictedFree G a X ≅ Free.object a X :=
  FreeHomTransport.iso G a X

example : component (FreeHomTransport.iso G a X).hom b = X ◁ inv (G.map a b) :=
  FreeHomTransport.iso_hom_component G a X b

example : MonoidalClosed.uncurry ((FreeHomTransport.restrictedFree G a X).toEnrichedFunctor.map b c) ≫
      (FreeHomTransport.componentIso G a X c).hom =
    ((FreeHomTransport.componentIso G a X b).hom ⊗ₘ 𝟙 (b ⟶[V] c)) ≫
      MonoidalClosed.uncurry ((Free.object a X).toEnrichedFunctor.map b c) :=
  FreeHomTransport.inverse_natural G a X b c

example {X Y : V} (f : X ⟶ Y) :
    restrictionMap G (Free.coefficientMap (G.obj a) f) ≫ (FreeHomTransport.iso G a Y).hom =
      (FreeHomTransport.iso G a X).hom ≫ Free.coefficientMap a f :=
  FreeHomTransport.coefficient_natural G a f

example : Free.functor (V := V) (G.obj a) ⋙ restriction G ≅ Free.functor (V := V) a :=
  FreeHomTransport.functorIso G a

example : (Free.adjunction (V := V) (G.obj a)).unit.app X ≫
      component (FreeHomTransport.iso G a X).hom a = (Free.adjunction (V := V) a).unit.app X :=
  FreeHomTransport.iso_unit G a X

end Isomorphisms
end CategoryTheory.EnrichedFunctorCat.FreeHomTransportClients
