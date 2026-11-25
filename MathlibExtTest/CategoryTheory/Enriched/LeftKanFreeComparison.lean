/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Authors: Tsutomu Okano <toskua@meta.com>
-/

import MathlibExt.CategoryTheory.Enriched.LeftKanFreeComparison

/-!
# Clients of the original Kan/free comparison

These clients use the entire original coend, actual free functors and both
actual adjunctions. Source Hom objects, coefficient maps and index arrows
retain their independently sized enriched categories.
-/

set_option autoImplicit false
noncomputable section

universe uV vV uA uB

open CategoryTheory Limits MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedFunctorCat.LeftKanFreeComparisonTests

open LeftKanFreeComparison

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]
  {B : Type uB} [EnrichedCategory V B]
  (j : EnrichedFunctor V A B)
  [∀ (F : EnrichedFunctorCat V A) (b : B),
    HasCoproduct (Enriched.weightedCoend.relations (leftKanWeight j b) F.toEnrichedFunctor)]
  [∀ (F : EnrichedFunctorCat V A) (b : B),
    HasCoproduct (Enriched.weightedCoend.objects (leftKanWeight j b) F.toEnrichedFunctor)]
  [∀ (F : EnrichedFunctorCat V A) (b : B),
    HasCoequalizer (Enriched.weightedCoend.leftMap (leftKanWeight j b) F.toEnrichedFunctor)
      (Enriched.weightedCoend.rightMap (leftKanWeight j b) F.toEnrichedFunctor)]

def actualKanFreeIso (a : A) (X : V) :
    leftKanObject j (Free.object a X) ≅ Free.object (j.obj a) X := iso j a X

theorem full_generator (a : A) (X : V) (b : B) (c : A) :
    Enriched.weightedCoend.ι (leftKanWeight j b) (Free.object a X).toEnrichedFunctor c ≫
        component (actualKanFreeIso j a X).hom b =
      ((j.obj c ⟶[V] b) ◁ (X ◁ j.map a c)) ≫
        (β_ (j.obj c ⟶[V] b) (X ⊗ (j.obj a ⟶[V] j.obj c))).hom ≫
        (α_ X (j.obj a ⟶[V] j.obj c) (j.obj c ⟶[V] b)).hom ≫
        (X ◁ eComp V (j.obj a) (j.obj c) b) := hom_ι j a X b c

theorem full_source_unit (a : A) (X : V) (c : A) :
    leftKanUnitComponent j (Free.object a X) c ≫
        component (actualKanFreeIso j a X).hom (j.obj c) = X ◁ j.map a c :=
  hom_unit_component j a X c

theorem inverse_unit_coefficient (a : A) (X : V) :
    Free.evaluate (j.obj a) X (leftKanObject j (Free.object a X))
        (actualKanFreeIso j a X).inv =
      (ρ_ X).inv ≫ (X ◁ eId V a) ≫ leftKanUnitComponent j (Free.object a X) a :=
  (evaluate_inv j a X).trans (inv_coefficient j a X)

theorem whole_kan_counit (a : A) (X : V) :
    (actualKanFreeIso j a X).hom = (leftKan j).map (FreeHomTransport.map j a X) ≫
      (leftKanRestrictionAdjunction j).counit.app (Free.object (j.obj a) X) :=
  hom_counit j a X

theorem both_inverse_laws (a : A) (X : V) :
    (actualKanFreeIso j a X).hom ≫ (actualKanFreeIso j a X).inv =
        𝟙 (leftKanObject j (Free.object a X)) ∧
      (actualKanFreeIso j a X).inv ≫ (actualKanFreeIso j a X).hom =
        𝟙 (Free.object (j.obj a) X) :=
  ⟨hom_inv_id j a X, inv_hom_id j a X⟩

theorem coefficient_family (a : A) {X Y : V} (f : X ⟶ Y) :
    (leftKan j).map (Free.coefficientMap a f) ≫ (actualKanFreeIso j a Y).hom =
      (actualKanFreeIso j a X).hom ≫ Free.coefficientMap (j.obj a) f :=
  hom_coefficient j a f

theorem source_family {a a' : A} (e : 𝟙_ V ⟶ (a ⟶[V] a')) (X : V) :
    (leftKan j).map (Free.sourceMap e X) ≫ (actualKanFreeIso j a X).hom =
      (actualKanFreeIso j a' X).hom ≫ Free.sourceMap (e ≫ j.map a a') X :=
  hom_source j e X

theorem inverse_source_family {a a' : A} (e : 𝟙_ V ⟶ (a ⟶[V] a')) (X : V) :
    Free.sourceMap (e ≫ j.map a a') X ≫ (actualKanFreeIso j a X).inv =
      (actualKanFreeIso j a' X).inv ≫ (leftKan j).map (Free.sourceMap e X) :=
  inv_source j e X

theorem entire_hom_comparison (a : A) (X : V) (Y : EnrichedFunctorCat V B)
    (f : leftKanObject j (Free.object a X) ⟶ Y) :
    (leftKanHomEquiv j (Free.object a X) Y).trans
        (Free.homEquiv a X (restrictionObject j Y)) f =
      Free.homEquiv (j.obj a) X Y ((actualKanFreeIso j a X).inv ≫ f) :=
  homEquiv_comparison j a X Y f

end CategoryTheory.EnrichedFunctorCat.LeftKanFreeComparisonTests
