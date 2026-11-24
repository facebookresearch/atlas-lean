/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

import MathlibExt.CategoryTheory.Enriched.RightKanExtension

/-!
Public clients for the right enriched Kan adjunction: unique counit
factorization, simultaneous input naturality, actual unit and counit action,
and original weighted-end projection formulas.
-/

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section

universe uA uB uV vV
open CategoryTheory Limits MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedFunctorCat.RightKanExtensionTests

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]
  {B : Type uB} [EnrichedCategory V B]
  (j : EnrichedFunctor V A B)
  [∀ (X : EnrichedFunctorCat V A) (b : B),
    HasProduct (Enriched.weightedEnd.objects
      (Enriched.weightedEnd.rightKanWeight j b) X.toEnrichedFunctor)]
  [∀ (X : EnrichedFunctorCat V A) (b : B),
    HasProduct (Enriched.weightedEnd.relations
      (Enriched.weightedEnd.rightKanWeight j b) X.toEnrichedFunctor)]
  [∀ (X : EnrichedFunctorCat V A) (b : B),
    HasEqualizer
      (Enriched.weightedEnd.leftMap
        (Enriched.weightedEnd.rightKanWeight j b) X.toEnrichedFunctor)
      (Enriched.weightedEnd.rightMap
        (Enriched.weightedEnd.rightKanWeight j b) X.toEnrichedFunctor)]

set_option maxHeartbeats 200000 in
-- Preserve the existing project proof budget for this declaration.
example : True := by
  fail_if_success letI : Category A := inferInstance
  fail_if_success letI : Category B := inferInstance
  fail_if_success letI : HasProducts V := inferInstance
  fail_if_success letI : HasEqualizers V := inferInstance
  trivial

set_option maxHeartbeats 200000 in
-- Preserve the existing project proof budget for this declaration.
example : restriction j ⊣ rightKan j := rightKanAdjunction j

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 200000 in
-- Preserve the existing project proof budget for this declaration.
example (Y : EnrichedFunctorCat V B) (X : EnrichedFunctorCat V A)
    (f : (restriction j).obj Y ⟶ X) :
    ∃! g : Y ⟶ (rightKan j).obj X,
      (restriction j).map g ≫ (rightKanAdjunction j).counit.app X = f := by
  refine ⟨rightKanTranspose j f, ?_, ?_⟩
  · rw [rightKanAdjunction_counit_app]
    exact rightKanHomToRestricted_transpose j f
  · intro g hg
    rw [rightKanAdjunction_counit_app] at hg
    change rightKanHomToRestricted j g = f at hg
    exact (rightKanTranspose_homToRestricted j g).symm.trans
      (congrArg (rightKanTranspose j) hg)

set_option maxHeartbeats 200000 in
-- Preserve the existing project proof budget for this declaration.
example {Y' Y : EnrichedFunctorCat V B} {X X' : EnrichedFunctorCat V A}
    (p : Y' ⟶ Y) (f : (restriction j).obj Y ⟶ X) (q : X ⟶ X') :
    rightKanTranspose j ((restriction j).map p ≫ f ≫ q) =
      p ≫ rightKanTranspose j f ≫ (rightKan j).map q := by
  change rightKanTranspose j (restrictionMap j p ≫ f ≫ q) =
    p ≫ rightKanTranspose j f ≫ rightKanMap j q
  rw [rightKanTranspose_naturality_left, rightKanTranspose_naturality_right]

set_option maxHeartbeats 200000 in
-- Preserve the existing project proof budget for this declaration.
example {Y' Y : EnrichedFunctorCat V B} {X X' : EnrichedFunctorCat V A}
    (p : Y' ⟶ Y) (g : Y ⟶ (rightKan j).obj X) (q : X ⟶ X') :
    rightKanHomToRestricted j (p ≫ g ≫ (rightKan j).map q) =
      (restriction j).map p ≫ rightKanHomToRestricted j g ≫ q := by
  change rightKanHomToRestricted j (p ≫ g ≫ rightKanMap j q) =
    restrictionMap j p ≫ rightKanHomToRestricted j g ≫ q
  calc
    _ = restrictionMap j p ≫ rightKanHomToRestricted j (g ≫ rightKanMap j q) :=
      rightKanHomToRestricted_naturality_left j p (g ≫ rightKanMap j q)
    _ = _ := congrArg
      (fun h : restrictionObject j Y ⟶ X' => restrictionMap j p ≫ h)
      (rightKanHomToRestricted_naturality_right j g q)

set_option maxHeartbeats 200000 in
-- Preserve the existing project proof budget for this declaration.
example {Y : EnrichedFunctorCat V B} {X : EnrichedFunctorCat V A}
    (f : (restriction j).obj Y ⟶ X) :
    rightKanTranspose j f =
      (rightKanAdjunction j).unit.app Y ≫ (rightKan j).map f := by
  have h := (rightKanAdjunction j).homEquiv_unit (f := f)
  rw [rightKanAdjunction_homEquiv] at h
  exact h

set_option maxHeartbeats 200000 in
-- Preserve the existing project proof budget for this declaration.
example {Y : EnrichedFunctorCat V B} {X : EnrichedFunctorCat V A}
    (g : Y ⟶ (rightKan j).obj X) :
    rightKanHomToRestricted j g =
      (restriction j).map g ≫ (rightKanAdjunction j).counit.app X := by
  rw [rightKanAdjunction_counit_app]
  rfl

set_option maxHeartbeats 200000 in
-- Preserve the existing project proof budget for this declaration.
example {Y Y' : EnrichedFunctorCat V B} (f : Y ⟶ Y') :
    f ≫ (rightKanAdjunction j).unit.app Y' =
      (rightKanAdjunction j).unit.app Y ≫
        (rightKan j).map ((restriction j).map f) :=
  (rightKanAdjunction j).unit.naturality f

set_option maxHeartbeats 200000 in
-- Preserve the existing project proof budget for this declaration.
example {X X' : EnrichedFunctorCat V A} (f : X ⟶ X') :
    (restriction j).map ((rightKan j).map f) ≫
        (rightKanAdjunction j).counit.app X' =
      (rightKanAdjunction j).counit.app X ≫ f :=
  (rightKanAdjunction j).counit.naturality f

set_option maxHeartbeats 200000 in
-- Preserve the existing project proof budget for this declaration.
example (Y : EnrichedFunctorCat V B) (b c : B) :
    MonoidalClosed.uncurry (Y.toEnrichedFunctor.map b c) ≫
        component ((rightKanAdjunction j).unit.app Y) c =
      (component ((rightKanAdjunction j).unit.app Y) b ⊗ₘ 𝟙 (b ⟶[V] c)) ≫
        MonoidalClosed.uncurry
          (((rightKan j).obj ((restriction j).obj Y)).toEnrichedFunctor.map b c) :=
  ((rightKanAdjunction j).unit.app Y).uncurriedNaturality b c

set_option maxHeartbeats 200000 in
-- Preserve the existing project proof budget for this declaration.
example (X : EnrichedFunctorCat V A) (a a' : A) :
    MonoidalClosed.uncurry
        (((restriction j).obj ((rightKan j).obj X)).toEnrichedFunctor.map a a') ≫
        component ((rightKanAdjunction j).counit.app X) a' =
      (component ((rightKanAdjunction j).counit.app X) a ⊗ₘ 𝟙 (a ⟶[V] a')) ≫
        MonoidalClosed.uncurry (X.toEnrichedFunctor.map a a') :=
  ((rightKanAdjunction j).counit.app X).uncurriedNaturality a a'

set_option maxHeartbeats 200000 in
-- Preserve the existing project proof budget for this declaration.
example (Y : EnrichedFunctorCat V B) (b : B) (a : A) :
    component ((rightKanAdjunction j).unit.app Y) b ≫
        Enriched.weightedEnd.π (Enriched.weightedEnd.rightKanWeight j b)
          ((restriction j).obj Y).toEnrichedFunctor a =
      MonoidalClosed.curry
        ((β_ (b ⟶[V] j.obj a) (Y.toEnrichedFunctor.obj b)).hom ≫
          MonoidalClosed.uncurry (Y.toEnrichedFunctor.map b (j.obj a))) :=
  rightKanAdjunction_unit_component_π j Y b a

set_option maxHeartbeats 200000 in
-- Preserve the existing project proof budget for this declaration.
example (X : EnrichedFunctorCat V A) (a : A) :
    component ((rightKanAdjunction j).counit.app X) a =
      (λ_ (Enriched.weightedEnd.rightKanEndObject j X.toEnrichedFunctor (j.obj a))).inv ≫
        (eId V (j.obj a) ▷
          Enriched.weightedEnd.rightKanEndObject j X.toEnrichedFunctor (j.obj a)) ≫
        MonoidalClosed.uncurry (Enriched.weightedEnd.π
          (Enriched.weightedEnd.rightKanWeight j (j.obj a)) X.toEnrichedFunctor a) :=
  (rightKanAdjunction_counit_component j X a).trans (rightKanCounitComponent_eq j X a)

set_option maxHeartbeats 200000 in
-- Preserve the existing project proof budget for this declaration.
example {X X' X'' : EnrichedFunctorCat V A} (f : X ⟶ X') (g : X' ⟶ X'')
    (b : B) (a : A) :
    component ((rightKan j).map (f ≫ g)) b ≫ Enriched.weightedEnd.π
        (Enriched.weightedEnd.rightKanWeight j b) X''.toEnrichedFunctor a =
      Enriched.weightedEnd.π (Enriched.weightedEnd.rightKanWeight j b) X.toEnrichedFunctor a ≫
        (ihom (b ⟶[V] j.obj a)).map (component f a ≫ component g a) := by
  have h := rightKanMapComponent_π j (f ≫ g) b a
  rw [component_comp] at h
  change component (rightKanMap j (f ≫ g)) b ≫ _ = _
  rw [rightKanMap_component]
  exact h

set_option maxHeartbeats 200000 in
-- Preserve the existing project proof budget for this declaration.
example (Y : EnrichedFunctorCat V B) (a : A) :
    component ((restriction j).map ((rightKanAdjunction j).unit.app Y) ≫
        (rightKanAdjunction j).counit.app ((restriction j).obj Y)) a =
      𝟙 (Y.toEnrichedFunctor.obj (j.obj a)) :=
  (congrArg (fun q : (restriction j).obj Y ⟶ (restriction j).obj Y => component q a)
    ((rightKanAdjunction j).left_triangle_components Y)).trans
      (component_id ((restriction j).obj Y) a)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 200000 in
-- Preserve the existing project proof budget for this declaration.
example (X : EnrichedFunctorCat V A) (b : B) (a : A) :
    component ((rightKanAdjunction j).unit.app ((rightKan j).obj X) ≫
        (rightKan j).map ((rightKanAdjunction j).counit.app X)) b ≫
        Enriched.weightedEnd.π (Enriched.weightedEnd.rightKanWeight j b)
          X.toEnrichedFunctor a =
      Enriched.weightedEnd.π (Enriched.weightedEnd.rightKanWeight j b)
        X.toEnrichedFunctor a := by
  change (component
      (((rightKanAdjunction j).unit.app ((rightKan j).obj X) ≫
        (rightKan j).map ((rightKanAdjunction j).counit.app X)) :
          rightKanObject j X ⟶ rightKanObject j X) b :
        Enriched.weightedEnd.rightKanEndObject j X.toEnrichedFunctor b ⟶
          Enriched.weightedEnd.rightKanEndObject j X.toEnrichedFunctor b) ≫
      Enriched.weightedEnd.π (Enriched.weightedEnd.rightKanWeight j b)
        X.toEnrichedFunctor a = _
  have h := congrArg
    (fun q : rightKanObject j X ⟶ rightKanObject j X =>
      (component q b :
        Enriched.weightedEnd.rightKanEndObject j X.toEnrichedFunctor b ⟶
          Enriched.weightedEnd.rightKanEndObject j X.toEnrichedFunctor b) ≫
      Enriched.weightedEnd.π (Enriched.weightedEnd.rightKanWeight j b) X.toEnrichedFunctor a)
    ((rightKanAdjunction j).right_triangle_components X)
  have hi := component_id (rightKanObject j X) b
  change (component (𝟙 (rightKanObject j X)) b :
      Enriched.weightedEnd.rightKanEndObject j X.toEnrichedFunctor b ⟶
        Enriched.weightedEnd.rightKanEndObject j X.toEnrichedFunctor b) =
      𝟙 (Enriched.weightedEnd.rightKanEndObject j X.toEnrichedFunctor b) at hi
  exact h.trans ((congrArg
    (fun q : Enriched.weightedEnd.rightKanEndObject j X.toEnrichedFunctor b ⟶
        Enriched.weightedEnd.rightKanEndObject j X.toEnrichedFunctor b =>
      q ≫ Enriched.weightedEnd.π
        (Enriched.weightedEnd.rightKanWeight j b) X.toEnrichedFunctor a) hi).trans
      (Category.id_comp _))

end CategoryTheory.EnrichedFunctorCat.RightKanExtensionTests
