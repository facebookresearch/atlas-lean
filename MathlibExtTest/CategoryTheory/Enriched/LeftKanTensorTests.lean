/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

import MathlibExt.CategoryTheory.Enriched.LeftKanTensor
import Batteries.Tactic.Lint

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 512
noncomputable section
universe uA uB uV vV
open CategoryTheory Limits MonoidalCategory BraidedCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedFunctorCat
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A] {B : Type uB} [EnrichedCategory V B]
  (j : EnrichedFunctor V A B)
  [∀ (X : EnrichedFunctorCat V A) (b : B),
    HasCoproduct (Enriched.weightedCoend.relations (leftKanWeight j b) X.toEnrichedFunctor)]
  [∀ (X : EnrichedFunctorCat V A) (b : B),
    HasCoproduct (Enriched.weightedCoend.objects (leftKanWeight j b) X.toEnrichedFunctor)]
  [∀ (X : EnrichedFunctorCat V A) (b : B),
    HasCoequalizer (Enriched.weightedCoend.leftMap (leftKanWeight j b) X.toEnrichedFunctor)
      (Enriched.weightedCoend.rightMap (leftKanWeight j b) X.toEnrichedFunctor)]

example (M : V) : tensorLeft M ⋙ leftKan j ≅ leftKan j ⋙ tensorLeft M :=
  leftKanTensorNatIso j M

example (M : V) (X : EnrichedFunctorCat V A) :
    leftKanTensorHom j M X ≫ leftKanTensorInv j M X =
      𝟙 (leftKanObject j (tensorLeftObject M X)) :=
  leftKanTensorHom_inv j M X

example (M : V) (X : EnrichedFunctorCat V A) :
    leftKanTensorInv j M X ≫ leftKanTensorHom j M X =
      𝟙 (tensorLeftObject M (leftKanObject j X)) :=
  leftKanTensorInv_hom j M X

example (M : V) (X : EnrichedFunctorCat V A) (a : A) :
    leftKanUnitComponent j (tensorLeftObject M X) a ≫
        component ((leftKanTensorNatIso j M).hom.app X) (j.obj a) =
      M ◁ leftKanUnitComponent j X a := by
  rw [leftKanTensorNatIso_hom_app]
  exact leftKanTensorHom_unit j M X a

example (M : V) (X : EnrichedFunctorCat V A) (a : A) :
    (M ◁ leftKanUnitComponent j X a) ≫
        component ((leftKanTensorNatIso j M).inv.app X) (j.obj a) =
      leftKanUnitComponent j (tensorLeftObject M X) a := by
  rw [leftKanTensorNatIso_inv_app]
  exact leftKanTensorInv_unit j M X a

example (M : V) (X : EnrichedFunctorCat V A) (b : B) (a : A) :
    Enriched.weightedCoend.ι (leftKanWeight j b) (tensorLeftObject M X).toEnrichedFunctor a ≫
        component (leftKanTensorHom j M X) b =
      (α_ (j.obj a ⟶[V] b) M (X.toEnrichedFunctor.obj a)).inv ≫
        ((β_ (j.obj a ⟶[V] b) M).hom ▷ X.toEnrichedFunctor.obj a) ≫
        (α_ M (j.obj a ⟶[V] b) (X.toEnrichedFunctor.obj a)).hom ≫
        (M ◁ Enriched.weightedCoend.ι (leftKanWeight j b) X.toEnrichedFunctor a) :=
  leftKanTensorHom_ι j M X b a

example (M : V) (X : EnrichedFunctorCat V A) (b : B) (a : A) :
    (M ◁ Enriched.weightedCoend.ι (leftKanWeight j b) X.toEnrichedFunctor a) ≫
        component (leftKanTensorInv j M X) b =
      (α_ M (j.obj a ⟶[V] b) (X.toEnrichedFunctor.obj a)).inv ≫
        ((β_ (j.obj a ⟶[V] b) M).inv ▷ X.toEnrichedFunctor.obj a) ≫
        (α_ (j.obj a ⟶[V] b) M (X.toEnrichedFunctor.obj a)).hom ≫
        Enriched.weightedCoend.ι (leftKanWeight j b) (tensorLeftObject M X).toEnrichedFunctor a :=
  leftKanTensorInv_ι j M X b a

example (M : V) {X X' : EnrichedFunctorCat V A} (p : X ⟶ X') :
    (leftKan j).map (tensorLeftMap M p) ≫ leftKanTensorHom j M X' =
      leftKanTensorHom j M X ≫ tensorLeftMap M ((leftKan j).map p) :=
  leftKanTensorHom_naturality j M p

example (M : V) {X X' : EnrichedFunctorCat V A} (p : X ⟶ X') :
    tensorLeftMap M ((leftKan j).map p) ≫ leftKanTensorInv j M X' =
      leftKanTensorInv j M X ≫ (leftKan j).map (tensorLeftMap M p) :=
  leftKanTensorInv_naturality j M p

example {M N : V} (u : M ⟶ N) (X : EnrichedFunctorCat V A) :
    (leftKan j).map (scalarTensorMap u X) ≫ leftKanTensorHom j N X =
      leftKanTensorHom j M X ≫ scalarTensorMap u (leftKanObject j X) :=
  leftKanTensorHom_scalar_naturality j u X

example {M N : V} (u : M ⟶ N) (X : EnrichedFunctorCat V A) :
    scalarTensorMap u (leftKanObject j X) ≫ leftKanTensorInv j N X =
      leftKanTensorInv j M X ≫ (leftKan j).map (scalarTensorMap u X) :=
  leftKanTensorInv_scalar_naturality j u X

example (Γ : Center V) {X X' : EnrichedFunctorCat V A}
    (t : GradedNatTrans Γ X.toEnrichedFunctor X'.toEnrichedFunctor) :
    gradedTensorToUnit Γ (leftKanGradedMap j Γ t) =
      leftKanTensorInv j Γ.1 X ≫ (leftKan j).map (gradedTensorToUnit Γ t) :=
  leftKanTensorInv_gradedMap j Γ t

example (Γ : Center V) {X X' : EnrichedFunctorCat V A}
    (t : GradedNatTrans Γ X.toEnrichedFunctor X'.toEnrichedFunctor) :
    leftKanTensorHom j Γ.1 X ≫ gradedTensorToUnit Γ (leftKanGradedMap j Γ t) =
      (leftKan j).map (gradedTensorToUnit Γ t) :=
  leftKanTensorHom_gradedMap j Γ t

end CategoryTheory.EnrichedFunctorCat

#check CategoryTheory.EnrichedFunctorCat.leftKanTensorNatIso
#check CategoryTheory.EnrichedFunctorCat.leftKanTensorHom_unit
#check CategoryTheory.EnrichedFunctorCat.leftKanTensorInv_unit
#check CategoryTheory.EnrichedFunctorCat.leftKanTensorHom_ι
#check CategoryTheory.EnrichedFunctorCat.leftKanTensorInv_ι
#check CategoryTheory.EnrichedFunctorCat.leftKanTensorHom_scalar_naturality
#check CategoryTheory.EnrichedFunctorCat.leftKanTensorInv_scalar_naturality
#check CategoryTheory.EnrichedFunctorCat.leftKanTensorInv_gradedMap
#check CategoryTheory.EnrichedFunctorCat.leftKanTensorHom_gradedMap
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanTensorHom
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanTensorHom_unit
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanTensorInv
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanTensorInv_unit
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanTensorHom_inv
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanTensorInv_hom
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanTensorIso
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanTensorIso_hom
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanTensorIso_inv
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanTensorInv_ι
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanTensorHom_ι
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanTensorHom_naturality
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanTensorHom_scalar_naturality
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanTensorInv_naturality
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanTensorInv_scalar_naturality
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanTensorNatIso
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanTensorNatIso_hom_app
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanTensorNatIso_inv_app
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanTensorInv_gradedMap
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanTensorHom_gradedMap
#lint only unusedArguments in MathlibExt.CategoryTheory.Enriched.LeftKanTensor
