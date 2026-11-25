/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

import MathlibExt.CategoryTheory.Enriched.LeftKanGradedAction
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

example {Γ Δ : Center V} {X X' X'' : EnrichedFunctorCat V A}
    (t : GradedNatTrans Γ X.toEnrichedFunctor X'.toEnrichedFunctor)
    (u : GradedNatTrans Δ X'.toEnrichedFunctor X''.toEnrichedFunctor) :
    leftKanGradedMap j (Γ ⊗ Δ) (GradedNatTrans.tensorComp t u) =
      GradedNatTrans.tensorComp (leftKanGradedMap j Γ t) (leftKanGradedMap j Δ u) :=
  leftKanGradedMap_tensorComp j t u

example {Γ Δ : Center V} (h : Γ ⟶ Δ) {X X' : EnrichedFunctorCat V A}
    (t : GradedNatTrans Δ X.toEnrichedFunctor X'.toEnrichedFunctor) :
    leftKanGradedMap j Γ (GradedNatTrans.regrade h t) =
      GradedNatTrans.regrade h (leftKanGradedMap j Δ t) :=
  leftKanGradedMap_regrade j h t

example (Γ : Center V) {X X' : EnrichedFunctorCat V A}
    (t : GradedNatTrans Γ X.toEnrichedFunctor X'.toEnrichedFunctor) :
    gradedPrecomp Γ (leftKanUnit j X) (GradedNatTrans.restrict j (leftKanGradedMap j Γ t)) =
      gradedPostcomp Γ t (leftKanUnit j X') :=
  leftKanGradedMap_eta j Γ t

example {X X' : EnrichedFunctorCat V A} (t : X ⟶ X') :
    leftKanGradedMap j ((Center.ofBraided V).obj (𝟙_ V)) t = (leftKan j).map t :=
  leftKanGradedMap_unit j t

example (X : EnrichedFunctorCat V A) :
    leftKanGradedMap j ((Center.ofBraided V).obj (𝟙_ V)) (𝟙 X) = 𝟙 (leftKanObject j X) :=
  leftKanGradedMap_id j X

example {Γ Δ : Center V} {X' X : EnrichedFunctorCat V A} (Y : EnrichedFunctorCat V B)
    (s : GradedNatTrans Δ X'.toEnrichedFunctor X.toEnrichedFunctor)
    (t : GradedNatTrans Γ (leftKanObject j X).toEnrichedFunctor Y.toEnrichedFunctor) :
    leftKanGradedHomEquiv j (Δ ⊗ Γ) X' Y
        (GradedNatTrans.tensorComp (leftKanGradedMap j Δ s) t) =
      GradedNatTrans.tensorComp s (leftKanGradedHomEquiv j Γ X Y t) :=
  leftKanGradedHomEquiv_tensorComp_left j Y s t

example {Γ Δ : Center V} (X : EnrichedFunctorCat V A) {Y Y' : EnrichedFunctorCat V B}
    (t : GradedNatTrans Γ (leftKanObject j X).toEnrichedFunctor Y.toEnrichedFunctor)
    (u : GradedNatTrans Δ Y.toEnrichedFunctor Y'.toEnrichedFunctor) :
    leftKanGradedHomEquiv j (Γ ⊗ Δ) X Y' (GradedNatTrans.tensorComp t u) =
      GradedNatTrans.tensorComp (leftKanGradedHomEquiv j Γ X Y t) (GradedNatTrans.restrict j u) :=
  leftKanGradedHomEquiv_tensorComp_right j X t u

example {Γ Δ : Center V} {X' X : EnrichedFunctorCat V A} (Y : EnrichedFunctorCat V B)
    (s : GradedNatTrans Δ X'.toEnrichedFunctor X.toEnrichedFunctor)
    (f : GradedNatTrans Γ X.toEnrichedFunctor (restrictionObject j Y).toEnrichedFunctor) :
    (leftKanGradedHomEquiv j (Δ ⊗ Γ) X' Y).symm (GradedNatTrans.tensorComp s f) =
      GradedNatTrans.tensorComp (leftKanGradedMap j Δ s) ((leftKanGradedHomEquiv j Γ X Y).symm f) :=
  leftKanGradedHomEquiv_tensorComp_left_symm j Y s f

example {Γ Δ : Center V} (X : EnrichedFunctorCat V A) {Y Y' : EnrichedFunctorCat V B}
    (f : GradedNatTrans Γ X.toEnrichedFunctor (restrictionObject j Y).toEnrichedFunctor)
    (u : GradedNatTrans Δ Y.toEnrichedFunctor Y'.toEnrichedFunctor) :
    (leftKanGradedHomEquiv j (Γ ⊗ Δ) X Y').symm
        (GradedNatTrans.tensorComp f (GradedNatTrans.restrict j u)) =
      GradedNatTrans.tensorComp ((leftKanGradedHomEquiv j Γ X Y).symm f) u :=
  leftKanGradedHomEquiv_tensorComp_right_symm j X f u

example (Γ : Center V) {X X' : EnrichedFunctorCat V A}
    (t : GradedNatTrans Γ X.toEnrichedFunctor X'.toEnrichedFunctor) (b : B) (a : A) :
    (Γ.1 ◁ Enriched.weightedCoend.ι (leftKanWeight j b) X.toEnrichedFunctor a) ≫
        GradedNatTrans.gradeFirstComponent Γ (leftKanGradedMap j Γ t) b =
      (α_ Γ.1 (j.obj a ⟶[V] b) (X.toEnrichedFunctor.obj a)).inv ≫
        ((β_ (j.obj a ⟶[V] b) Γ.1).inv ▷ X.toEnrichedFunctor.obj a) ≫
        (α_ (j.obj a ⟶[V] b) Γ.1 (X.toEnrichedFunctor.obj a)).hom ≫
        ((j.obj a ⟶[V] b) ◁ GradedNatTrans.gradeFirstComponent Γ t a) ≫
        Enriched.weightedCoend.ι (leftKanWeight j b) X'.toEnrichedFunctor a :=
  leftKanGradedMap_gradeFirstComponent_ι j Γ t b a

end CategoryTheory.EnrichedFunctorCat

#check CategoryTheory.EnrichedFunctorCat.leftKanGradedMap
#check CategoryTheory.EnrichedFunctorCat.leftKanGradedMap_tensorComp
#check CategoryTheory.EnrichedFunctorCat.leftKanGradedMap_regrade
#check CategoryTheory.EnrichedFunctorCat.leftKanGradedMap_unit
#check CategoryTheory.EnrichedFunctorCat.leftKanGradedMap_gradeFirstComponent_ι
#check CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_tensorComp_left
#check CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_tensorComp_right
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_eta_restrict
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanGradedMap
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanGradedMap_apply
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanGradedMap_homEquiv
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanGradedMap_eta
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanGradedMap_tensorComp
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanGradedMap_regrade
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_tensorComp_left
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_tensorComp_right
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_tensorComp_left_symm
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_tensorComp_right_symm
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanGradedMap_unit
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanGradedMap_id
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanGradedMap_gradeFirstComponent_ι
#lint only unusedArguments in MathlibExt.CategoryTheory.Enriched.LeftKanGradedAction
