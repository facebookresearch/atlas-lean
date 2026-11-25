/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

import MathlibExt.CategoryTheory.Enriched.LeftKanExtension
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

example (X : EnrichedFunctorCat V A) (b : B) :
    ((leftKan j).obj X).toEnrichedFunctor.obj b =
      Enriched.weightedCoend (leftKanWeight j b) X.toEnrichedFunctor :=
  leftKan_obj j X b

example (X : EnrichedFunctorCat V A) (a : A) (b : B) :
    ((j.obj a ⟶[V] b) ◁ leftKanUnitComponent j X a) ≫
        leftKanCoendAction j X.toEnrichedFunctor (j.obj a) b =
      Enriched.weightedCoend.ι (leftKanWeight j b) X.toEnrichedFunctor a :=
  leftKanUnitComponent_action j X a b

example (X : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V B)
    (f : X ⟶ restrictionObject j Y) :
    leftKanHomEquiv j X Y ((leftKanHomEquiv j X Y).symm f) = f :=
  (leftKanHomEquiv j X Y).apply_symm_apply f

example (X : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V B)
    (t : leftKanObject j X ⟶ Y) :
    (leftKanHomEquiv j X Y).symm (leftKanHomEquiv j X Y t) = t :=
  (leftKanHomEquiv j X Y).symm_apply_apply t

example (X : EnrichedFunctorCat V A) :
    (leftKan j).map ((leftKanRestrictionAdjunction j).unit.app X) ≫
        (leftKanRestrictionAdjunction j).counit.app ((leftKan j).obj X) =
      𝟙 ((leftKan j).obj X) :=
  leftKanRestrictionAdjunction_left_triangle j X

example (Y : EnrichedFunctorCat V B) :
    (leftKanRestrictionAdjunction j).unit.app ((restriction j).obj Y) ≫
        (restriction j).map ((leftKanRestrictionAdjunction j).counit.app Y) =
      𝟙 ((restriction j).obj Y) :=
  leftKanRestrictionAdjunction_right_triangle j Y

example (Y : EnrichedFunctorCat V B) (b : B) (a : A) :
    Enriched.weightedCoend.ι (leftKanWeight j b) ((restriction j).obj Y).toEnrichedFunctor a ≫
        component ((leftKanRestrictionAdjunction j).counit.app Y) b =
      (β_ (j.obj a ⟶[V] b) (Y.toEnrichedFunctor.obj (j.obj a))).hom ≫
        MonoidalClosed.uncurry (Y.toEnrichedFunctor.map (j.obj a) b) :=
  leftKanRestrictionAdjunction_counit_ι j Y b a

example (Γ : Center V) (X : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V B)
    (t : GradedNatTrans Γ (leftKanObject j X).toEnrichedFunctor Y.toEnrichedFunctor) :
    (leftKanGradedHomEquiv j Γ X Y).symm (leftKanGradedHomEquiv j Γ X Y t) = t :=
  leftKanGradedHomEquiv_left_inverse j Γ X Y t

example (Γ : Center V) (X : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V B)
    (f : GradedNatTrans Γ X.toEnrichedFunctor (restrictionObject j Y).toEnrichedFunctor) :
    leftKanGradedHomEquiv j Γ X Y ((leftKanGradedHomEquiv j Γ X Y).symm f) = f :=
  leftKanGradedHomEquiv_right_inverse j Γ X Y f

example (Γ : Center V) (X : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V B)
    (f : GradedNatTrans Γ X.toEnrichedFunctor (restrictionObject j Y).toEnrichedFunctor)
    (b : B) (a : A) :
    (Γ.1 ◁ Enriched.weightedCoend.ι (leftKanWeight j b) X.toEnrichedFunctor a) ≫
        GradedNatTrans.gradeFirstComponent Γ ((leftKanGradedHomEquiv j Γ X Y).symm f) b =
      (α_ Γ.1 (j.obj a ⟶[V] b) (X.toEnrichedFunctor.obj a)).inv ≫
        ((β_ (j.obj a ⟶[V] b) Γ.1).inv ▷ X.toEnrichedFunctor.obj a) ≫
        (α_ (j.obj a ⟶[V] b) Γ.1 (X.toEnrichedFunctor.obj a)).hom ≫
        ((j.obj a ⟶[V] b) ◁ GradedNatTrans.gradeFirstComponent Γ f a) ≫
        (β_ (j.obj a ⟶[V] b) (Y.toEnrichedFunctor.obj (j.obj a))).hom ≫
        MonoidalClosed.uncurry (Y.toEnrichedFunctor.map (j.obj a) b) :=
  leftKanGradedHomEquiv_symm_gradeFirstComponent_ι j Γ X Y f b a

example (Γ : Center V) {X' X : EnrichedFunctorCat V A} (Y : EnrichedFunctorCat V B)
    (p : X' ⟶ X) (t : GradedNatTrans Γ (leftKanObject j X).toEnrichedFunctor Y.toEnrichedFunctor) :
    leftKanGradedHomEquiv j Γ X' Y (gradedPrecomp Γ ((leftKan j).map p) t) =
      gradedPrecomp Γ p (leftKanGradedHomEquiv j Γ X Y t) :=
  leftKanGradedHomEquiv_naturality_left j Γ Y p t

example (Γ : Center V) (X : EnrichedFunctorCat V A) {Y Y' : EnrichedFunctorCat V B}
    (t : GradedNatTrans Γ (leftKanObject j X).toEnrichedFunctor Y.toEnrichedFunctor) (q : Y ⟶ Y') :
    leftKanGradedHomEquiv j Γ X Y' (gradedPostcomp Γ t q) =
      gradedPostcomp Γ (leftKanGradedHomEquiv j Γ X Y t) ((restriction j).map q) :=
  leftKanGradedHomEquiv_naturality_right j Γ X t q

example {Γ Γ' : Center V} (u : Γ ⟶ Γ') (X : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V B)
    (t : GradedNatTrans Γ' (leftKanObject j X).toEnrichedFunctor Y.toEnrichedFunctor) :
    leftKanGradedHomEquiv j Γ X Y (GradedNatTrans.regrade u t) =
      GradedNatTrans.regrade u (leftKanGradedHomEquiv j Γ' X Y t) :=
  leftKanGradedHomEquiv_regrade j u X Y t

example (X : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V B) :
    leftKanGradedHomEquiv j ((Center.ofBraided V).obj (𝟙_ V)) X Y = leftKanHomEquiv j X Y :=
  leftKanGradedHomEquiv_unit j X Y

example (X : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V B) (M : Vᵒᵖ)
    (t : ULift.{max uA uB vV}
      ((enrichedNatTransYoneda (leftKanObject j X).toEnrichedFunctor Y.toEnrichedFunctor).obj M)) :
    (leftKanEnrichedNatTransYonedaIso j X Y).hom.app M t =
      ULift.up (leftKanGradedHomEquiv j ((Center.ofBraided V).obj M.unop) X Y t.down) :=
  leftKanEnrichedNatTransYonedaIso_hom_app j X Y M t

example (X : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V B)
    (f : X ⟶ restrictionObject j Y) (t : leftKanObject j X ⟶ Y)
    (h : ∀ a, leftKanUnitComponent j X a ≫ component t (j.obj a) = component f a) :
    t = leftKanTransposeMap j X Y f :=
  leftKanTransposeMap_unique_of_unit_components j X Y f t h

end CategoryTheory.EnrichedFunctorCat


#check CategoryTheory.EnrichedFunctorCat.leftKanWeight
#check CategoryTheory.EnrichedFunctorCat.leftKanCoendAction
#check CategoryTheory.EnrichedFunctorCat.leftKanCoendMap
#check CategoryTheory.EnrichedFunctorCat.leftKanCoendFunctor
#check CategoryTheory.EnrichedFunctorCat.leftKan
#check CategoryTheory.EnrichedFunctorCat.leftKanHomEquiv
#check CategoryTheory.EnrichedFunctorCat.leftKanRestrictionAdjunction
#check CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv
#check CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_app
#check CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_symm_gradeFirstComponent_ι
#check CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_naturality_left
#check CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_naturality_right
#check CategoryTheory.EnrichedFunctorCat.leftKanEnrichedNatTransYonedaIso
#check CategoryTheory.EnrichedFunctorCat.leftKanGradedGenerator_ext

#print axioms CategoryTheory.EnrichedFunctorCat.leftKanWeight
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanWeight_eq
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanWeight_obj
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanCoendObject
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanCoendActionComponent
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanCoendActionComponent_eq
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanCoendAction
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanCoendAction_ι
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanCoendMap
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanCoendMap_uncurry
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanCoendMap_id
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanCoendMap_comp
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanCoendFunctor
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanCoendFunctor_obj
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanCoendFunctor_map
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanObject
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanMapComponent
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanMapComponent_ι
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanMapComponent_id
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanMapComponent_comp
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanMap
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanMap_component
#print axioms CategoryTheory.EnrichedFunctorCat.leftKan
#print axioms CategoryTheory.EnrichedFunctorCat.leftKan_obj
#print axioms CategoryTheory.EnrichedFunctorCat.leftKan_fullMap
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanUnitComponent
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanUnitComponent_action
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanUnit
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanUnit_component
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanUnit_natural
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanTransposeCocone
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanTransposeCocone_eq
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanTransposeMapComponent
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanTransposeMapComponent_ι
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanTransposeMap
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanTransposeMap_component
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanHomToRestriction
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanHomToRestriction_component
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanHomToRestriction_transpose
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanTranspose_homToRestriction
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanHomToRestriction_precomp
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanHomToRestriction_postcomp
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanHomEquiv
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanHomEquiv_apply
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanHomEquiv_symm_apply
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanHomEquiv_naturality_left
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanHomEquiv_naturality_right
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanHomEquiv_naturality_left_symm
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanHomEquiv_naturality_right_symm
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanRestrictionAdjunction
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanRestrictionAdjunction_homEquiv
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanRestrictionAdjunction_unit
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanRestrictionAdjunction_counit
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanRestrictionAdjunction_unit_component
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanRestrictionAdjunction_counit_ι
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanRestrictionAdjunction_left_triangle
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanRestrictionAdjunction_right_triangle
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanTransposeMap_unique
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanTransposeMap_unique_of_unit_components
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanTransposeMap_unique_of_generators
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanHomEquiv_symm_ι
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_left_inverse
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_right_inverse
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_gradeFirstComponent
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_app
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_regrade
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_symm_regrade
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_presheaf_naturality
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanEnrichedNatTransYonedaIso
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanEnrichedNatTransYonedaIso_hom_app
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanEnrichedNatTransYonedaIso_inv_app
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_symm_gradeFirstComponent_ι
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_unit_apply
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_unit
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_unit_symm_apply
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanGradedGenerator_ext
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_symm_unique
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_naturality_left
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_naturality_right
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_naturality_left_symm
#print axioms CategoryTheory.EnrichedFunctorCat.leftKanGradedHomEquiv_naturality_right_symm
#lint only unusedArguments in MathlibExt.CategoryTheory.Enriched.LeftKanExtension
