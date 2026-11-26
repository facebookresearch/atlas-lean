/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module

import MathlibExt.CategoryTheory.Enriched.ScalarCotensor
import Batteries.Tactic.Lint

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 512
noncomputable section
universe uI uA uB uV vV
open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedFunctorCat
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {I : Type uI} [EnrichedCategory V I]

example (M : V) (F : EnrichedFunctor V I V) (a b : I) :
    (EnrichedFunctor.cotensor M F).map a b =
      F.map a b ≫ MonoidalClosed.curry (eComp V M (F.obj a) (F.obj b)) :=
  EnrichedFunctor.cotensor_map M F a b

example (M : V) (F : EnrichedFunctor V I V) (a b : I) :
    MonoidalClosed.uncurry (A := M)
        (MonoidalClosed.uncurry ((EnrichedFunctor.cotensor M F).map a b)) =
      (α_ M ((ihom M).obj (F.obj a)) (a ⟶[V] b)).inv ≫
        ((ihom.ev M).app (F.obj a) ▷ (a ⟶[V] b)) ≫ MonoidalClosed.uncurry (F.map a b) :=
  EnrichedFunctor.cotensor_doubleUncurry M F a b

example (Γ : Center V) (F G : EnrichedFunctorCat V I)
    (t : GradedNatTrans Γ F.toEnrichedFunctor G.toEnrichedFunctor) (a b : I) :
    MonoidalClosed.uncurry (F.toEnrichedFunctor.map a b) ≫
        component (gradedCotensorEquiv Γ F G t) b =
      (component (gradedCotensorEquiv Γ F G t) a ⊗ₘ 𝟙 (a ⟶[V] b)) ≫
        MonoidalClosed.uncurry ((cotensorObject Γ.1 G).toEnrichedFunctor.map a b) :=
  (gradedCotensorEquiv Γ F G t).uncurriedNaturality a b

example (Γ : Center V) (F G : EnrichedFunctorCat V I)
    (t : GradedNatTrans Γ F.toEnrichedFunctor G.toEnrichedFunctor) :
    (gradedCotensorEquiv Γ F G).symm (gradedCotensorEquiv Γ F G t) = t :=
  (gradedCotensorEquiv Γ F G).symm_apply_apply t

example (Γ : Center V) (F G : EnrichedFunctorCat V I) (t : F ⟶ cotensorObject Γ.1 G) :
    gradedCotensorEquiv Γ F G ((gradedCotensorEquiv Γ F G).symm t) = t :=
  (gradedCotensorEquiv Γ F G).apply_symm_apply t

example (Γ : Center V) (F G : EnrichedFunctorCat V I) (t : F ⟶ cotensorObject Γ.1 G) (a : I) :
    ((gradedCotensorEquiv Γ F G).symm t).app a =
      MonoidalClosed.curry ((Γ.2.β (F.toEnrichedFunctor.obj a)).inv ≫
        MonoidalClosed.uncurry (component t a)) :=
  (congrArg (fun x => x.app a) (gradedCotensorEquiv_symm_apply Γ F G t)).trans
    (cotensorToGraded_app Γ F G t a)

example (Γ : Center V) {F' F G : EnrichedFunctorCat V I} (p : F' ⟶ F)
    (t : GradedNatTrans Γ F.toEnrichedFunctor G.toEnrichedFunctor) :
    gradedToCotensor Γ F' G (gradedPrecomp Γ p t) = p ≫ gradedToCotensor Γ F G t :=
  gradedToCotensor_precomp Γ p t

example (Γ : Center V) {F G H : EnrichedFunctorCat V I}
    (t : GradedNatTrans Γ F.toEnrichedFunctor G.toEnrichedFunctor) (q : G ⟶ H) :
    gradedToCotensor Γ F H (gradedPostcomp Γ t q) =
      gradedToCotensor Γ F G t ≫ cotensorMap Γ.1 q :=
  gradedToCotensor_postcomp Γ t q

example {Γ Γ' : Center V} (u : Γ ⟶ Γ') (F G : EnrichedFunctorCat V I)
    (t : GradedNatTrans Γ' F.toEnrichedFunctor G.toEnrichedFunctor) :
    gradedToCotensor Γ F G (GradedNatTrans.regrade u t) =
      gradedToCotensor Γ' F G t ≫ cotensorScalarMap u.f G :=
  gradedToCotensor_regrade u F G t

example (M : V) {F G H : EnrichedFunctorCat V I} (t : F ⟶ G) (s : G ⟶ H) :
    (cotensor M).map (t ≫ s) = (cotensor M).map t ≫ (cotensor M).map s :=
  (cotensor M).map_comp t s

example {M N : V} (u : M ⟶ N) (F : EnrichedFunctorCat V I) (a : I) :
    component (cotensorScalarMap u F) a = (MonoidalClosed.pre u).app (F.toEnrichedFunctor.obj a) :=
  cotensorScalarMap_component u F a

example {M N P : V} (u : M ⟶ N) (v : N ⟶ P) (F : EnrichedFunctorCat V I) :
    cotensorScalarMap (u ≫ v) F = cotensorScalarMap v F ≫ cotensorScalarMap u F :=
  cotensorScalarMap_comp u v F

example {M N : V} (u : M ⟶ N) {F G : EnrichedFunctorCat V I} (t : F ⟶ G) :
    cotensorMap N t ≫ cotensorScalarMap u G = cotensorScalarMap u F ≫ cotensorMap M t :=
  cotensorScalarMap_naturality u t

example : True := by
  fail_if_success letI : Category.{vV} I := by infer_instance
  trivial

example [Category.{vV} I] : True := by
  let : Category.{vV} I := inferInstance
  trivial

example : True := by
  fail_if_success letI : Limits.HasColimitsOfSize.{uI, uI} V := by infer_instance
  trivial

example [Limits.HasColimitsOfSize.{uI, uI} V] : True := by
  let : Limits.HasColimitsOfSize.{uI, uI} V := inferInstance
  trivial

variable {A : Type uA} [EnrichedCategory V A] {B : Type uB} [EnrichedCategory V B]

example (j : EnrichedFunctor V A B) (M : V) (Y : EnrichedFunctorCat V B) (a : A) :
    component (cotensorRestrictionIso j M Y).hom a =
      𝟙 ((ihom M).obj (Y.toEnrichedFunctor.obj (j.obj a))) :=
  cotensorRestrictionIso_hom_component j M Y a

example (j : EnrichedFunctor V A B) (M : V) {F G : EnrichedFunctorCat V B} (t : F ⟶ G) :
    cotensorMap M (restrictionMap j t) ≫ (cotensorRestrictionIso j M G).hom =
      (cotensorRestrictionIso j M F).hom ≫ restrictionMap j (cotensorMap M t) :=
  cotensorRestrictionIso_naturality j M t

example (j : EnrichedFunctor V A B) {M N : V} (u : M ⟶ N) (Y : EnrichedFunctorCat V B) :
    cotensorScalarMap u (restrictionObject j Y) ≫ (cotensorRestrictionIso j M Y).hom =
      (cotensorRestrictionIso j N Y).hom ≫ restrictionMap j (cotensorScalarMap u Y) :=
  cotensorRestrictionIso_scalar_naturality j u Y

end CategoryTheory.EnrichedFunctorCat


#check CategoryTheory.EnrichedFunctor.cotensor
#check CategoryTheory.EnrichedFunctor.cotensor_eq
#check CategoryTheory.EnrichedFunctor.cotensor_map
#check CategoryTheory.EnrichedFunctor.cotensor_doubleUncurry
#check CategoryTheory.EnrichedFunctorCat.cotensorObject
#check CategoryTheory.EnrichedFunctorCat.cotensorOfLeftComponents
#check CategoryTheory.EnrichedFunctorCat.cotensorOfLeftComponents_component
#check CategoryTheory.EnrichedFunctorCat.cotensorComponent_naturality
#check CategoryTheory.EnrichedFunctorCat.cotensorOfLeftComponents_reconstruct
#check CategoryTheory.EnrichedFunctorCat.cotensorMap
#check CategoryTheory.EnrichedFunctorCat.cotensorMap_component
#check CategoryTheory.EnrichedFunctorCat.cotensor
#check CategoryTheory.EnrichedFunctorCat.cotensorScalarMap
#check CategoryTheory.EnrichedFunctorCat.cotensorScalarMap_component
#check CategoryTheory.EnrichedFunctorCat.cotensorScalarMap_id
#check CategoryTheory.EnrichedFunctorCat.cotensorScalarMap_comp
#check CategoryTheory.EnrichedFunctorCat.cotensorScalarMap_naturality
#check CategoryTheory.EnrichedFunctorCat.gradedToCotensor
#check CategoryTheory.EnrichedFunctorCat.gradedToCotensor_component
#check CategoryTheory.EnrichedFunctorCat.cotensorToGraded
#check CategoryTheory.EnrichedFunctorCat.cotensorToGraded_app
#check CategoryTheory.EnrichedFunctorCat.cotensorToGraded_gradeFirst
#check CategoryTheory.EnrichedFunctorCat.cotensorToGraded_toCotensor
#check CategoryTheory.EnrichedFunctorCat.gradedToCotensor_fromCotensor
#check CategoryTheory.EnrichedFunctorCat.gradedCotensorEquiv
#check CategoryTheory.EnrichedFunctorCat.gradedCotensorEquiv_apply
#check CategoryTheory.EnrichedFunctorCat.gradedCotensorEquiv_symm_apply
#check CategoryTheory.EnrichedFunctorCat.gradedToCotensor_precomp
#check CategoryTheory.EnrichedFunctorCat.gradedToCotensor_postcomp
#check CategoryTheory.EnrichedFunctorCat.cotensorToGraded_precomp
#check CategoryTheory.EnrichedFunctorCat.cotensorToGraded_postcomp
#check CategoryTheory.EnrichedFunctorCat.gradedToCotensor_regrade
#check CategoryTheory.EnrichedFunctorCat.cotensorToGraded_regrade
#check CategoryTheory.EnrichedFunctorCat.cotensorRestrictionIso
#check CategoryTheory.EnrichedFunctorCat.cotensorRestrictionIso_hom_component
#check CategoryTheory.EnrichedFunctorCat.cotensorRestrictionIso_inv_component
#check CategoryTheory.EnrichedFunctorCat.cotensorRestrictionIso_naturality
#check CategoryTheory.EnrichedFunctorCat.cotensorRestrictionIso_scalar_naturality

#print axioms CategoryTheory.EnrichedFunctor.cotensor
#print axioms CategoryTheory.EnrichedFunctor.cotensor_eq
#print axioms CategoryTheory.EnrichedFunctor.cotensor_map
#print axioms CategoryTheory.EnrichedFunctor.cotensor_doubleUncurry
#print axioms CategoryTheory.EnrichedFunctorCat.cotensorObject
#print axioms CategoryTheory.EnrichedFunctorCat.cotensorOfLeftComponents
#print axioms CategoryTheory.EnrichedFunctorCat.cotensorOfLeftComponents_component
#print axioms CategoryTheory.EnrichedFunctorCat.cotensorComponent_naturality
#print axioms CategoryTheory.EnrichedFunctorCat.cotensorOfLeftComponents_reconstruct
#print axioms CategoryTheory.EnrichedFunctorCat.cotensorMap
#print axioms CategoryTheory.EnrichedFunctorCat.cotensorMap_component
#print axioms CategoryTheory.EnrichedFunctorCat.cotensor
#print axioms CategoryTheory.EnrichedFunctorCat.cotensorScalarMap
#print axioms CategoryTheory.EnrichedFunctorCat.cotensorScalarMap_component
#print axioms CategoryTheory.EnrichedFunctorCat.cotensorScalarMap_id
#print axioms CategoryTheory.EnrichedFunctorCat.cotensorScalarMap_comp
#print axioms CategoryTheory.EnrichedFunctorCat.cotensorScalarMap_naturality
#print axioms CategoryTheory.EnrichedFunctorCat.gradedToCotensor
#print axioms CategoryTheory.EnrichedFunctorCat.gradedToCotensor_component
#print axioms CategoryTheory.EnrichedFunctorCat.cotensorToGraded
#print axioms CategoryTheory.EnrichedFunctorCat.cotensorToGraded_app
#print axioms CategoryTheory.EnrichedFunctorCat.cotensorToGraded_gradeFirst
#print axioms CategoryTheory.EnrichedFunctorCat.cotensorToGraded_toCotensor
#print axioms CategoryTheory.EnrichedFunctorCat.gradedToCotensor_fromCotensor
#print axioms CategoryTheory.EnrichedFunctorCat.gradedCotensorEquiv
#print axioms CategoryTheory.EnrichedFunctorCat.gradedCotensorEquiv_apply
#print axioms CategoryTheory.EnrichedFunctorCat.gradedCotensorEquiv_symm_apply
#print axioms CategoryTheory.EnrichedFunctorCat.gradedToCotensor_precomp
#print axioms CategoryTheory.EnrichedFunctorCat.gradedToCotensor_postcomp
#print axioms CategoryTheory.EnrichedFunctorCat.cotensorToGraded_precomp
#print axioms CategoryTheory.EnrichedFunctorCat.cotensorToGraded_postcomp
#print axioms CategoryTheory.EnrichedFunctorCat.gradedToCotensor_regrade
#print axioms CategoryTheory.EnrichedFunctorCat.cotensorToGraded_regrade
#print axioms CategoryTheory.EnrichedFunctorCat.cotensorRestrictionIso
#print axioms CategoryTheory.EnrichedFunctorCat.cotensorRestrictionIso_hom_component
#print axioms CategoryTheory.EnrichedFunctorCat.cotensorRestrictionIso_inv_component
#print axioms CategoryTheory.EnrichedFunctorCat.cotensorRestrictionIso_naturality
#print axioms CategoryTheory.EnrichedFunctorCat.cotensorRestrictionIso_scalar_naturality

#lint only unusedArguments in MathlibExt.CategoryTheory.Enriched.ScalarCotensor
