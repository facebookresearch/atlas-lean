/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

import MathlibExt.CategoryTheory.Enriched.Limits.WeightedEnd

/-! Public API tests for enriched weighted ends. -/

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory MonoidalClosed

universe uI uB vI uV vV

namespace CategoryTheory.Enriched.WeightedEndTests

attribute [local instance] MonoidalClosed.enrichedCategorySelf

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
variable {I : Type uI} [EnrichedCategory V I]

example : True := by
  fail_if_success exact inferInstanceAs (Category I)
  trivial

#check weightedEnd
#check weightedEnd.objects
#check weightedEnd.relations
#check weightedEnd.leftMap
#check weightedEnd.rightMap
#check weightedEnd.π
#check weightedEnd.condition
#check weightedEnd.lift
#check weightedEnd.lift_π
#check weightedEnd.hom_ext
#check weightedEnd.mapWeight
#check weightedEnd.mapDiagram
#check weightedEnd.mapWeight_π
#check weightedEnd.mapDiagram_π
#check weightedEnd.mapWeight_id
#check weightedEnd.mapWeight_comp
#check weightedEnd.mapDiagram_id
#check weightedEnd.mapDiagram_comp
#check weightedEnd.yonedaIso
#check weightedEnd.rightKanWeight
#check weightedEnd.rightKanEndObject
#check weightedEnd.rightKanActionComponent
#check weightedEnd.rightKanEndAction
#check weightedEnd.rightKanEndAction_π
#check weightedEnd.rightKanEndMap
#check weightedEnd.rightKanEndMap_uncurry
#check weightedEnd.rightKanEndMap_id
#check weightedEnd.rightKanEndMap_comp
#check weightedEnd.rightKanEndMap_π
#check weightedEnd.rightKanEndFunctor
#check weightedEnd.rightKanEndFunctor_obj
#check weightedEnd.rightKanEndFunctor_map

section MinimalPresentation

variable (W F : EnrichedFunctor V I V)

private abbrev clientEndObjects (a : I) : V :=
  (ihom (W.obj a)).obj (F.obj a)

private abbrev clientEndRelations (p : I × I) : V :=
  (ihom ((p.1 ⟶[V] p.2) ⊗ W.obj p.1)).obj (F.obj p.2)

private abbrev clientEndLeft
    [HasProduct (clientEndObjects W F)]
    [HasProduct (clientEndRelations W F)] :
    (∏ᶜ clientEndObjects W F) ⟶ ∏ᶜ clientEndRelations W F :=
  Pi.lift fun p ↦ MonoidalClosed.curry <|
    (α_ (p.1 ⟶[V] p.2) (W.obj p.1)
        (∏ᶜ clientEndObjects W F)).hom ≫
      ((p.1 ⟶[V] p.2) ◁
        ((W.obj p.1) ◁ Pi.π (clientEndObjects W F) p.1)) ≫
      ((p.1 ⟶[V] p.2) ◁
        (ihom.ev (W.obj p.1)).app (F.obj p.1)) ≫
      (β_ (p.1 ⟶[V] p.2) (F.obj p.1)).hom ≫
      MonoidalClosed.uncurry (F.map p.1 p.2)

private abbrev clientEndRight
    [HasProduct (clientEndObjects W F)]
    [HasProduct (clientEndRelations W F)] :
    (∏ᶜ clientEndObjects W F) ⟶ ∏ᶜ clientEndRelations W F :=
  Pi.lift fun p ↦ MonoidalClosed.curry <|
    (((β_ (p.1 ⟶[V] p.2) (W.obj p.1)).hom ≫
        MonoidalClosed.uncurry (W.map p.1 p.2)) ⊗ₘ
          𝟙 (∏ᶜ clientEndObjects W F)) ≫
      ((W.obj p.2) ◁ Pi.π (clientEndObjects W F) p.2) ≫
      (ihom.ev (W.obj p.2)).app (F.obj p.2)

variable [HasProduct (clientEndObjects W F)]
  [HasProduct (clientEndRelations W F)]
  [HasEqualizer (clientEndLeft W F) (clientEndRight W F)]

example : V := weightedEnd W F

example (a : I) :
    weightedEnd W F ⟶ (ihom (W.obj a)).obj (F.obj a) :=
  weightedEnd.π W F a

end MinimalPresentation

section UniversalProperty

variable (W F : EnrichedFunctor V I V)
variable [HasProductsOfShape I V] [HasProductsOfShape (I × I) V]
  [HasEqualizers V]

example : V := weightedEnd W F

example (a : I) :
    weightedEnd W F ⟶ (ihom (W.obj a)).obj (F.obj a) :=
  weightedEnd.π W F a

example (a b : I) := weightedEnd.condition W F a b

example : weightedEnd W F ⟶ weightedEnd W F :=
  weightedEnd.lift W F (weightedEnd.π W F)
    (weightedEnd.condition W F)

example (a : I) :
    weightedEnd.lift W F (weightedEnd.π W F)
          (weightedEnd.condition W F) ≫
        weightedEnd.π W F a =
      weightedEnd.π W F a :=
  weightedEnd.lift_π W F (weightedEnd.π W F)
    (weightedEnd.condition W F) a

example :
    weightedEnd.lift W F (weightedEnd.π W F)
        (weightedEnd.condition W F) =
      𝟙 (weightedEnd W F) := by
  apply weightedEnd.hom_ext
  intro a
  simp

end UniversalProperty

section Variance

variable (W W' F F' : EnrichedFunctor V I V)
variable [HasProductsOfShape I V] [HasProductsOfShape (I × I) V]
  [HasEqualizers V]

variable
  (d : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F F')
  (w : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) W' W)

example : weightedEnd W F ⟶ weightedEnd W F' :=
  weightedEnd.mapDiagram W F F' d

example (a : I) :
    weightedEnd.mapDiagram W F F' d ≫ weightedEnd.π W F' a =
      weightedEnd.π W F a ≫
        (ihom (W.obj a)).map
          ((eHomEquiv V).symm (d.app a)) :=
  weightedEnd.mapDiagram_π W F F' d a

example : weightedEnd W F ⟶ weightedEnd W' F :=
  weightedEnd.mapWeight W F W' w

example (a : I) :
    weightedEnd.mapWeight W F W' w ≫ weightedEnd.π W' F a =
      weightedEnd.π W F a ≫
        (MonoidalClosed.pre ((eHomEquiv V).symm (w.app a))).app
          (F.obj a) :=
  weightedEnd.mapWeight_π W F W' w a

example :
    weightedEnd.mapDiagram W F F (GradedNatTrans.unitId F) =
      𝟙 (weightedEnd W F) :=
  weightedEnd.mapDiagram_id W F

example :
    weightedEnd.mapWeight W F W (GradedNatTrans.unitId W) =
      𝟙 (weightedEnd W F) :=
  weightedEnd.mapWeight_id W F

example (F'' : EnrichedFunctor V I V)
    (e : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F' F'') :
    weightedEnd.mapDiagram W F F' d ≫
        weightedEnd.mapDiagram W F' F'' e =
      weightedEnd.mapDiagram W F F'' (GradedNatTrans.unitComp d e) :=
  weightedEnd.mapDiagram_comp W F F' F'' d e

example (W'' : EnrichedFunctor V I V)
    (v : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) W'' W') :
    weightedEnd.mapWeight W F W' w ≫
        weightedEnd.mapWeight W' F W'' v =
      weightedEnd.mapWeight W F W'' (GradedNatTrans.unitComp v w) :=
  weightedEnd.mapWeight_comp W F W' W'' w v

example (W'' : EnrichedFunctor V I V)
    (_v : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) W'' W') : True := by
  fail_if_success
    exact (weightedEnd.mapWeight W F W' w ≫
        weightedEnd.mapWeight W' F W'' _v =
      weightedEnd.mapWeight W F W'' (GradedNatTrans.unitComp w _v))
  trivial

example : True := by
  fail_if_success
    exact (weightedEnd.mapDiagram W F F' d :
      weightedEnd W F' ⟶ weightedEnd W F)
  fail_if_success
    exact (weightedEnd.mapWeight W F W' w :
      weightedEnd W' F ⟶ weightedEnd W F)
  trivial

end Variance

private abbrev clientCovariantRepresentable (c : I) : EnrichedFunctor V I V :=
  EnrichedFunctor.covariantRepresentable V I c

section Yoneda

variable (F : EnrichedFunctor V I V) (c : I)
variable [HasProductsOfShape I V] [HasProductsOfShape (I × I) V]
  [HasEqualizers V]

example : weightedEnd (clientCovariantRepresentable c) F ≅ F.obj c :=
  weightedEnd.yonedaIso c F

example :
    weightedEnd (clientCovariantRepresentable c) F ⟶ F.obj c :=
  (weightedEnd.yonedaIso c F).hom

example :
    F.obj c ⟶ weightedEnd (clientCovariantRepresentable c) F :=
  (weightedEnd.yonedaIso c F).inv

example :
    (weightedEnd.yonedaIso c F).hom ≫
        (weightedEnd.yonedaIso c F).inv =
      𝟙 (weightedEnd (clientCovariantRepresentable c) F) :=
  (weightedEnd.yonedaIso c F).hom_inv_id

example :
    (weightedEnd.yonedaIso c F).inv ≫
        (weightedEnd.yonedaIso c F).hom =
      𝟙 (F.obj c) :=
  (weightedEnd.yonedaIso c F).inv_hom_id

example : True := by
  fail_if_success
    exact (weightedEnd.yonedaIso c F :
      F.obj c ≅ weightedEnd (clientCovariantRepresentable c) F)
  trivial

end Yoneda

section RightKanEnd

variable {A : Type uI} [EnrichedCategory V A]
  {B : Type uB} [EnrichedCategory V B]
variable (u : EnrichedFunctor V A B) (X : EnrichedFunctor V A V)
  [∀ b : B, HasProduct
    (weightedEnd.objects (weightedEnd.rightKanWeight u b) X)]
  [∀ b : B, HasProduct
    (weightedEnd.relations (weightedEnd.rightKanWeight u b) X)]
  [∀ b : B, HasEqualizer
    (weightedEnd.leftMap (weightedEnd.rightKanWeight u b) X)
    (weightedEnd.rightMap (weightedEnd.rightKanWeight u b) X)]

example : True := by
  fail_if_success exact inferInstanceAs (Category A)
  fail_if_success exact inferInstanceAs (Category B)
  trivial

example (b : B) : EnrichedFunctor V A V :=
  weightedEnd.rightKanWeight u b

example (b : B) : V :=
  weightedEnd.rightKanEndObject u X b

example (b c : B) :
    (b ⟶[V] c) ⊗ weightedEnd.rightKanEndObject u X b ⟶
      weightedEnd.rightKanEndObject u X c :=
  weightedEnd.rightKanEndAction u X b c

example (b c : B) :
    (b ⟶[V] c) ⟶
      (ihom (weightedEnd.rightKanEndObject u X b)).obj
        (weightedEnd.rightKanEndObject u X c) :=
  weightedEnd.rightKanEndMap u X b c

example (b c : B) :
    MonoidalClosed.uncurry (weightedEnd.rightKanEndMap u X b c) =
      (β_ (b ⟶[V] c) (weightedEnd.rightKanEndObject u X b)).inv ≫
        weightedEnd.rightKanEndAction u X b c :=
  weightedEnd.rightKanEndMap_uncurry u X b c

example (b c : B) (a : A) :
    MonoidalClosed.uncurry (weightedEnd.rightKanEndMap u X b c) ≫
        weightedEnd.π (weightedEnd.rightKanWeight u c) X a =
      (β_ (b ⟶[V] c) (weightedEnd.rightKanEndObject u X b)).inv ≫
        weightedEnd.rightKanActionComponent u X b c a :=
  weightedEnd.rightKanEndMap_π u X b c a

example (b : B) :
    eId V b ≫ weightedEnd.rightKanEndMap u X b b =
      eId V (weightedEnd.rightKanEndObject u X b) :=
  weightedEnd.rightKanEndMap_id u X b

example (b c d : B) :
    eComp V b c d ≫ weightedEnd.rightKanEndMap u X b d =
      (weightedEnd.rightKanEndMap u X b c ⊗ₘ
        weightedEnd.rightKanEndMap u X c d) ≫
      eComp V (weightedEnd.rightKanEndObject u X b)
        (weightedEnd.rightKanEndObject u X c)
        (weightedEnd.rightKanEndObject u X d) :=
  weightedEnd.rightKanEndMap_comp u X b c d

example : EnrichedFunctor V B V :=
  weightedEnd.rightKanEndFunctor u X

example (b : B) :
    (weightedEnd.rightKanEndFunctor u X).obj b =
      weightedEnd.rightKanEndObject u X b :=
  weightedEnd.rightKanEndFunctor_obj u X b

example (b c : B) :
    (weightedEnd.rightKanEndFunctor u X).map b c =
      weightedEnd.rightKanEndMap u X b c :=
  weightedEnd.rightKanEndFunctor_map u X b c

end RightKanEnd

section Universes

#check @weightedEnd.{0, 0, 0}
#check @weightedEnd.{1, 1, 1}
#check @weightedEnd.{0, 0, 1}
#check @weightedEnd.{1, 1, 0}
#check @weightedEnd.yonedaIso.{0, 0, 0}
#check @weightedEnd.yonedaIso.{1, 1, 1}
#check @weightedEnd.yonedaIso.{0, 0, 1}
#check @weightedEnd.yonedaIso.{1, 1, 0}
#check @weightedEnd.mapDiagram_id.{0, 0, 1}
#check @weightedEnd.mapDiagram_comp.{1, 1, 0}
#check @weightedEnd.mapWeight_id.{0, 0, 1}
#check @weightedEnd.mapWeight_comp.{1, 1, 0}
#check @weightedEnd.rightKanWeight.{0, 0, 0}
#check @weightedEnd.rightKanWeight.{1, 0, 1}
#check @weightedEnd.rightKanEndFunctor.{0, 0, 0}
#check @weightedEnd.rightKanEndFunctor.{0, 1, 0}
#check @weightedEnd.rightKanEndFunctor.{1, 0, 1}
#check @weightedEnd.rightKanEndMap_comp.{1, 1, 0}

end Universes

section OrdinarySourceRegression

variable {J : Type uI} [Category.{vI} J] [EnrichedOrdinaryCategory V J]
variable (W F : EnrichedFunctor V J V)
  [HasProductsOfShape J V] [HasProductsOfShape (J × J) V] [HasEqualizers V]

example : V := weightedEnd W F

example (a : J) :
    weightedEnd W F ⟶ (ihom (W.obj a)).obj (F.obj a) :=
  weightedEnd.π W F a

example (c : J) :
    weightedEnd (EnrichedFunctor.covariantRepresentable V J c) F ≅ F.obj c :=
  weightedEnd.yonedaIso c F

end OrdinarySourceRegression

section PrivateNonleakage

#guard_msgs (error, substring := true) in
#check CategoryTheory.Enriched.weightedEndObjects
#guard_msgs (error, substring := true) in
#check CategoryTheory.Enriched.weightedEndRelations
#guard_msgs (error, substring := true) in
#check CategoryTheory.Enriched.tensorUncurry_comp
#guard_msgs (error, substring := true) in
#check CategoryTheory.Enriched.gradedComponent
#guard_msgs (error, substring := true) in
#check CategoryTheory.Enriched.covariantRepresentable
#guard_msgs (error, substring := true) in
#check CategoryTheory.Enriched.weightedEnd.yonedaEvaluation
#guard_msgs (error, substring := true) in
#check CategoryTheory.Enriched.weightedEnd.yonedaCoevaluation

end PrivateNonleakage

#print axioms CategoryTheory.Enriched.weightedEnd.mapWeight
#print axioms CategoryTheory.Enriched.weightedEnd.mapDiagram
#print axioms CategoryTheory.Enriched.weightedEnd.mapWeight_id
#print axioms CategoryTheory.Enriched.weightedEnd.mapWeight_comp
#print axioms CategoryTheory.Enriched.weightedEnd.mapDiagram_id
#print axioms CategoryTheory.Enriched.weightedEnd.mapDiagram_comp
#print axioms CategoryTheory.Enriched.weightedEnd.yonedaIso
#print axioms CategoryTheory.Enriched.weightedEnd.rightKanActionComponent
#print axioms CategoryTheory.Enriched.weightedEnd.rightKanEndAction
#print axioms CategoryTheory.Enriched.weightedEnd.rightKanEndAction_π
#print axioms CategoryTheory.Enriched.weightedEnd.rightKanEndMap
#print axioms CategoryTheory.Enriched.weightedEnd.rightKanEndMap_id
#print axioms CategoryTheory.Enriched.weightedEnd.rightKanEndMap_comp
#print axioms CategoryTheory.Enriched.weightedEnd.rightKanEndMap_π
#print axioms CategoryTheory.Enriched.weightedEnd.rightKanEndFunctor

end CategoryTheory.Enriched.WeightedEndTests
