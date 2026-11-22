/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.BasedHomotopyExtension
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHBasedHomotopyExtension
import MathlibExt.CategoryTheory.Enriched.ScalarFreeTensor
import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting

/-!
# Endpoint lifting and closure for native based homotopy extension

The full endpoint evaluation dictionary identifies native based HEP with the
left lifting class of the actual scalar-cotensor evaluations. Coproduct,
pushout, continuous ordinal and retract closure retain the caller's complete
maps and cocones. The original scalar/free comparison transports pointed
boundary HEP for every enriched index category.

The existing public namespace is retained for these index-generic APIs.
-/

set_option autoImplicit false
noncomputable section

universe u v w uC vC

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open CategoryTheory.EnrichedFunctorCat MonoidalCategory HomotopicalAlgebra
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.OriginalIClosedHomotopyExtension

namespace Internal

variable {C : Type uC} [Category.{vC} C]
  {T R : C ⥤ C} (adj : T ⊣ R) (e : 𝟭 C ⟶ T)

/-- Evaluate the actual right-adjoint object at the supplied original endpoint. -/
def endpointEvaluation (Y : C) : R.obj Y ⟶ Y :=
  e.app (R.obj Y) ≫ adj.counit.app Y

/-- The complete evaluation family is natural under every original target map. -/
@[reassoc]
theorem endpointEvaluation_naturality {Y Z : C} (g : Y ⟶ Z) :
    R.map g ≫ endpointEvaluation adj e Z = endpointEvaluation adj e Y ≫ g := by
  have he : R.map g ≫ e.app (R.obj Z) = e.app (R.obj Y) ≫ T.map (R.map g) :=
    e.naturality (R.map g)
  have hc : T.map (R.map g) ≫ adj.counit.app Z = adj.counit.app Y ≫ g :=
    adj.counit.naturality g
  rw [endpointEvaluation, endpointEvaluation, ← Category.assoc,
    he, Category.assoc, hc, ← Category.assoc]

/-- The original evaluations form one whole natural transformation. -/
def endpointEvaluationNatTrans : R ⟶ 𝟭 C where
  app := endpointEvaluation adj e
  naturality _ _ g := endpointEvaluation_naturality adj e g

/-- Endpoint restriction of the inverse transpose is the actual evaluation composite. -/
@[reassoc]
theorem endpoint_untranspose {X Y : C} (k : X ⟶ R.obj Y) :
    e.app X ≫ (adj.homEquiv X Y).symm k = k ≫ endpointEvaluation adj e Y := by
  rw [adj.homEquiv_counit, ← Category.assoc, ← e.naturality]
  exact Category.assoc _ _ _

/-- The converse dictionary retains the original homotopy and its complete transpose. -/
@[reassoc]
theorem transpose_endpoint {X Y : C} (H : T.obj X ⟶ Y) :
    adj.homEquiv X Y H ≫ endpointEvaluation adj e Y = e.app X ≫ H := by
  rw [← endpoint_untranspose, Equiv.symm_apply_apply]

/-- The full right family consists of all actual endpoint evaluation arrows. -/
def endpointFamily : MorphismProperty C :=
  MorphismProperty.ofHoms (endpointEvaluation adj e)

/-- Every native target supplies its own genuine endpoint evaluation member. -/
theorem endpointEvaluation_mem (Y : C) :
    endpointFamily adj e (endpointEvaluation adj e Y) := .mk Y

/-- All-target extension gives a lift against every entire original evaluation arrow. -/
theorem lifting_of_extension {A X : C} (i : A ⟶ X)
    (hi : IntervalHomotopyExtension.property T e i) (Y : C) :
    HasLiftingProperty i (endpointEvaluation adj e Y) := by
  constructor
  intro a f sq
  let H : T.obj A ⟶ Y := (adj.homEquiv A Y).symm a
  have h0 : e.app A ≫ H = i ≫ f :=
    (endpoint_untranspose adj e a).trans sq.w
  obtain ⟨K, hK0, hKi⟩ := hi Y f H h0
  refine CommSq.HasLift.mk' {
    l := adj.homEquiv X Y K
    fac_left := ?_
    fac_right := (transpose_endpoint adj e K).trans hK0 }
  rw [← adj.homEquiv_naturality_left, hKi]
  exact (adj.homEquiv A Y).apply_symm_apply a

/-- Lifting against the original evaluation gives both original HEP equations. -/
theorem extension_of_lifting {A X : C} (i : A ⟶ X)
    (hi : ∀ Y : C, HasLiftingProperty i (endpointEvaluation adj e Y)) :
    IntervalHomotopyExtension.property T e i := by
  intro Y f H h0
  let a : A ⟶ R.obj Y := adj.homEquiv A Y H
  let sq : CommSq a i (endpointEvaluation adj e Y) f :=
    ⟨(transpose_endpoint adj e H).trans h0⟩
  let _ : HasLiftingProperty i (endpointEvaluation adj e Y) := hi Y
  let K : T.obj X ⟶ Y := (adj.homEquiv X Y).symm sq.lift
  refine ⟨K, (endpoint_untranspose adj e sq.lift).trans sq.fac_right, ?_⟩
  change T.map i ≫ (adj.homEquiv X Y).symm sq.lift = H
  rw [← adj.homEquiv_naturality_left_symm, sq.fac_left]
  exact (adj.homEquiv A Y).symm_apply_apply H

/-- The complete extension and endpoint-lifting dictionaries are equivalent. -/
theorem property_iff_lifting {A X : C} (i : A ⟶ X) :
    IntervalHomotopyExtension.property T e i ↔
      ∀ Y : C, HasLiftingProperty i (endpointEvaluation adj e Y) :=
  ⟨fun hi Y => lifting_of_extension adj e i hi Y, extension_of_lifting adj e i⟩

/-- Native HEP is exactly the LLP against the genuine all-target evaluation family. -/
theorem property_eq_llp :
    IntervalHomotopyExtension.property T e = (endpointFamily adj e).llp := by
  ext A X i
  rw [property_iff_lifting]
  constructor
  · intro hi U Y p hp
    cases hp with
    | mk Y => exact hi Y
  · intro hi Y
    exact hi _ (endpointEvaluation_mem adj e Y)

end Internal

section NativeEndpoint

attribute [local instance] MonoidalClosed.enrichedCategorySelf

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]

/-- The actual original free-time scalar and every native enriched Hom action are retained. -/
abbrev NativeCategory := EnrichedFunctorCat PointedCGWH.{u, v} I

/-- Evaluate the actual original scalar cotensor at any original free-time endpoint. -/
def cotensorEndpointEvaluation (t : unitInterval) (Y : NativeCategory (I := I)) :
    cotensorObject RealizedIntervalContraction.time Y ⟶ Y :=
  Internal.endpointEvaluation
    (ScalarLeibniz.adjunction RealizedIntervalContraction.time)
    (EnrichedIntervalContraction.timeInclusionNatTrans t) Y

/-- Both original maps in the actual endpoint evaluation are kept as whole native arrows. -/
theorem cotensorEndpointEvaluation_eq (t : unitInterval) (Y : NativeCategory (I := I)) :
    cotensorEndpointEvaluation t Y =
      EnrichedIntervalContraction.timeInclusion t
          (cotensorObject RealizedIntervalContraction.time Y) ≫
        (ScalarLeibniz.adjunction RealizedIntervalContraction.time).counit.app Y := rfl

/-- Every full original target map commutes with the entire genuine endpoint evaluation. -/
@[reassoc]
theorem cotensorEndpointEvaluation_naturality (t : unitInterval)
    {Y Z : NativeCategory (I := I)} (g : Y ⟶ Z) :
    cotensorMap RealizedIntervalContraction.time g ≫ cotensorEndpointEvaluation t Z =
      cotensorEndpointEvaluation t Y ≫ g :=
  Internal.endpointEvaluation_naturality
    (ScalarLeibniz.adjunction RealizedIntervalContraction.time)
    (EnrichedIntervalContraction.timeInclusionNatTrans t) g

/-- The complete original scalar cotensor evaluation is a genuine natural transformation. -/
def cotensorEndpointEvaluationNatTrans (t : unitInterval) :
    cotensor RealizedIntervalContraction.time ⟶ 𝟭 (NativeCategory (I := I)) :=
  Internal.endpointEvaluationNatTrans
    (ScalarLeibniz.adjunction RealizedIntervalContraction.time)
    (EnrichedIntervalContraction.timeInclusionNatTrans t)

/-- The full actual native target family uses the original time-zero convention. -/
def cotensorEndpointFamily : MorphismProperty (NativeCategory (I := I)) :=
  MorphismProperty.ofHoms (cotensorEndpointEvaluation 0)

/-- Every arbitrary original native target supplies its actual scalar-cotensor evaluation. -/
theorem cotensorEndpointEvaluation_mem (Y : NativeCategory (I := I)) :
    cotensorEndpointFamily (cotensorEndpointEvaluation 0 Y) := .mk Y

/-- The original based all-target HEP is the entire actual scalar-cotensor left lifting class. -/
theorem nativeHEP_eq_llp :
    EnrichedBasedHomotopyExtension.property (I := I) = cotensorEndpointFamily.llp :=
  Internal.property_eq_llp
    (ScalarLeibniz.adjunction RealizedIntervalContraction.time)
    (EnrichedIntervalContraction.timeInclusionNatTrans 0)

/-- All arbitrary native targets, maps and homotopies are retained by the lifting dictionary. -/
theorem nativeHEP_iff_lifting {A X : NativeCategory (I := I)} (i : A ⟶ X) :
    EnrichedBasedHomotopyExtension.property i ↔
      ∀ Y : NativeCategory (I := I),
        HasLiftingProperty i (cotensorEndpointEvaluation 0 Y) :=
  Internal.property_iff_lifting
    (ScalarLeibniz.adjunction RealizedIntervalContraction.time)
    (EnrichedIntervalContraction.timeInclusionNatTrans 0) i

/-- The original based extension class is stable under full Arrow retracts. -/
instance nativeHEP_retracts :
    (EnrichedBasedHomotopyExtension.property (I := I)).IsStableUnderRetracts := by
  rw [nativeHEP_eq_llp]
  infer_instance

/-- Every original coproduct shape, in an independent universe, preserves native HEP. -/
instance nativeHEP_coproducts :
    IsStableUnderCoproducts.{w} (EnrichedBasedHomotopyExtension.property (I := I)) := by
  rw [nativeHEP_eq_llp]
  infer_instance

/-- Actual well-order-continuous diagrams of any original shape preserve native HEP. -/
instance nativeHEP_transfinite :
    IsStableUnderTransfiniteComposition.{w}
      (EnrichedBasedHomotopyExtension.property (I := I)) := by
  rw [nativeHEP_eq_llp]
  infer_instance

/-- All original full coproduct arrows lie in the same literal native extension class. -/
theorem nativeHEP_coproducts_le :
    coproducts.{w} (EnrichedBasedHomotopyExtension.property (I := I)) ≤
      EnrichedBasedHomotopyExtension.property :=
  MorphismProperty.coproducts_le _

/-- The actual original pushout class lies in the same literal native extension class. -/
theorem nativeHEP_pushouts_le :
    (EnrichedBasedHomotopyExtension.property (I := I)).pushouts ≤
      EnrichedBasedHomotopyExtension.property :=
  MorphismProperty.pushouts_le

/-- Each complete original ordinal-cell witness gives literal all-target native HEP. -/
theorem nativeHEP_transfinite_mem
    (J : Type w) [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
    {A X : NativeCategory (I := I)} (i : A ⟶ X)
    (d : EnrichedBasedHomotopyExtension.property.TransfiniteCompositionOfShape J i) :
    EnrichedBasedHomotopyExtension.property i :=
  MorphismProperty.transfiniteCompositionsOfShape_le _ J _ d.mem

/-- The original colimit cocone itself, with all of its native legs, gives the endpoint arrow. -/
theorem nativeHEP_colimit_endpoint_mem
    (J : Type w) [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
    (F : J ⥤ NativeCategory (I := I)) [F.IsWellOrderContinuous]
    (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ j : J, ¬IsMax j →
      EnrichedBasedHomotopyExtension.property (F.map (homOfLE (Order.le_succ j)))) :
    EnrichedBasedHomotopyExtension.property (c.ι.app ⊥) := by
  let d : EnrichedBasedHomotopyExtension.property.TransfiniteCompositionOfShape J
      (c.ι.app ⊥) := {
    F := F
    isoBot := Iso.refl (F.obj ⊥)
    incl := c.ι
    isColimit := hc
    fac := Category.id_comp _
    map_mem := hF }
  exact nativeHEP_transfinite_mem J _ d

/-- Every map/homotopy pair at the original ordinal colimit has both full extension equations. -/
theorem nativeHEP_colimit_endpoint_extension
    (J : Type w) [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
    (F : J ⥤ NativeCategory (I := I)) [F.IsWellOrderContinuous]
    (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ j : J, ¬IsMax j →
      EnrichedBasedHomotopyExtension.property (F.map (homOfLE (Order.le_succ j))))
    (Y : NativeCategory (I := I)) (f : c.pt ⟶ Y)
    (H : EnrichedIntervalContraction.timeObject (F.obj ⊥) ⟶ Y)
    (h0 : EnrichedIntervalContraction.timeInclusion 0 (F.obj ⊥) ≫ H = c.ι.app ⊥ ≫ f) :
    ∃ K : EnrichedIntervalContraction.timeObject c.pt ⟶ Y,
      EnrichedIntervalContraction.timeInclusion 0 c.pt ≫ K = f ∧
        tensorLeftMap RealizedIntervalContraction.time (c.ι.app ⊥) ≫ K = H :=
  nativeHEP_colimit_endpoint_mem J F c hc hF Y f H h0

/-- Retraction uses the actual complete original Arrow retraction, on arbitrary endpoints. -/
theorem nativeHEP_retract_mem {A X A' X' : NativeCategory (I := I)}
    {i : A ⟶ X} {i' : A' ⟶ X'} (r : RetractArrow i' i)
    (hi : EnrichedBasedHomotopyExtension.property i) :
    EnrichedBasedHomotopyExtension.property i' :=
  MorphismProperty.of_retract r hi

end NativeEndpoint

section OriginalFree

attribute [local instance] MonoidalClosed.enrichedCategorySelf

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]

/-- The original scalar/free comparison gives the whole free-time comparison on coefficients. -/
def freeTimeComparison (a : I) :
    BasedTimeHomotopyExtension.timeFunctor ⋙ Free.functor a ≅
      Free.functor a ⋙ EnrichedIntervalContraction.timeFunctor :=
  (Free.scalarFreeNatIso RealizedIntervalContraction.time a).symm

/-- Both original free-time endpoints are retained by the complete free/evaluation comparison. -/
theorem freeTimeComparison_endpoint (a : I) (t : unitInterval) (X : PointedCGWH.{u, v}) :
    (Free.functor a).map ((BasedTimeHomotopyExtension.inclusionNatTrans t).app X) ≫
        ((freeTimeComparison a).app X).hom =
      (EnrichedIntervalContraction.timeInclusionNatTrans t).app ((Free.functor a).obj X) := by
  change Free.coefficientMap a ((λ_ X).inv ≫ freePointIntervalEndpoint t ▷ X) ≫
      (Free.scalarFreeIso RealizedIntervalContraction.time X a).inv =
    EnrichedIntervalContraction.timeInclusion t (Free.object a X)
  apply EnrichedFunctorCat.hom_ext
  intro b
  rw [component_comp, Free.coefficientMap_component, Free.scalarFreeIso_inv_component,
    EnrichedIntervalContraction.timeInclusion_component, comp_whiskerRight]
  monoidal

/-- Pointed based HEP transports through the actual original free/evaluation adjunction. -/
theorem freeMap_mem (a : I) {A X : PointedCGWH.{u, v}} (i : A ⟶ X)
    (hi : BasedTimeHomotopyExtension.property i) :
    EnrichedBasedHomotopyExtension.property ((Free.functor a).map i) :=
  IntervalHomotopyExtension.map_mem_of_adjunction (Free.adjunction a)
    BasedTimeHomotopyExtension.timeFunctor (BasedTimeHomotopyExtension.inclusionNatTrans 0)
    EnrichedIntervalContraction.timeFunctor (EnrichedIntervalContraction.timeInclusionNatTrans 0)
    (freeTimeComparison a) (freeTimeComparison_endpoint a 0) i hi

/-- The complete original pointed boundary family is cofibrant by its original I-right equation. -/
theorem boundaryMap_modelCofibration {A X : PointedCGWH.{u, v}} (i : A ⟶ X)
    (hi : realizedBoundaryInclusions i) : cofibrations PointedCGWH.{u, v} i := by
  have hRight : realizedBoundaryInclusions.{u, v}.rlp =
      trivialFibrations PointedCGWH.{u, v} := cofibrantGenerationData.{u, v}.I_rlp
  have h := realizedBoundaryInclusions.{u, v}.le_llp_rlp i hi
  rwa [hRight, trivialFibrations_llp] at h

/-- Every actual original boundary free map has native all-target based HEP. -/
theorem freeBoundaryMap_mem (a : I) {A X : PointedCGWH.{u, v}} (i : A ⟶ X)
    (hi : realizedBoundaryInclusions i) :
    EnrichedBasedHomotopyExtension.property ((Free.functor a).map i) :=
  freeMap_mem a i
    (BasedTimeHomotopyExtension.modelCofibration_mem i (boundaryMap_modelCofibration i hi))

/-- Membership in the full original free-I family retains the original source Arrow witness. -/
theorem originalFreeI_le_nativeHEP :
    HomotopicalAlgebra.EnrichedProjective.generators (A := I) realizedBoundaryInclusions ≤
      EnrichedBasedHomotopyExtension.property := by
  intro A X i hi
  let L : I → PointedCGWH.{u, v} ⥤ NativeCategory (I := I) := fun a => Free.functor a
  obtain ⟨q, hq⟩ := (MorphismProperty.adjointFamilyGenerators_iff L
    realizedBoundaryInclusions i).mp hi
  have hActual := freeBoundaryMap_mem q.1 q.2.1.hom q.2.2
  exact (EnrichedBasedHomotopyExtension.property.arrow_mk_iso_iff (eqToIso hq)).mpr hActual

end OriginalFree

end PointedCGWH.Spectra.Orthogonal.OriginalIClosedHomotopyExtension
