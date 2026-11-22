/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.BergnerTwoLabelOriginalIntervalLift
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalBergnerIntervalGenerators

/-!
# Both original interval point maps lift against genuine F1/F2 maps

The SAME full weak-unit interval has an actual original equivalence
coefficient between its two labels. Exact F2 lifts its unchanged original
image coefficient and chooses the actual original other object. The full
unit readback retains the original two-label fibration frame. Its proved
original interval lift recovers both complete square triangles, for both
point labels and including coincident original target objects.
-/

noncomputable section
universe u
open CategoryTheory HomotopicalAlgebra MonoidalCategory Opposite
open scoped Simplicial SSet.modelCategoryQuillen

namespace CategoryTheory.SimplicialEnrichment.OriginalBergnerIntervalConverse
open FixedObjects OriginalWalkingArrowFreeSingleHomIso ComponentCategory EnrichedHomWeakTransport
open EnrichedHomActionNaturality EnrichedHomPrecomposition
attribute [local instance] FixedObjectModel.modelCategory

/-- Every original full Hom unit map in a genuine weak-unit fixed-label interval remains genuinely weak at actual
original vertices. -/
theorem original_hom_weak (H : FixedObjects walking.{u})
    (hH : FixedObjectModel.weakEquivalences walking (CodiscreteTerminal.toTerminal H)) (x y : H.val) :
    SSet.realizationWeakEquivalences (CodiscreteEnrichment.toUnit (x ⟶[SSet.{u}] y)) := by
  have h := (FixedObjectModel.weakEquivalences_iff _).mp hH (label H x) (label H y)
  have hw := (congrArg (fun k : hom H (label H x) (label H y) ⟶ 𝟙_ SSet.{u} =>
    SSet.realizationWeakEquivalences k) (CodiscreteTerminal.toTerminal_homMap H _ _)).mp h
  exact (CodiscreteEnrichment.toUnit_weak_iff (originalHomIso H x y).hom
    (SSet.realizationWeakEquivalences.of_isIso _)).mpr hw

/-- Genuine original F1/F2 lifts the SAME actual original (BergnerTwoObject.source (𝟙_ SSet.{u})) point map into the
full fixed-cofibrant weak interval. -/
theorem source_point_lifting {E D : Carrier.{u}} (r : E ⟶ D) (hr : Bergner.localFibrations r)
    (H : FixedObjects walking.{u}) [IsCofibrant H]
    (hH : FixedObjectModel.weakEquivalences walking (CodiscreteTerminal.toTerminal H)) :
    HasLiftingProperty (OriginalBergnerIntervalFamily.pointMap H (BergnerTwoObject.source (𝟙_ SSet.{u}))) r := by
  refine ⟨fun {top bottom} sq => ?_⟩
  let x0 := top.obj PUnit.unit
  let sx := vertex H (BergnerTwoObject.source (𝟙_ SSet.{u}))
  let ty := vertex H (BergnerTwoObject.target (𝟙_ SSet.{u}))
  have h0 : r.obj x0 = bottom.obj sx := congrArg (fun f => f.obj PUnit.unit) sq.w
  let eH := OriginalWeakUnitHomsPointRecognition.componentIso H.val (original_hom_weak H hH) sx ty
  let qH := forwardUnit eH
  have hqH : IsIso (arrowOf H.val (SSet.unitHomEquiv _ qH)) :=
    (congrArg IsIso (forwardUnit_class eH)).mpr eH.isIso_hom
  let Q := qH ≫ bottom.map sx ty
  have hQ : IsIso (arrowOf D (SSet.unitHomEquiv _ Q)) := by
    let _ : IsIso (arrowOf H.val (SSet.unitHomEquiv _ qH)) := hqH
    exact (congrArg IsIso (component_map_unit bottom qH)).mp inferInstance
  let Q' := Q ≫ eqToHom (congrArg₂ (fun a b : D => a ⟶[SSet.{u}] b) h0.symm rfl)
  have hQ' : IsIso (arrowOf D (SSet.unitHomEquiv _ Q')) := unit_endpoint_isIso h0.symm rfl Q hQ
  have hF2 := (Bergner.componentIsofibration_iff_equivalenceVertexLifting r hr.1).mp hr.2
  obtain ⟨Y, hY, e, he, hread⟩ := hF2 x0 (bottom.obj ty) (SSet.unitHomEquiv _ Q') hQ'
  let a : walking.{u} → E := fun z => match z.down with
    | .source => x0
    | .target => Y
  have hObj : ∀ z, r.obj (a z) = bottom.obj (vertex H z) := by
    rintro ⟨z⟩
    cases z
    · exact h0
    · exact hY
  let qA : 𝟙_ SSet.{u} ⟶ (a (BergnerTwoObject.source (𝟙_ SSet.{u})) ⟶[SSet.{u}] a (BergnerTwoObject.target (𝟙_
    SSet.{u}))) := (SSet.unitHomEquiv _).symm e
  have hqA : IsIso (arrowOf E (SSet.unitHomEquiv _ qA)) :=
    (congrArg (fun v => IsIso (arrowOf E v)) ((SSet.unitHomEquiv _).apply_symm_apply e)).mpr he
  have hread' : (r.map x0 Y ≫ eqToHom
      (congrArg₂ (fun a b : D => a ⟶[SSet.{u}] b) rfl hY)).app (op ⦋0⦌)
        (SSet.unitHomEquiv _ qA) = SSet.unitHomEquiv _ Q' :=
    (congrArg (fun v => (r.map x0 Y ≫ eqToHom
      (congrArg₂ (fun a b : D => a ⟶[SSet.{u}] b) rfl hY)).app (op ⦋0⦌) v)
        ((SSet.unitHomEquiv _).apply_symm_apply e)).trans hread
  have hfull := OriginalF2CoefficientEquation.full_unit_image r x0 Y (bottom.obj sx) (bottom.obj ty)
    h0 hY qA Q hread'
  obtain ⟨L, hL, hObjects⟩ := BergnerTwoLabelFibrationSquare.exists_original_lift r hr.1 H hH bottom a
    hObj (BergnerTwoObject.source (𝟙_ SSet.{u})) (BergnerTwoObject.target (𝟙_ SSet.{u})) (Or.inl ⟨rfl, rfl⟩) qA qH hfull
      hqA hqH
  refine CommSq.HasLift.mk' ⟨L, ?_, hL⟩
  exact (BergnerObjects.select_comp sx L).trans
    ((congrArg BergnerObjects.select (hObjects (BergnerTwoObject.source (𝟙_ SSet.{u})))).trans
      (BergnerObjects.select_readback top))


/-- Genuine original F1/F2 lifts the SAME actual original (BergnerTwoObject.target (𝟙_ SSet.{u})) point map into the
full fixed-cofibrant weak interval. -/
theorem target_point_lifting {E D : Carrier.{u}} (r : E ⟶ D) (hr : Bergner.localFibrations r)
    (H : FixedObjects walking.{u}) [IsCofibrant H]
    (hH : FixedObjectModel.weakEquivalences walking (CodiscreteTerminal.toTerminal H)) :
    HasLiftingProperty (OriginalBergnerIntervalFamily.pointMap H (BergnerTwoObject.target (𝟙_ SSet.{u}))) r := by
  refine ⟨fun {top bottom} sq => ?_⟩
  let x0 := top.obj PUnit.unit
  let sx := vertex H (BergnerTwoObject.target (𝟙_ SSet.{u}))
  let ty := vertex H (BergnerTwoObject.source (𝟙_ SSet.{u}))
  have h0 : r.obj x0 = bottom.obj sx := congrArg (fun f => f.obj PUnit.unit) sq.w
  let eH := OriginalWeakUnitHomsPointRecognition.componentIso H.val (original_hom_weak H hH) sx ty
  let qH := forwardUnit eH
  have hqH : IsIso (arrowOf H.val (SSet.unitHomEquiv _ qH)) :=
    (congrArg IsIso (forwardUnit_class eH)).mpr eH.isIso_hom
  let Q := qH ≫ bottom.map sx ty
  have hQ : IsIso (arrowOf D (SSet.unitHomEquiv _ Q)) := by
    let _ : IsIso (arrowOf H.val (SSet.unitHomEquiv _ qH)) := hqH
    exact (congrArg IsIso (component_map_unit bottom qH)).mp inferInstance
  let Q' := Q ≫ eqToHom (congrArg₂ (fun a b : D => a ⟶[SSet.{u}] b) h0.symm rfl)
  have hQ' : IsIso (arrowOf D (SSet.unitHomEquiv _ Q')) := unit_endpoint_isIso h0.symm rfl Q hQ
  have hF2 := (Bergner.componentIsofibration_iff_equivalenceVertexLifting r hr.1).mp hr.2
  obtain ⟨Y, hY, e, he, hread⟩ := hF2 x0 (bottom.obj ty) (SSet.unitHomEquiv _ Q') hQ'
  let a : walking.{u} → E := fun z => match z.down with
    | .source => Y
    | .target => x0
  have hObj : ∀ z, r.obj (a z) = bottom.obj (vertex H z) := by
    rintro ⟨z⟩
    cases z
    · exact hY
    · exact h0
  let qA : 𝟙_ SSet.{u} ⟶ (a (BergnerTwoObject.target (𝟙_ SSet.{u})) ⟶[SSet.{u}] a (BergnerTwoObject.source (𝟙_
    SSet.{u}))) := (SSet.unitHomEquiv _).symm e
  have hqA : IsIso (arrowOf E (SSet.unitHomEquiv _ qA)) :=
    (congrArg (fun v => IsIso (arrowOf E v)) ((SSet.unitHomEquiv _).apply_symm_apply e)).mpr he
  have hread' : (r.map x0 Y ≫ eqToHom
      (congrArg₂ (fun a b : D => a ⟶[SSet.{u}] b) rfl hY)).app (op ⦋0⦌)
        (SSet.unitHomEquiv _ qA) = SSet.unitHomEquiv _ Q' :=
    (congrArg (fun v => (r.map x0 Y ≫ eqToHom
      (congrArg₂ (fun a b : D => a ⟶[SSet.{u}] b) rfl hY)).app (op ⦋0⦌) v)
        ((SSet.unitHomEquiv _).apply_symm_apply e)).trans hread
  have hfull := OriginalF2CoefficientEquation.full_unit_image r x0 Y (bottom.obj sx) (bottom.obj ty)
    h0 hY qA Q hread'
  obtain ⟨L, hL, hObjects⟩ := BergnerTwoLabelFibrationSquare.exists_original_lift r hr.1 H hH bottom a
    hObj (BergnerTwoObject.target (𝟙_ SSet.{u})) (BergnerTwoObject.source (𝟙_ SSet.{u})) (Or.inr ⟨rfl, rfl⟩) qA qH hfull
      hqA hqH
  refine CommSq.HasLift.mk' ⟨L, ?_, hL⟩
  exact (BergnerObjects.select_comp sx L).trans
    ((congrArg BergnerObjects.select (hObjects (BergnerTwoObject.target (𝟙_ SSet.{u})))).trans
      (BergnerObjects.select_readback top))


end CategoryTheory.SimplicialEnrichment.OriginalBergnerIntervalConverse
