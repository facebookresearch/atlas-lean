/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalBergnerIntervalPointLifting
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalUnitCoefficientSourceTransport
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectComponentUnitMaps

/-!
# Genuine small A2 right lifting recovers the SAME supplied equivalence vertex

The actual full original interval constructed for the supplied equivalence
has its exact forward coefficient and original endpoint images. Its SAME
point lifts against the actual small A2 right class. The full lift square
then recovers the exact supplied coefficient, and the genuine component
unit projection proves its lifted original vertex invertible. No desired
vertex lift, global model or weak outcome is supplied as an input.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.SimplicialEnrichment.OriginalBergnerIntervalFamily
open FixedObjects OriginalWalkingArrowFreeSingleHomIso
variable {E D : Carrier.{u}} (r : E ⟶ D)

/-- Actual original small-A2 right lifts recover every SAME supplied original equivalence vertex with its exact original
target object. -/
theorem right_equivalenceVertexLifting (hr : generatingIntervals.rlp r) :
    Bergner.equivalenceVertexLifting r := by
  intro x d e he
  let a : walking.{u} → D := fun z => match z.down with
    | .source => r.obj x
    | .target => d
  let H := OriginalEquivalenceCountableInterval.fixedObject a e he
  let b := OriginalEquivalenceCountableInterval.toOriginal a e he
  let sx := vertex H (BergnerTwoObject.source (𝟙_ SSet.{u}))
  let ty := vertex H (BergnerTwoObject.target (𝟙_ SSet.{u}))
  have hs : b.obj sx = r.obj x := OriginalEquivalenceCountableInterval.toOriginal_obj a e he _
  have ht : b.obj ty = d := OriginalEquivalenceCountableInterval.toOriginal_obj a e he _
  have sq : CommSq (BergnerObjects.select x) (pointMap H (BergnerTwoObject.source (𝟙_ SSet.{u}))) r b :=
    ⟨(BergnerObjects.select_comp x r).trans
      ((congrArg BergnerObjects.select hs).symm.trans (BergnerObjects.select_comp sx b).symm)⟩
  let hp := original_interval_point_lifting r a e he hr (BergnerTwoObject.source (𝟙_ SSet.{u}))
  let _ : sq.HasLift := hp.sq_hasLift sq
  let L := sq.lift
  have hsource : L.obj sx = x := congrArg (fun F => F.obj PUnit.unit) sq.fac_left
  have htarget : r.obj (L.obj ty) = d :=
    (congrArg (fun F => F.obj ty) sq.fac_right).trans ht
  let q : 𝟙_ SSet.{u} ⟶ (sx ⟶[SSet.{u}] ty) :=
    FreeSingleHom.generator (BergnerTwoObject.source (𝟙_ SSet.{u}))
      (BergnerTwoObject.target (𝟙_ SSet.{u})) (𝟙_ SSet.{u}) ≫
      homMap (OriginalEquivalenceCountableInterval.fromFree a e he)
        (BergnerTwoObject.source (𝟙_ SSet.{u})) (BergnerTwoObject.target (𝟙_ SSet.{u}))
  have hq : IsIso (ComponentCategory.arrowOf H.val (SSet.unitHomEquiv _ q)) :=
    OriginalUnitCoefficientReadback.component_isIso H.val
      (OriginalEquivalenceCountableInterval.originalHom_toUnit_weak a e he) q
  have hL : IsIso (ComponentCategory.arrowOf E (SSet.unitHomEquiv _ (q ≫ L.map sx ty))) := by
    let _ : IsIso (ComponentCategory.arrowOf H.val (SSet.unitHomEquiv _ q)) := hq
    exact inferInstanceAs (IsIso ((ComponentCategory.mapFunctor L).map
      (ComponentCategory.arrowOf H.val (SSet.unitHomEquiv _ q))))
  have hread := (OriginalUnitCoefficientReadback.square_unit L r b sq.fac_right sx ty q
    (r.obj x) d hs ht).trans (OriginalEquivalenceCountableInterval.direct_generator_original a e he)
  let qL : 𝟙_ SSet.{u} ⟶ (L.obj sx ⟶[SSet.{u}] L.obj ty) := q ≫ L.map sx ty
  let qx : 𝟙_ SSet.{u} ⟶ (x ⟶[SSet.{u}] L.obj ty) :=
    qL ≫ eqToHom (congrArg₂ (fun s t : E => s ⟶[SSet.{u}] t) hsource rfl)
  have hxIso : IsIso (ComponentCategory.arrowOf E (SSet.unitHomEquiv _ qx)) :=
    EnrichedHomPrecomposition.unit_endpoint_isIso hsource rfl qL hL
  refine ⟨L.obj ty, htarget, SSet.unitHomEquiv _ qx, hxIso, ?_⟩
  have himage : qx ≫ (r.map x (L.obj ty) ≫
      eqToHom (congrArg₂ (fun s t : D => s ⟶[SSet.{u}] t) rfl htarget)) =
      (SSet.unitHomEquiv _).symm e :=
    (OriginalUnitCoefficientReadback.source_transport_image r hsource d htarget qL).trans hread
  exact (congrArg (SSet.unitHomEquiv _) himage).trans ((SSet.unitHomEquiv _).apply_symm_apply e)

end CategoryTheory.SimplicialEnrichment.OriginalBergnerIntervalFamily
