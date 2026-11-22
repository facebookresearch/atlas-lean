/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalF2CoefficientEquation
import MathlibExt.AlgebraicTopology.SimplicialCategory.ComponentCategoryReindexing

/-!
# The actual original two-label reindexed Hom-fibration square

The existing reindexing and whole carrier readback construct the full
original right map on the unchanged two labels. Every original Hom map
is the supplied original right Hom map followed only by its proved
endpoint equations. Its genuine full Hom fibrations and original
component equivalences are retained through the actual projections.
-/

noncomputable section
universe u
open CategoryTheory HomotopicalAlgebra MonoidalCategory
open scoped Simplicial SSet.modelCategoryQuillen

namespace CategoryTheory.SimplicialEnrichment.BergnerTwoLabelFibrationSquare
open FixedObjects OriginalWalkingArrowFreeSingleHomIso ComponentCategory
variable {E D : Carrier.{u}} (r : E ⟶ D) (a : walking.{u} → E) (b : walking.{u} → D)
variable (hObj : ∀ x, r.obj (a x) = b x)

/-- The SAME actual original two-label source keeps the full Homs at its prescribed original image objects. -/
abbrev source : FixedObjects walking.{u} := CarrierReindexing.object E a

/-- The SAME actual original two-label target keeps the full Homs at its prescribed original image objects. -/
abbrev target : FixedObjects walking.{u} := CarrierReindexing.object D b

/-- The actual full original right map is the existing original whole labelled carrier readback. -/
def right : source a ⟶ target b :=
  CarrierLabelReadback.map (source a) b (CarrierReindexing.toTarget E a ≫ r) hObj

/-- Every original full reindexed right Hom is exactly the supplied original right Hom with its actual endpoint
transport. -/
theorem right_hom (x y : walking.{u}) :
    homMap (right r a b hObj) x y = r.map (a x) (a y) ≫
      eqToHom (congrArg₂ (fun s t : D => s ⟶[SSet.{u}] t) (hObj x) (hObj y)) := by
  have hm := CarrierLabelReadback.homMap_map (source a) b
    (CarrierReindexing.toTarget E a ≫ r) hObj x y
  change homMap (right r a b hObj) x y = (𝟙 _ ≫ r.map (a x) (a y)) ≫ eqToHom _ at hm
  exact hm.trans (congrArg (fun k => k ≫ eqToHom
    (congrArg₂ (fun s t : D => s ⟶[SSet.{u}] t) (hObj x) (hObj y))) (Category.id_comp _))

/-- The SAME full original right projection square recovers the unchanged whole supplied right functor. -/
theorem right_projection :
    (right r a b hObj).val ≫ CarrierReindexing.toTarget D b =
      CarrierReindexing.toTarget E a ≫ r :=
  CarrierLabelReadback.map_fac (source a) b (CarrierReindexing.toTarget E a ≫ r) hObj

/-- Every original all-Hom Kan fibration remains an actual full fixed-label Hom fibration on this SAME right map. -/
theorem right_fibration (hr : Bergner.homFibrations r) :
    FixedObjectModel.fibrations walking (right r a b hObj) := by
  apply (FixedObjectModel.fibrations_iff _).mpr
  intro x y
  let _ : Fibration (r.map (a x) (a y)) := hr (a x) (a y)
  have hc : Fibration (r.map (a x) (a y) ≫
      eqToHom (congrArg₂ (fun s t : D => s ⟶[SSet.{u}] t) (hObj x) (hObj y))) := inferInstance
  exact (congrArg (fun k : hom (source a) x y ⟶ hom (target b) x y => Fibration k)
    (right_hom r a b hObj x y)).mpr hc

/-- The actual original full projection is genuinely fully faithful on components of the SAME reindexed Homs. -/
def projectionFullyFaithful :
    (mapFunctor (CarrierReindexing.toTarget E a)).FullyFaithful :=
  ComponentCategory.reindexProjectionFullyFaithful a

/-- The unchanged original coefficient equivalence is retained on the SAME full two-label reindexed Hom. -/
theorem unit_isIso (x y : walking.{u}) (q : 𝟙_ SSet.{u} ⟶ (a x ⟶[SSet.{u}] a y))
    (hq : IsIso (arrowOf E (SSet.unitHomEquiv _ q))) :
    IsIso (arrowOf (source a).val (SSet.unitHomEquiv _ q)) := by
  let P := CarrierReindexing.toTarget E a
  let _ : (mapFunctor P).ReflectsIsomorphisms := (projectionFullyFaithful a).reflectsIsomorphisms
  have hm : (mapFunctor P).map (arrowOf (source a).val (SSet.unitHomEquiv _ q)) =
      arrowOf E (SSet.unitHomEquiv _ q) :=
    (EnrichedHomActionNaturality.component_map_unit P q).trans
      (congrArg (fun k => arrowOf E (SSet.unitHomEquiv _ k)) (Category.comp_id q))
  let _ : IsIso ((mapFunctor P).map (arrowOf (source a).val (SSet.unitHomEquiv _ q))) :=
    (congrArg IsIso hm).mpr hq
  exact isIso_of_reflects_iso _ (mapFunctor P)

end CategoryTheory.SimplicialEnrichment.BergnerTwoLabelFibrationSquare
