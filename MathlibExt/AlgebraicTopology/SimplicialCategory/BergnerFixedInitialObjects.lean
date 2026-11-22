/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.BergnerFreePointCofibrations
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectSmallColimits

/-!
# The original fixed-label initial enrichment is genuinely free on its objects

Its actual fixed-label initial universal property and complete original
readback identify every entire global enriched map with its original
individual object function. Both full inverse maps compare it with the
existing actual coproduct of original point enrichments. Original point
inclusions are consequently genuine global C0 cofibrations.
-/

noncomputable section
universe u
open CategoryTheory Limits

namespace CategoryTheory.SimplicialEnrichment.BergnerFixedInitialObjects
open FixedObjects

/-- The actual initial object of the SAME original fixed-label enriched category. -/
abbrev fixedObject (O : Type u) : FixedObjects O := ⊥_ (FixedObjects O)

/-- Its whole underlying original changing-object enrichment. -/
abbrev object (O : Type u) : Carrier.{u} := (fixedObject O).val

/-- The individual original vertex with its supplied fixed label. -/
def vertex (O : Type u) (x : O) : object O := FixedObjects.vertex (fixedObject O) x

/-- The actual fixed-label initial map into the full original target reindexed at its original object function. -/
def fixedDesc (O : Type u) {C : Carrier.{u}} (a : O → C) :
    fixedObject O ⟶ CarrierReindexing.object C a := initial.to _

/-- Extend the same original object function to the entire original enriched map. -/
def desc (O : Type u) {C : Carrier.{u}} (a : O → C) : object O ⟶ C :=
  (fixedDesc O a).val ≫ CarrierReindexing.toTarget C a

/-- Every individual original source label has the EXACT prescribed original target object. -/
theorem desc_vertex (O : Type u) {C : Carrier.{u}} (a : O → C) (x : O) :
    (desc O a).obj (vertex O x) = a x :=
  congrArg a (map_vertex (fixedDesc O a) x)

/-- Readback of the SAME original object function recovers the ENTIRE original global enriched map. -/
theorem desc_readback (O : Type u) {C : Carrier.{u}} (F : object O ⟶ C) :
    desc O (fun x => F.obj (vertex O x)) = F := by
  let a : O → C := fun x => F.obj (vertex O x)
  let G := CarrierLabelReadback.map (fixedObject O) a F (fun _ => rfl)
  have h : fixedDesc O a = G := initialIsInitial.hom_ext _ _
  exact (congrArg (fun H : fixedObject O ⟶ CarrierReindexing.object C a =>
    H.val ≫ CarrierReindexing.toTarget C a) h).trans
      (CarrierLabelReadback.map_fac (fixedObject O) a F (fun _ => rfl))

/-- Genuine full maps out of the original initial enrichment are exactly its SAME individual object functions. -/
def homEquiv (O : Type u) (C : Carrier.{u}) : (object O ⟶ C) ≃ (O → C) where
  toFun F x := F.obj (vertex O x)
  invFun := desc O
  left_inv := desc_readback O
  right_inv a := funext (desc_vertex O a)

/-- The full original comparison from the actual point coproduct. -/
def fromFree (O : Type u) : BergnerFreeObjects.object O ⟶ object O :=
  BergnerFreeObjects.desc O (vertex O)

/-- The full original comparison to the actual point coproduct. -/
def toFree (O : Type u) : object O ⟶ BergnerFreeObjects.object O :=
  desc O (BergnerFreeObjects.vertex O)

/-- Both entire original comparison maps compose to the SAME point-coproduct identity. -/
theorem fromFree_toFree (O : Type u) : fromFree O ≫ toFree O = 𝟙 (BergnerFreeObjects.object O) := by
  apply (BergnerFreeObjects.homEquiv O (BergnerFreeObjects.object O)).injective
  funext x
  change (toFree O).obj ((fromFree O).obj (BergnerFreeObjects.vertex O x)) = BergnerFreeObjects.vertex O x
  exact (congrArg (toFree O).obj (BergnerFreeObjects.desc_vertex O (vertex O) x)).trans
    (desc_vertex O (BergnerFreeObjects.vertex O) x)

/-- Both entire original comparison maps compose to the SAME fixed-label initial identity. -/
theorem toFree_fromFree (O : Type u) : toFree O ≫ fromFree O = 𝟙 (object O) := by
  apply (homEquiv O (object O)).injective
  funext x
  change (fromFree O).obj ((toFree O).obj (vertex O x)) = vertex O x
  exact (congrArg (fromFree O).obj (desc_vertex O (BergnerFreeObjects.vertex O) x)).trans
    (BergnerFreeObjects.desc_vertex O (vertex O) x)

/-- An actual entire original enriched isomorphism, with both full original object/Hom maps and inverse equations
retained. -/
def freeObjectsIso (O : Type u) : object O ≅ BergnerFreeObjects.object O where
  hom := toFree O
  inv := fromFree O
  hom_inv_id := toFree_fromFree O
  inv_hom_id := fromFree_toFree O

/-- Every original point selection into the fixed-label initial enrichment is genuinely globally C0 cofibrant. -/
theorem point_cofibration (O : Type u) (x : O) : Bergner.cofibrations (BergnerObjects.select (vertex O x)) := by
  let _ : IsIso (fromFree O) := (freeObjectsIso O).isIso_inv
  have h : Bergner.cofibrations (BergnerFreeObjects.injection O x ≫ fromFree O) :=
    Bergner.cofibrations.comp_mem _ _ (BergnerFreeObjects.injection_cofibration O x)
      (MorphismProperty.of_isIso Bergner.cofibrations (fromFree O))
  exact (congrArg (fun F : BergnerObjects.point.{u} ⟶ object O => Bergner.cofibrations F)
    (BergnerFreeObjects.injection_desc O (vertex O) x)).mp h

end CategoryTheory.SimplicialEnrichment.BergnerFixedInitialObjects
