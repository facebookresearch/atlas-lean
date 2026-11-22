/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectLabelCarrierUnit
import MathlibExt.AlgebraicTopology.SimplicialCategory.CarrierLabelLift
import MathlibExt.AlgebraicTopology.SimplicialCategory.BergnerFixedInitialObjects
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# The SAME original label-pushforward is a genuine global carrier pushout

The actual initial source enrichment and initial target-label enrichment
retain every original object. The complete original carrier unit has
the genuine varying-object pushout universal property for every label
map, including colliding and empty families. All original coefficients
and both full source maps are retained.
-/

noncomputable section
universe u
open CategoryTheory Limits

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.LabelPushforward.GlobalPushout

variable {A O : Type u} (a : A → O) (C : FixedObjects A)

/-- The SAME actual original initial source map. -/
def sourceMap : BergnerFixedInitialObjects.object A ⟶ C.val := (initial.to C).val

/-- The complete original free-label map with its SAME individual prescribed images. -/
def labelsMap : BergnerFixedInitialObjects.object A ⟶ BergnerFixedInitialObjects.object O :=
  BergnerFixedInitialObjects.desc A (fun s => BergnerFixedInitialObjects.vertex O (a s))

/-- The SAME actual original target-label initial map. -/
def targetMap : BergnerFixedInitialObjects.object O ⟶ (object a C).val := (initial.to (object a C)).val

/-- The SAME complete original initial-label square commutes on every original object and full map. -/
theorem condition : sourceMap C ≫ carrierUnit a C = labelsMap a ≫ targetMap a C := by
  apply (BergnerFixedInitialObjects.homEquiv A (object a C).val).injective
  funext s
  change (carrierUnit a C).obj ((initial.to C).val.obj (vertex (BergnerFixedInitialObjects.fixedObject A) s)) =
    (targetMap a C).obj ((labelsMap a).obj (BergnerFixedInitialObjects.vertex A s))
  exact (congrArg (carrierUnit a C).obj (map_vertex (initial.to C) s)).trans
    ((carrierUnit_vertex a C s).trans
      ((map_vertex (initial.to (object a C)) (a s)).symm.trans
        (congrArg (targetMap a C).obj
          (BergnerFixedInitialObjects.desc_vertex A
            (fun s => BergnerFixedInitialObjects.vertex O (a s)) s).symm)))

/-- The actual whole original carrier pushout cocone. -/
def cocone : PushoutCocone (sourceMap C) (labelsMap a) :=
  PushoutCocone.mk (carrierUnit a C) (targetMap a C) (condition a C)

variable {E : Carrier.{u}} (b : O → E)

/-- Both complete target-label projections retain the SAME whole original restricted unit. -/
theorem target_projection (G : object a C ⟶ CarrierReindexing.object E b) :
    (unit a C ≫ LabelRestriction.map a G).val ≫ CarrierReindexing.toTarget E (fun s => b (a s)) =
      carrierUnit a C ≫ (G.val ≫ CarrierReindexing.toTarget E b) := by
  let U := unit a C ≫ LabelRestriction.map a G
  change U.val ≫ CarrierReindexing.toTarget E (fun s => b (a s)) = _
  exact (congrArg (fun k => U.val ≫ k) (CarrierLabelLift.projection_comp a b).symm).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ CarrierReindexing.toTarget E b) (carrierUnit_projection a C G)).trans
        (Category.assoc _ _ _)))

variable (s : PushoutCocone (sourceMap C) (labelsMap a))

/-- The SAME actual original cocone object assignment at every complete target label. -/
def objectMap (o : O) : s.pt := s.inr.obj (BergnerFixedInitialObjects.vertex O o)

/-- The original whole cocone condition gives precisely the true source-vertex equation. -/
theorem source_vertex (t : A) : s.inl.obj (vertex C t) = objectMap a C s (a t) := by
  have h := congrArg (fun F : BergnerFixedInitialObjects.object A ⟶ s.pt =>
    F.obj (BergnerFixedInitialObjects.vertex A t)) s.condition
  change s.inl.obj ((sourceMap C).obj (BergnerFixedInitialObjects.vertex A t)) =
    s.inr.obj ((labelsMap a).obj (BergnerFixedInitialObjects.vertex A t)) at h
  exact (congrArg s.inl.obj (map_vertex (initial.to C) t)).symm.trans
    (h.trans (congrArg s.inr.obj
      (BergnerFixedInitialObjects.desc_vertex A (fun t => BergnerFixedInitialObjects.vertex O (a t)) t)))

/-- The SAME original source cocone map as an actual full restricted fixed-label input. -/
def input : C ⟶ LabelRestriction.object a (CarrierReindexing.object s.pt (objectMap a C s)) :=
  CarrierLabelReadback.map C (fun t => objectMap a C s (a t)) s.inl (source_vertex a C s)

/-- The existing original presentation descender into the actual cocone's complete original target. -/
def fixedDesc : object a C ⟶ CarrierReindexing.object s.pt (objectMap a C s) :=
  LabelPushforward.desc a C (input a C s)

/-- The SAME entire original carrier cocone descender. -/
def desc : (object a C).val ⟶ s.pt :=
  (fixedDesc a C s).val ≫ CarrierReindexing.toTarget s.pt (objectMap a C s)

/-- The actual original whole source cocone leg is retained by its SAME descender. -/
theorem desc_left : carrierUnit a C ≫ desc a C s = s.inl := by
  have h := congrArg (fun F : C ⟶ LabelRestriction.object a (CarrierReindexing.object s.pt (objectMap a C s)) =>
    F.val ≫ CarrierReindexing.toTarget s.pt (fun t => objectMap a C s (a t)))
      (unit_desc a C (input a C s))
  exact (target_projection a C (objectMap a C s) (fixedDesc a C s)).symm.trans
    (h.trans (CarrierLabelReadback.map_fac C (fun t => objectMap a C s (a t)) s.inl (source_vertex a C s)))

/-- The complete original target-label cocone leg is retained by that SAME descender. -/
theorem desc_right : targetMap a C ≫ desc a C s = s.inr := by
  apply (BergnerFixedInitialObjects.homEquiv O s.pt).injective
  funext o
  change (desc a C s).obj ((targetMap a C).obj (BergnerFixedInitialObjects.vertex O o)) =
    objectMap a C s o
  exact (congrArg (desc a C s).obj (map_vertex (initial.to (object a C)) o)).trans
    (congrArg (objectMap a C s) (map_vertex (fixedDesc a C s) o))

/-- Any actual entire original cocone extension has the SAME original target-label assignment. -/
theorem desc_labels (H : (object a C).val ⟶ s.pt) (hH : targetMap a C ≫ H = s.inr) (o : O) :
    H.obj (vertex (object a C) o) = objectMap a C s o := by
  have h := congrArg (fun F : BergnerFixedInitialObjects.object O ⟶ s.pt =>
    F.obj (BergnerFixedInitialObjects.vertex O o)) hH
  exact (congrArg H.obj (map_vertex (initial.to (object a C)) o)).symm.trans h

/-- The SAME whole original source and object-label legs uniquely determine every full enriched extension. -/
theorem desc_unique (H : (object a C).val ⟶ s.pt)
    (hF : carrierUnit a C ≫ H = s.inl) (hG : targetMap a C ≫ H = s.inr) : H = desc a C s := by
  let R : object a C ⟶ CarrierReindexing.object s.pt (objectMap a C s) :=
    CarrierLabelReadback.map (object a C) (objectMap a C s) H (desc_labels a C s H hG)
  have hr : R.val ≫ CarrierReindexing.toTarget s.pt (objectMap a C s) = H :=
    CarrierLabelReadback.map_fac (object a C) (objectMap a C s) H (desc_labels a C s H hG)
  have hu : unit a C ≫ LabelRestriction.map a R = input a C s := by
    apply CarrierLabelMaps.projection_injective (fun t => objectMap a C s (a t))
    exact (target_projection a C (objectMap a C s) R).trans
      ((congrArg (fun k => carrierUnit a C ≫ k) hr).trans
        (hF.trans (CarrierLabelReadback.map_fac C (fun t => objectMap a C s (a t))
          s.inl (source_vertex a C s)).symm))
  have he : R = fixedDesc a C s := LabelPushforward.desc_unique a C (input a C s) R hu
  exact hr.symm.trans
    (congrArg (fun G : object a C ⟶ CarrierReindexing.object s.pt (objectMap a C s) =>
      G.val ≫ CarrierReindexing.toTarget s.pt (objectMap a C s)) he)

/-- The actual original carrier label cocone has its genuine full varying-object universal property. -/
def isColimit : IsColimit (cocone a C) :=
  PushoutCocone.IsColimit.mk (condition a C) (desc a C) (desc_left a C) (desc_right a C) (desc_unique a C)

/-- The SAME original source/unit/label square is a genuine global enriched pushout for every label map. -/
theorem isPushout : IsPushout (sourceMap C) (labelsMap a) (carrierUnit a C) (targetMap a C) :=
  IsPushout.of_isColimit (isColimit a C)

end CategoryTheory.SimplicialEnrichment.FixedObjects.LabelPushforward.GlobalPushout
