/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CarrierLimitLift

/-!
# The full universal property of actual varying-object enriched limits

The original object-limit property fixes every individual object of a
whole candidate cone map. Its canonical original fixed-label readback
then has all the same full cone triangles. Uniqueness in the actual
restricted Hom limit proves uniqueness of the entire original enriched
map. Together with the constructed whole lift this proves the genuine
changing-object enriched limit, not merely separate Hom limits.
-/

noncomputable section
universe u v
open CategoryTheory Limits

namespace CategoryTheory.SimplicialEnrichment.CarrierLimit
open FixedObjects

variable {J : Type v} [SmallCategory J] (F : J ⥤ Carrier.{u})
variable [HasLimit (F ⋙ forgetObjects)] [HasLimitsOfShape J SSet.{u}]

/-- The original object label of any actual limit object reads every complete original cone
projection. -/
theorem projection_obj_label (j : J) (x : object F) :
    (projection F j).obj x = (limit.π (F ⋙ forgetObjects) j) (label (fixedObject F) x) :=
  (congrArg (projection F j).obj (vertex_label (fixedObject F) x).symm).trans
    (projection_obj F j (label (fixedObject F) x))

/-- The genuine object-limit property fixes each individual original label of any whole cone map. -/
theorem label_of_fac (s : Cone F) (m : s.pt ⟶ object F)
    (hm : ∀ j, m ≫ projection F j = s.π.app j) (x : s.pt) :
    label (fixedObject F) (m.obj x) = coneLabel F s x := by
  apply Types.limit_ext (F ⋙ forgetObjects)
  intro j
  have hx : (projection F j).obj (m.obj x) = (s.π.app j).obj x :=
    congrArg (fun G : s.pt ⟶ F.obj j => G.obj x) (hm j)
  exact (projection_obj_label F j (m.obj x)).symm.trans
    (hx.trans (coneLabel_projection F s j x).symm)

/-- Every actual whole cone map has the SAME original individual-object function as the
constructed lift. -/
theorem objects_of_fac (s : Cone F) (m : s.pt ⟶ object F)
    (hm : ∀ j, m ≫ projection F j = s.π.app j) (x : s.pt) :
    m.obj x = vertex (fixedObject F) (coneLabel F s x) :=
  (vertex_label (fixedObject F) (m.obj x)).symm.trans
    (congrArg (vertex (fixedObject F)) (label_of_fac F s m hm x))

/-- Read the SAME entire candidate cone map into the actual original restricted enrichment. -/
def readback (s : Cone F) (m : s.pt ⟶ object F)
    (hm : ∀ j, m ≫ projection F j = s.π.app j) :
    CarrierReindexing.source s.pt ⟶ (restriction F s).obj (fixedObject F) :=
  CarrierLabelReadback.map (CarrierReindexing.source s.pt)
    (fun x => vertex (fixedObject F) (coneLabel F s x)) m (objects_of_fac F s m hm)

/-- The complete original candidate map is recovered, with EVERY original Hom retained. -/
theorem readback_fac (s : Cone F) (m : s.pt ⟶ object F)
    (hm : ∀ j, m ≫ projection F j = s.π.app j) :
    (readback F s m hm).val ≫ LabelRestriction.projection (coneLabel F s) (fixedObject F) = m :=
  CarrierLabelReadback.map_fac (CarrierReindexing.source s.pt)
    (fun x => vertex (fixedObject F) (coneLabel F s x)) m (objects_of_fac F s m hm)

private theorem restrictedMap_projection (s : Cone F)
    (G : CarrierReindexing.source s.pt ⟶ (restriction F s).obj (fixedObject F)) (j : J) :
    (G.val ≫ LabelRestriction.projection (coneLabel F s) (fixedObject F)) ≫ projection F j =
      (G.val ≫ ((restriction F s).map (HomLimit.projection (diagram F) j)).val) ≫
        restrictedProjection F s j :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun H => G.val ≫ H)
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun H => H ≫ CarrierLimitLabelDiagram.projection F
          (limit.cone (F ⋙ forgetObjects)) j)
            (LabelRestriction.projection_naturality (coneLabel F s) (HomLimit.projection
              (diagram F) j)).symm).trans
          (Category.assoc _ _ _)))).trans (Category.assoc _ _ _).symm)

/-- The SAME whole candidate cone map has every complete triangle in the actual restricted
fixed-label Hom limit. -/
theorem readback_projection (s : Cone F) (m : s.pt ⟶ object F)
    (hm : ∀ j, m ≫ projection F j = s.π.app j) (j : J) :
    readback F s m hm ≫ (restriction F s).map (HomLimit.projection (diagram F) j) =
      fixedLeg F s j := by
  apply CarrierLabelMaps.projection_injective
    (fun x => (limit.π (F ⋙ forgetObjects) j) (coneLabel F s x))
  let r := CarrierReindexing.toTarget (F.obj j)
    (fun x => (limit.π (F ⋙ forgetObjects) j) (coneLabel F s x))
  let G := readback F s m hm
  change (G.val ≫ ((restriction F s).map (HomLimit.projection (diagram F) j)).val) ≫ r =
    (fixedLeg F s j).val ≫ r
  have left : (G.val ≫ ((restriction F s).map (HomLimit.projection (diagram F) j)).val) ≫ r =
      s.π.app j :=
    (congrArg (fun H => (G.val ≫ ((restriction F s).map (HomLimit.projection (diagram F)
      j)).val) ≫ H)
      (restrictedProjection_original F s j).symm).trans
        ((restrictedMap_projection F s G j).symm.trans
          ((congrArg (fun H => H ≫ projection F j) (readback_fac F s m hm)).trans (hm j)))
  have right : (fixedLeg F s j).val ≫ r = s.π.app j :=
    CarrierLabelReadback.map_fac (CarrierReindexing.source s.pt)
      (fun x => (limit.π (F ⋙ forgetObjects) j) (coneLabel F s x))
        (s.π.app j) (fun x => (coneLabel_projection F s j x).symm)
  exact left.trans right.symm

/-- The SAME entire original enriched cone map is uniquely the constructed whole lift. -/
theorem lift_unique (s : Cone F) (m : s.pt ⟶ object F)
    (hm : ∀ j, m ≫ projection F j = s.π.app j) : m = lift F s := by
  have h : readback F s m hm = fixedLift F s :=
    (restrictedIsLimit F s).uniq (fixedCone F s) (readback F s m hm) (readback_projection F s m hm)
  exact (readback_fac F s m hm).symm.trans
    (congrArg (fun G : CarrierReindexing.source s.pt ⟶ (restriction F s).obj (fixedObject F) =>
      G.val ≫ LabelRestriction.projection (coneLabel F s) (fixedObject F)) h)

/-- The actual original compatible-object/full-Hom cone has the full changing-object
enriched limit universal
property. -/
def isLimit : IsLimit (cone F) where
  lift := lift F
  fac := lift_fac F
  uniq := lift_unique F

end CategoryTheory.SimplicialEnrichment.CarrierLimit
