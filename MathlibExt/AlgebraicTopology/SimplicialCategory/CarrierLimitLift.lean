/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CarrierLimitCone
import MathlibExt.AlgebraicTopology.SimplicialCategory.CarrierReindexingNested
import MathlibExt.AlgebraicTopology.SimplicialCategory.LabelRestrictionProjection
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Types.Limits

/-!
# Whole changing-object enriched cone lifts

Every original cone has its actual map to the original object limit.
Restriction along that complete map is the proved original right
adjoint and preserves the existing full fixed-label Hom limit. The
original cone maps therefore give a genuine whole fixed-label cone,
whose full lift projects to the original varying-object enrichment.
Every original object and entire enriched projection is read back.
-/

noncomputable section
universe u v
open CategoryTheory Limits

namespace CategoryTheory.SimplicialEnrichment.CarrierLimit
open FixedObjects

variable {J : Type v} [SmallCategory J] (F : J ⥤ Carrier.{u})
variable [HasLimit (F ⋙ forgetObjects)]

/-- The SAME whole original cone's native map to its individual-object limit. -/
def coneLabel (s : Cone F) : s.pt → labels F :=
  limit.lift (F ⋙ forgetObjects) (forgetObjects.mapCone s)

/-- Each supplied original cone object map is exactly the corresponding original limit
projection. -/
theorem coneLabel_projection (s : Cone F) (j : J) (x : s.pt) :
    (limit.π (F ⋙ forgetObjects) j) (coneLabel F s x) = (s.π.app j).obj x :=
  ConcreteCategory.congr_hom (C := Type u) (limit.lift_π (forgetObjects.mapCone s) j) x

/-- The full original fixed-label restriction along that actual cone object map. -/
abbrev restriction (s : Cone F) : FixedObjects (labels F) ⥤ FixedObjects (s.pt : Type u) :=
  LabelRestriction.functor (coneLabel F s)

/-- The SAME original double projection from a restricted diagram object. -/
def restrictedProjection (s : Cone F) (j : J) :
    ((restriction F s).obj ((diagram F).obj j)).val ⟶ F.obj j :=
  LabelRestriction.projection (coneLabel F s) ((diagram F).obj j) ≫
    CarrierLimitLabelDiagram.projection F (limit.cone (F ⋙ forgetObjects)) j

/-- The entire restricted projection is exactly the original identity-Hom projection at the
actual composite label
map. -/
theorem restrictedProjection_original (s : Cone F) (j : J) :
    restrictedProjection F s j = CarrierReindexing.toTarget (F.obj j)
      (fun x => (limit.π (F ⋙ forgetObjects) j) (coneLabel F s x)) :=
  CarrierReindexing.nested_projection (F.obj j) (limit.π (F ⋙ forgetObjects) j) (coneLabel F s)

/-- The SAME whole original restricted projections satisfy every complete diagram naturality
square. -/
theorem restrictedProjection_naturality (s : Cone F) {j k : J} (f : j ⟶ k) :
    ((restriction F s).map ((diagram F).map f)).val ≫ restrictedProjection F s k =
      restrictedProjection F s j ≫ F.map f :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun G => G ≫ CarrierLimitLabelDiagram.projection F
      (limit.cone (F ⋙ forgetObjects)) k)
        (LabelRestriction.projection_naturality (coneLabel F s) ((diagram F).map f))).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun G => LabelRestriction.projection (coneLabel F s) ((diagram F).obj j) ≫ G)
          (CarrierLimitLabelDiagram.projection_naturality F (limit.cone (F ⋙
            forgetObjects)) f)).trans
            (Category.assoc _ _ _).symm)))

/-- The actual original cone leg read back into its SAME restricted fixed-label target. -/
def fixedLeg (s : Cone F) (j : J) :
    CarrierReindexing.source s.pt ⟶ (restriction F s).obj ((diagram F).obj j) :=
  CarrierLabelReadback.map (CarrierReindexing.source s.pt)
    (fun x => (limit.π (F ⋙ forgetObjects) j) (coneLabel F s x))
      (s.π.app j) (fun x => (coneLabel_projection F s j x).symm)

/-- Projection recovers the SAME whole original cone leg, including its entire Hom maps. -/
theorem fixedLeg_fac (s : Cone F) (j : J) :
    (fixedLeg F s j).val ≫ restrictedProjection F s j = s.π.app j :=
  (congrArg (fun G => (fixedLeg F s j).val ≫ G) (restrictedProjection_original F s j)).trans
    (CarrierLabelReadback.map_fac (CarrierReindexing.source s.pt)
      (fun x => (limit.π (F ⋙ forgetObjects) j) (coneLabel F s x))
        (s.π.app j) (fun x => (coneLabel_projection F s j x).symm))

/-- The complete supplied changing-object cone gives its genuine cone in the actual
fixed-label restriction. -/
def fixedCone (s : Cone F) : Cone (diagram F ⋙ restriction F s) where
  pt := CarrierReindexing.source s.pt
  π := {
    app := fixedLeg F s
    naturality j k f := by
      apply CarrierLabelMaps.projection_injective
        (fun x => (limit.π (F ⋙ forgetObjects) k) (coneLabel F s x))
      let r := CarrierReindexing.toTarget (F.obj k)
        (fun x => (limit.π (F ⋙ forgetObjects) k) (coneLabel F s x))
      change (𝟙 (CarrierReindexing.source s.pt) ≫ fixedLeg F s k).val ≫ r =
        ((fixedLeg F s j).val ≫ ((restriction F s).map ((diagram F).map f)).val) ≫ r
      have left : (fixedLeg F s k).val ≫ r = s.π.app k :=
        CarrierLabelReadback.map_fac (CarrierReindexing.source s.pt)
          (fun x => (limit.π (F ⋙ forgetObjects) k) (coneLabel F s x))
            (s.π.app k) (fun x => (coneLabel_projection F s k x).symm)
      have right : ((fixedLeg F s j).val ≫ ((restriction F s).map ((diagram F).map f)).val) ≫ r =
          s.π.app k :=
        (congrArg (fun G => ((fixedLeg F s j).val ≫
          ((restriction F s).map ((diagram F).map f)).val) ≫ G)
            (restrictedProjection_original F s k).symm).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (fun G => (fixedLeg F s j).val ≫ G)
              (restrictedProjection_naturality F s f)).trans
                ((Category.assoc _ _ _).symm.trans
                  ((congrArg (fun G => G ≫ F.map f) (fixedLeg_fac F s j)).trans (s.w f)))))
      exact (congrArg (fun G : CarrierReindexing.source s.pt ⟶ (restriction F s).obj
        ((diagram F).obj k) =>
        G.val ≫ r) (Category.id_comp (fixedLeg F s k))).trans (left.trans right.symm) }

variable [HasLimitsOfShape J SSet.{u}]

/-- The actual original label-restriction right adjoint preserves the full original
Hom-limit cone. -/
def restrictedIsLimit (s : Cone F) :
    IsLimit ((restriction F s).mapCone (HomLimit.cone (diagram F))) := by
  let _ : PreservesLimitsOfSize.{v, v} (restriction F s) :=
    (LabelPushforward.adjunction (coneLabel F s)).rightAdjoint_preservesLimits
  exact isLimitOfPreserves (restriction F s) (HomLimit.isLimit (diagram F))

/-- The entire actual fixed-label universal cone lift. -/
def fixedLift (s : Cone F) :
    CarrierReindexing.source s.pt ⟶ (restriction F s).obj (fixedObject F) :=
  (restrictedIsLimit F s).lift (fixedCone F s)

/-- Each complete original fixed-label cone triangle holds for the SAME actual lift. -/
theorem fixedLift_fac (s : Cone F) (j : J) :
    fixedLift F s ≫ (restriction F s).map (HomLimit.projection (diagram F) j) = fixedLeg F s j :=
  (restrictedIsLimit F s).fac (fixedCone F s) j

/-- The genuine entire changing-object enriched cone lift. -/
def lift (s : Cone F) : s.pt ⟶ object F :=
  (fixedLift F s).val ≫ LabelRestriction.projection (coneLabel F s) (fixedObject F)

/-- The actual universal enriched lift has the SAME native individual-object map. -/
theorem lift_obj (s : Cone F) (x : s.pt) :
    (lift F s).obj x = vertex (fixedObject F) (coneLabel F s x) :=
  congrArg (fun y => vertex (fixedObject F) (coneLabel F s y)) (map_vertex (fixedLift F s) x)

/-- Every complete original cone projection is recovered by the SAME entire enriched lift. -/
theorem lift_fac (s : Cone F) (j : J) : lift F s ≫ projection F j = s.π.app j := by
  have h := congrArg (fun G : CarrierReindexing.source s.pt ⟶ (restriction F s).obj
    ((diagram F).obj j) =>
    G.val ≫ restrictedProjection F s j) (fixedLift_fac F s j)
  have h' : lift F s ≫ projection F j =
      ((fixedLift F s).val ≫ ((restriction F s).map (HomLimit.projection (diagram F) j)).val) ≫
        restrictedProjection F s j := by
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun G => (fixedLift F s).val ≫ G)
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun G => G ≫ CarrierLimitLabelDiagram.projection F
            (limit.cone (F ⋙ forgetObjects)) j)
              (LabelRestriction.projection_naturality (coneLabel F s) (HomLimit.projection
                (diagram F) j)).symm).trans
            (Category.assoc _ _ _)))).trans (Category.assoc _ _ _).symm)
  exact h'.trans (h.trans (fixedLeg_fac F s j))

end CategoryTheory.SimplicialEnrichment.CarrierLimit
