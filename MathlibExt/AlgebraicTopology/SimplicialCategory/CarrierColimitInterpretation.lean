/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CarrierColimitCocone
import MathlibExt.AlgebraicTopology.SimplicialCategory.CarrierLabelLift

/-! # Whole original cocones interpret the actual enriched colimit

The original target object function is obtained from the genuine Type
colimit. Each complete original cocone leg has that exact label equation.
Its actual enriched extension supplies a fixed-label cocone; the whole
source equations prove its naturality, including all original Hom maps.
-/

noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory

namespace CategoryTheory.SimplicialEnrichment.CarrierColimit
open FixedObjects

variable {J : Type u} [Category.{u} J] (F : J ⥤ Carrier.{u}) (s : Cocone F)

/-- The actual target object function induced by all original cocone object maps. -/
def targetLabels : (labelCocone F).pt → s.pt :=
  colimit.desc (F ⋙ forgetObjects) (forgetObjects.mapCocone s)

/-- Each entire original cocone leg has its exact Type-colimit object-function equation. -/
theorem input_object_eq (j : J) : (s.ι.app j).obj =
    fun x => targetLabels F s (CarrierLabelDiagram.label F (labelCocone F) j x) := by
  funext x
  exact (ConcreteCategory.congr_hom (C := Type u)
    (colimit.ι_desc (forgetObjects.mapCocone s) j) x).symm

/-- The actual whole original cocone leg extended to the original target labels. -/
def fixedLeg (j : J) : (stages F).obj j ⟶ CarrierReindexing.object s.pt (targetLabels F s) :=
  CarrierLabelLift.fixedLift (F.obj j) (CarrierLabelDiagram.label F (labelCocone F) j)
    (targetLabels F s) (s.ι.app j) (input_object_eq F s j)

/-- Read the extended leg as its same complete changing-object target functor. -/
def rawLeg (j : J) : ((stages F).obj j).val ⟶ s.pt :=
  (fixedLeg F s j).val ≫ CarrierReindexing.toTarget s.pt (targetLabels F s)

/-- The entire original stage functor is retained after its actual source unit. -/
theorem rawLeg_fac (j : J) :
    CarrierLabelDiagram.leg F (labelCocone F) j ≫ rawLeg F s j = s.ι.app j :=
  CarrierLabelLift.lift_fac (F.obj j) (CarrierLabelDiagram.label F (labelCocone F) j)
    (targetLabels F s) (s.ι.app j) (input_object_eq F s j)

/-- Every original colimit label has its same prescribed target image in each extended leg. -/
theorem rawLeg_obj (j : J) (x : (labelCocone F).pt) :
    (rawLeg F s j).obj x = targetLabels F s x :=
  CarrierLabelLift.lift_obj (F.obj j) (CarrierLabelDiagram.label F (labelCocone F) j)
    (targetLabels F s) (s.ι.app j) (input_object_eq F s j) x

/-- The actual fixed-label extensions satisfy the same whole original cocone equations. -/
theorem fixedLeg_naturality {j k : J} (f : j ⟶ k) :
    (stages F).map f ≫ fixedLeg F s k = fixedLeg F s j := by
  let H : ((stages F).obj j).val ⟶ s.pt := ((stages F).map f).val ≫ rawLeg F s k
  have ho : H.obj = targetLabels F s := by
    funext x
    have hx := map_vertex ((stages F).map f) x
    change ((stages F).map f).val.obj x = x at hx
    exact (rawLeg_obj F s k (((stages F).map f).val.obj x)).trans
      (congrArg (targetLabels F s) hx)
  have hf : CarrierLabelDiagram.leg F (labelCocone F) j ≫ H = s.ι.app j := by
    change CarrierLabelDiagram.leg F (labelCocone F) j ≫
      (((stages F).map f).val ≫ rawLeg F s k) = s.ι.app j
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun G => G ≫ rawLeg F s k)
        (CarrierLabelDiagram.leg_naturality F (labelCocone F) f)).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (fun G => F.map f ≫ G) (rawLeg_fac F s k)).trans (s.w f))))
  have hu : H = rawLeg F s j :=
    CarrierLabelLift.lift_unique (F.obj j) (CarrierLabelDiagram.label F (labelCocone F) j)
      (targetLabels F s) (s.ι.app j) (input_object_eq F s j) H ho hf
  apply CarrierLabelMaps.projection_injective (targetLabels F s)
  change (((stages F).map f).val ≫ (fixedLeg F s k).val) ≫
    CarrierReindexing.toTarget s.pt (targetLabels F s) = rawLeg F s j
  exact (Category.assoc _ _ _).trans hu

/-- All whole original cocone legs form the genuine cocone on the same fixed target labels. -/
def targetCocone : Cocone (stages F) where
  pt := CarrierReindexing.object s.pt (targetLabels F s)
  ι := {
    app := fixedLeg F s
    naturality _ _ f := (fixedLeg_naturality F s f).trans (Category.comp_id _).symm }

end CategoryTheory.SimplicialEnrichment.CarrierColimit
