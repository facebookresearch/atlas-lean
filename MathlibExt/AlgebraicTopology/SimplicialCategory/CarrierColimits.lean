/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CarrierColimitInterpretation

/-! # Genuine arbitrary small colimits of changing-object simplicial enrichments

The actual Type-colimit labels and the proved fixed-label enriched
colimit give the complete carrier universal property. The universal
object map is derived from every original stage object. Its whole Hom
functor is constructed from the actual cocone and proved unique on all
original stage functors, with no model or comparison-outcome premise.
-/

noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory

namespace CategoryTheory.SimplicialEnrichment.CarrierColimit
open FixedObjects

variable {J : Type u} [Category.{u} J] (F : J ⥤ Carrier.{u})

/-- The genuine enriched fixed-label universal map of the entire original cocone. -/
def fixedDesc (s : Cocone F) : fixedObject F ⟶ (targetCocone F s).pt :=
  DiagramPresentation.desc (stages F) (targetCocone F s)

/-- The whole original changing-object universal map on the actual Type-colimit labels. -/
def desc (s : Cocone F) : object F ⟶ s.pt :=
  (fixedDesc F s).val ≫ CarrierReindexing.toTarget s.pt (targetLabels F s)

/-- The actual universal functor retains the prescribed target image of every original
colimit label. -/
theorem desc_obj (s : Cocone F) (x : (labelCocone F).pt) :
    (desc F s).obj x = targetLabels F s x := by
  have hx := map_vertex (fixedDesc F s) x
  change (fixedDesc F s).val.obj x = x at hx
  exact congrArg (targetLabels F s) hx

/-- The same entire original enriched cocone leg factors through the actual universal map. -/
theorem desc_fac (s : Cocone F) (j : J) : leg F j ≫ desc F s = s.ι.app j := by
  have hi := congrArg
    (fun H : (stages F).obj j ⟶ (targetCocone F s).pt => H.val)
    (DiagramPresentation.desc_fac (stages F) (targetCocone F s) j)
  change (DiagramPresentation.injection (stages F) j).val ≫ (fixedDesc F s).val =
    (fixedLeg F s j).val at hi
  change (CarrierLabelDiagram.leg F (labelCocone F) j ≫
      (DiagramPresentation.injection (stages F) j).val) ≫
      ((fixedDesc F s).val ≫ CarrierReindexing.toTarget s.pt (targetLabels F s)) = s.ι.app j
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun H => CarrierLabelDiagram.leg F (labelCocone F) j ≫ H)
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun H => H ≫ CarrierReindexing.toTarget s.pt (targetLabels F s)) hi))).trans
          (rawLeg_fac F s j))

/-- All original stage object equations determine the same actual universal target object
function. -/
theorem desc_object_unique (s : Cocone F) (d : object F ⟶ s.pt)
    (hd : ∀ j, leg F j ≫ d = s.ι.app j) : d.obj = targetLabels F s := by
  have he : (↾d.obj : (labelCocone F).pt ⟶ (s.pt : Type u)) =
      (↾targetLabels F s : (labelCocone F).pt ⟶ (s.pt : Type u)) := by
    apply colimit.hom_ext
    intro j
    apply ConcreteCategory.hom_ext
    intro x
    have hx := congrArg (fun H : F.obj j ⟶ s.pt => H.obj x) (hd j)
    exact ((congrArg d.obj (leg_obj F j x)).symm.trans hx).trans
      (congrFun (input_object_eq F s j) x)
  funext x
  exact ConcreteCategory.congr_hom (C := Type u) he x

/-- Every whole original carrier map factoring the cocone is the actual constructed
universal functor. -/
theorem desc_unique (s : Cocone F) (d : object F ⟶ s.pt)
    (hd : ∀ j, leg F j ≫ d = s.ι.app j) : d = desc F s := by
  let b := targetLabels F s
  have ho : d.obj = b := desc_object_unique F s d hd
  let G : fixedObject F ⟶ CarrierReindexing.object s.pt b :=
    CarrierLabelReadback.map (fixedObject F) b d (fun x => congrFun ho x)
  have hG : G.val ≫ CarrierReindexing.toTarget s.pt b = d :=
    CarrierLabelReadback.map_fac (fixedObject F) b d (fun x => congrFun ho x)
  have hi : ∀ j, DiagramPresentation.injection (stages F) j ≫ G = fixedLeg F s j := by
    intro j
    let H : ((stages F).obj j).val ⟶ s.pt :=
      (DiagramPresentation.injection (stages F) j).val ≫ d
    have hH : H.obj = b := by
      funext x
      have hx := map_vertex (DiagramPresentation.injection (stages F) j) x
      change (DiagramPresentation.injection (stages F) j).val.obj x = x at hx
      exact (congrFun ho ((DiagramPresentation.injection (stages F) j).val.obj x)).trans
        (congrArg b hx)
    have hF : CarrierLabelDiagram.leg F (labelCocone F) j ≫ H = s.ι.app j :=
      (Category.assoc _ _ _).symm.trans (hd j)
    have hu : H = rawLeg F s j :=
      CarrierLabelLift.lift_unique (F.obj j) (CarrierLabelDiagram.label F (labelCocone F) j)
        b (s.ι.app j) (input_object_eq F s j) H hH hF
    apply CarrierLabelMaps.projection_injective b
    change ((DiagramPresentation.injection (stages F) j).val ≫ G.val) ≫
      CarrierReindexing.toTarget s.pt b = rawLeg F s j
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun H => (DiagramPresentation.injection (stages F) j).val ≫ H) hG).trans hu)
  have hg : G = fixedDesc F s := DiagramPresentation.desc_uniq (stages F) (targetCocone F s) G hi
  exact hG.symm.trans
    (congrArg (fun H : fixedObject F ⟶ CarrierReindexing.object s.pt b =>
      H.val ≫ CarrierReindexing.toTarget s.pt b) hg)

/-- The whole changing-object enriched cocone satisfies the actual colimit universal property. -/
def isColimit : IsColimit (cocone F) where
  desc := desc F
  fac := desc_fac F
  uniq := desc_unique F

/-- Actual small diagram colimits exist in the ordinary carrier category of original
simplicial enrichments. -/
instance hasColimitsOfShape : HasColimitsOfShape J Carrier.{u} where
  has_colimit F := HasColimit.mk ⟨cocone F, isColimit F⟩

end CategoryTheory.SimplicialEnrichment.CarrierColimit
