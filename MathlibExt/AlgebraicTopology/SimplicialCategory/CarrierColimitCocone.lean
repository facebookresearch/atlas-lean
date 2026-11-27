/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CarrierLabelDiagram
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectColimits
import Mathlib.CategoryTheory.Limits.Types.Colimits

/-! # The actual changing-object enriched colimit cocone

The object type is the actual Type colimit of the original label diagram.
Pushforward along its entire cocone gives the fixed-label diagram. Its
genuine enriched colimit supplies the carrier, while every original stage
leg retains the original object map and complete Hom functor.
-/

noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory

namespace CategoryTheory.SimplicialEnrichment.CarrierColimit
open FixedObjects

variable {J : Type u} [Category.{u} J] (F : J ⥤ Carrier.{u})

/-- The genuine Type-colimit cocone of the original object functions. -/
def labelCocone : Cocone (F ⋙ forgetObjects) := colimit.cocone (F ⋙ forgetObjects)

/-- The actual entire pushed-forward diagram on the original colimit labels. -/
def stages : J ⥤ FixedObjects (labelCocone F).pt :=
  CarrierLabelDiagram.functor F (labelCocone F)

/-- The genuine fixed-label enriched colimit of those original stage sources. -/
abbrev fixedObject : FixedObjects (labelCocone F).pt := DiagramPresentation.object (stages F)

/-- The actual enriched carrier with the original Type-colimit object labels. -/
abbrev object : Carrier.{u} := (fixedObject F).val

/-- Every original stage functor factors through its complete path source and fixed-label
colimit leg. -/
def leg (j : J) : F.obj j ⟶ object F :=
  CarrierLabelDiagram.leg F (labelCocone F) j ≫ (DiagramPresentation.injection (stages F) j).val

/-- The whole original stage object is sent to its actual original Type-colimit label. -/
theorem leg_obj (j : J) (x : F.obj j) :
    (leg F j).obj x = vertex (fixedObject F) (CarrierLabelDiagram.label F (labelCocone F) j x) :=
  map_vertex (DiagramPresentation.injection (stages F) j)
    (CarrierLabelDiagram.label F (labelCocone F) j x)

/-- All original stage functors satisfy the full enriched cocone equations. -/
theorem leg_naturality {j k : J} (f : j ⟶ k) : F.map f ≫ leg F k = leg F j := by
  have hi := congrArg
    (fun H : (stages F).obj j ⟶ fixedObject F => H.val)
    ((DiagramPresentation.cocone (stages F)).w f)
  change (CarrierLabelDiagram.map F (labelCocone F) f).val ≫
    (DiagramPresentation.injection (stages F) k).val =
      (DiagramPresentation.injection (stages F) j).val at hi
  change F.map f ≫ (CarrierLabelDiagram.leg F (labelCocone F) k ≫
      (DiagramPresentation.injection (stages F) k).val) =
    CarrierLabelDiagram.leg F (labelCocone F) j ≫
      (DiagramPresentation.injection (stages F) j).val
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun H => H ≫ (DiagramPresentation.injection (stages F) k).val)
      (CarrierLabelDiagram.leg_naturality F (labelCocone F) f).symm).trans
        ((Category.assoc _ _ _).trans
          (congrArg (fun H => CarrierLabelDiagram.leg F (labelCocone F) j ≫ H) hi)))

/-- The actual whole enriched cocone, constructed on the original object-colimit labels. -/
def cocone : Cocone F where
  pt := object F
  ι := {
    app := leg F
    naturality _ _ f := (leg_naturality F f).trans (Category.comp_id _).symm }

end CategoryTheory.SimplicialEnrichment.CarrierColimit
