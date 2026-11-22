/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CarrierOriginalColimitComparison
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalUnderHomFunctor
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-!
# Original source labels in a genuine filtered under-category colimit

The actual original forgetful functor retains the full filtered carrier
colimit. Its SAME target-label bijection has a genuine inverse. Each
complete original under-root map retains precisely the label of its
original image in the full target, by the original cocone triangle.
-/

noncomputable section
universe u
open CategoryTheory Limits

namespace CategoryTheory.SimplicialEnrichment.OriginalUnderHomColimit
attribute [local instance] IsFiltered.isConnected

variable {C : Carrier.{u}} {J : Type u} [Category.{u} J] [IsFiltered J]
  (U : J ⥤ Under C) (s : Cocone U) (hs : IsColimit s)

/-- The SAME complete original underlying carrier diagram. -/
abbrev carrierDiagram : J ⥤ Carrier.{u} := U ⋙ Under.forget C

/-- The genuine original underlying carrier cocone, retaining every complete original leg. -/
abbrev carrierCocone : Cocone (carrierDiagram U) := (Under.forget C).mapCocone s

include hs

/-- The actual connected under-category colimit is the SAME genuine underlying carrier colimit. -/
def carrierIsColimit : IsColimit (carrierCocone U s) := isColimitOfPreserves (Under.forget C) hs

/-- The original carrier-colimit label function has its genuine full inverse. -/
def labelsEquiv : (CarrierColimit.labelCocone (carrierDiagram U)).pt ≃ s.pt.right :=
  Equiv.ofBijective (CarrierColimit.targetLabels (carrierDiagram U) (carrierCocone U s))
    (CarrierColimit.targetLabels_bijective (carrierDiagram U) (carrierCocone U s)
      (carrierIsColimit U s hs))

/-- The original source object has the label of its SAME full original terminal image. -/
def rootLabel (x : C) : (CarrierColimit.labelCocone (carrierDiagram U)).pt :=
  (labelsEquiv U s hs).symm (s.pt.hom.obj x)

/-- The SAME genuine target-label inverse reads back exactly the original terminal object image. -/
theorem rootLabel_target (x : C) :
    CarrierColimit.targetLabels (carrierDiagram U) (carrierCocone U s) (rootLabel U s hs x) =
      s.pt.hom.obj x := (labelsEquiv U s hs).apply_symm_apply _

/-- Every complete original root map retains the SAME original source label in the actual carrier colimit. -/
theorem stage_rootLabel (i : J) (x : C) :
    CarrierLabelDiagram.label (carrierDiagram U) (CarrierColimit.labelCocone (carrierDiagram U)) i
      ((U.obj i).hom.obj x) = rootLabel U s hs x := by
  apply (labelsEquiv U s hs).injective
  have hi := congrFun
    (CarrierColimit.input_object_eq (carrierDiagram U) (carrierCocone U s) i) ((U.obj i).hom.obj x)
  have hr := congrArg (fun F : C ⟶ s.pt.right => F.obj x) (Under.w (s.ι.app i))
  exact hi.symm.trans (hr.trans (rootLabel_target U s hs x).symm)

/-- The SAME full original source unit carries each original root image to its actual common label. -/
theorem unit_endpoint (i : J) (x : C) :
    (CarrierLabelDiagram.leg (carrierDiagram U) (CarrierColimit.labelCocone (carrierDiagram U)) i).obj
        ((U.obj i).hom.obj x) =
      FixedObjects.vertex ((CarrierColimit.stages (carrierDiagram U)).obj i) (rootLabel U s hs x) :=
  (CarrierLabelExtension.inclusion_obj ((carrierDiagram U).obj i)
    (CarrierLabelDiagram.label (carrierDiagram U) (CarrierColimit.labelCocone (carrierDiagram U)) i)
      ((U.obj i).hom.obj x)).trans
        (congrArg (FixedObjects.vertex ((CarrierColimit.stages (carrierDiagram U)).obj i))
          (stage_rootLabel U s hs i x))

end CategoryTheory.SimplicialEnrichment.OriginalUnderHomColimit
