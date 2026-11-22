/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalUnderHomColimitLabels
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalInjectiveLabelUnitHoms
import MathlibExt.AlgebraicTopology.SimplicialCategory.EnrichedOriginalHomSquare
import MathlibExt.AlgebraicTopology.SimplicialCategory.CarrierFilteredObjectInjections

/-!
# The SAME full original under-root unit comparison on every filtered stage

Each original root image retains its actual common colimit label.
The complete original source units induce a genuine natural Hom
comparison. Injective original object transitions give its actual
full inverse at every stage, with all original coefficients retained.
-/

noncomputable section
universe u
open CategoryTheory Limits

namespace CategoryTheory.SimplicialEnrichment.OriginalUnderHomColimit
open FixedObjects

variable {C : Carrier.{u}} {J : Type u} [Category.{u} J] [IsFiltered J]
  (U : J ⥤ Under C) (s : Cocone U) (hs : IsColimit s) (x y : C)

/-- The complete original Hom diagram on the SAME actual images of the source pair. -/
abbrev homDiagram : J ⥤ SSet.{u} := U ⋙ OriginalUnderHom.functor C x y

/-- The actual full fixed-label Hom diagram at the SAME original root labels. -/
def unitHomDiagram : J ⥤ SSet.{u} :=
  CarrierColimit.stages (carrierDiagram U) ⋙ FixedObjects.evaluation
    (rootLabel U s hs x) (rootLabel U s hs y)

/-- Each coefficient is the SAME complete original source-unit map at the two original images. -/
def unitHomMap (i : J) : (homDiagram U x y).obj i ⟶ (unitHomDiagram U s hs x y).obj i :=
  (CarrierLabelDiagram.leg (carrierDiagram U) (CarrierColimit.labelCocone (carrierDiagram U)) i).map
      ((U.obj i).hom.obj x) ((U.obj i).hom.obj y) ≫
    eqToHom (congrArg₂ (fun a b : ((CarrierColimit.stages (carrierDiagram U)).obj i).val => a ⟶[SSet.{u}] b)
      (unit_endpoint U s hs i x) (unit_endpoint U s hs i y))

/-- The actual whole original source squares retain naturality of the full original unit coefficients. -/
theorem unitHomMap_naturality {i j : J} (f : i ⟶ j) :
    (homDiagram U x y).map f ≫ unitHomMap U s hs x y j =
      unitHomMap U s hs x y i ≫ (unitHomDiagram U s hs x y).map f := by
  let E := CarrierLabelDiagram.leg (carrierDiagram U) (CarrierColimit.labelCocone (carrierDiagram U)) i
  let H := CarrierLabelDiagram.leg (carrierDiagram U) (CarrierColimit.labelCocone (carrierDiagram U)) j
  let G := (CarrierColimit.stages (carrierDiagram U)).map f
  exact (originalHomSquare E (U.map f).right G.val H
    (CarrierLabelDiagram.leg_naturality (carrierDiagram U) (CarrierColimit.labelCocone (carrierDiagram U)) f)
      ((U.obj i).hom.obj x) ((U.obj i).hom.obj y)
        (unit_endpoint U s hs i x) (unit_endpoint U s hs i y)
          (OriginalUnderHom.endpoint C (U.map f) x) (OriginalUnderHom.endpoint C (U.map f) y)
            (map_vertex G (rootLabel U s hs x)) (map_vertex G (rootLabel U s hs y))
              (unit_endpoint U s hs j x) (unit_endpoint U s hs j y)).symm

/-- The SAME entire original source units give the actual natural coefficient comparison. -/
def unitHomComparison : homDiagram U x y ⟶ unitHomDiagram U s hs x y where
  app := unitHomMap U s hs x y
  naturality _i _j f := unitHomMap_naturality U s hs x y f

/-- Actual original stage object injectivity gives the full original unit coefficient inverse. -/
theorem unitHomMap_isIso
    (h : ∀ {i j : J} (f : i ⟶ j), Function.Injective (U.map f).right.obj) (i : J) :
    IsIso (unitHomMap U s hs x y i) := by
  let E := CarrierLabelDiagram.leg (carrierDiagram U) (CarrierColimit.labelCocone (carrierDiagram U)) i
  let _ : IsIso (E.map ((U.obj i).hom.obj x) ((U.obj i).hom.obj y)) :=
    CarrierLabelExtension.inclusion_hom_isIso ((carrierDiagram U).obj i)
      (CarrierLabelDiagram.label (carrierDiagram U) (CarrierColimit.labelCocone (carrierDiagram U)) i)
        (CarrierColimit.label_injective (carrierDiagram U) h i) _ _
  let t := congrArg₂ (fun a b : ((CarrierColimit.stages (carrierDiagram U)).obj i).val => a ⟶[SSet.{u}] b)
    (unit_endpoint U s hs i x) (unit_endpoint U s hs i y)
  let T : (E.obj ((U.obj i).hom.obj x) ⟶[SSet.{u}] E.obj ((U.obj i).hom.obj y)) ≅
      (unitHomDiagram U s hs x y).obj i := eqToIso t
  let _ : IsIso T.hom := T.isIso_hom
  exact inferInstanceAs (IsIso (E.map ((U.obj i).hom.obj x) ((U.obj i).hom.obj y) ≫ T.hom))

/-- The complete original coefficient comparison has a genuine full natural inverse. -/
def unitHomIso
    (h : ∀ {i j : J} (f : i ⟶ j), Function.Injective (U.map f).right.obj) :
    homDiagram U x y ≅ unitHomDiagram U s hs x y :=
  NatIso.ofComponents
    (fun i => @asIso SSet.{u} inferInstance ((homDiagram U x y).obj i)
      ((unitHomDiagram U s hs x y).obj i) (unitHomMap U s hs x y i)
        (unitHomMap_isIso U s hs x y h i))
    (fun {_i _j} f => unitHomMap_naturality U s hs x y f)

end CategoryTheory.SimplicialEnrichment.OriginalUnderHomColimit
