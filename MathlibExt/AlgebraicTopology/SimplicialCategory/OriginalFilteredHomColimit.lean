/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFilteredHomUnitComparison
import MathlibExt.AlgebraicTopology.SimplicialCategory.CarrierOriginalColimitComparison
import Mathlib.CategoryTheory.Filtered.Final

/-!
# The complete original Hom tail retains a genuine filtered colimit

The actual original carrier colimit induces the full fixed-label Hom
colimit. The genuine final under-source tail and the SAME full original
unit isomorphism transport its entire cocone, including every coefficient
map. Only the original endpoint equations identify its target with the
full Hom of the two original cocone images.
-/

noncomputable section
universe u
open CategoryTheory Limits

namespace CategoryTheory.SimplicialEnrichment.OriginalFilteredUnderHom
open FixedObjects

variable {J : Type u} [Category.{u} J] (F : J ⥤ Carrier.{u}) (s : Cocone F)
  (j : J) (x y : F.obj j)

/-- The full original fixed-label coefficient cocone on the actual under-source tail. -/
def unitHomCocone : Cocone (unitHomDiagram F j x y) :=
  ((FixedObjects.evaluation
    (CarrierLabelDiagram.label F (CarrierColimit.labelCocone F) j x)
    (CarrierLabelDiagram.label F (CarrierColimit.labelCocone F) j y)).mapCocone
      (CarrierColimit.targetCocone F s)).whisker (Under.forget j)

/-- The SAME entire original unit coefficient map precomposes the actual full tail cocone. -/
def reindexedHomCocone : Cocone (homDiagram F j x y) :=
  (Cocone.precompose (unitHomComparison F j x y)).obj (unitHomCocone F s j x y)

/-- A genuine original carrier colimit gives the genuine full original Hom-tail colimit. -/
def reindexedHomIsColimit [IsFiltered J] (hs : IsColimit s)
    (h : ∀ {a b : J} (f : a ⟶ b), Function.Injective (F.map f).obj) :
    IsColimit (reindexedHomCocone F s j x y) :=
  (IsColimit.precomposeHomEquiv (unitHomIso F j x y h) (unitHomCocone F s j x y)).symm
    ((Functor.Final.isColimitWhiskerEquiv (Under.forget j) _).symm
      (CarrierColimit.fullHomIsColimit F s hs
        (CarrierLabelDiagram.label F (CarrierColimit.labelCocone F) j x)
        (CarrierLabelDiagram.label F (CarrierColimit.labelCocone F) j y)))

/-- The two true original cocone object equations identify precisely the SAME full target Hom. -/
def targetHomIso : (reindexedHomCocone F s j x y).pt ≅
    ((s.ι.app j).obj x ⟶[SSet.{u}] (s.ι.app j).obj y) :=
  eqToIso (congrArg₂ (fun a b : s.pt => a ⟶[SSet.{u}] b)
    (congrFun (CarrierColimit.input_object_eq F s j) x).symm
    (congrFun (CarrierColimit.input_object_eq F s j) y).symm)

/-- The complete original Hom cocone at the images of the SAME two original source objects. -/
def homCocone : Cocone (homDiagram F j x y) where
  pt := (s.ι.app j).obj x ⟶[SSet.{u}] (s.ι.app j).obj y
  ι := (reindexedHomCocone F s j x y).ι ≫
    (Functor.const (Under j)).map (targetHomIso F s j x y).hom

/-- The genuine whole original Hom cocone retains its actual original filtered colimit property. -/
def homIsColimit [IsFiltered J] (hs : IsColimit s)
    (h : ∀ {a b : J} (f : a ⟶ b), Function.Injective (F.map f).obj) :
    IsColimit (homCocone F s j x y) :=
  IsColimit.ofIsoColimit (reindexedHomIsColimit F s j x y hs h)
    (Cocone.ext (targetHomIso F s j x y) (fun _a => rfl))

end CategoryTheory.SimplicialEnrichment.OriginalFilteredUnderHom
