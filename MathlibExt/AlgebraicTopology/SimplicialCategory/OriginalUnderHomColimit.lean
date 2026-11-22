/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalUnderHomColimitUnit

/-!
# The complete original Hom cocone retains its genuine filtered colimit

The SAME full original source units transport the actual fixed-label
Hom cocone. Its actual carrier-colimit property and genuine natural
inverse give the complete Hom colimit. The original root endpoint
equations retain exactly the full target Hom of the source images.
-/

noncomputable section
universe u
open CategoryTheory Limits

namespace CategoryTheory.SimplicialEnrichment.OriginalUnderHomColimit
open FixedObjects

variable {C : Carrier.{u}} {J : Type u} [Category.{u} J] [IsFiltered J]
  (U : J ⥤ Under C) (s : Cocone U) (hs : IsColimit s) (x y : C)

/-- The actual complete fixed-label Hom cocone at the two SAME original root labels. -/
def unitHomCocone : Cocone (unitHomDiagram U s hs x y) :=
  (FixedObjects.evaluation (rootLabel U s hs x) (rootLabel U s hs y)).mapCocone
    (CarrierColimit.targetCocone (carrierDiagram U) (carrierCocone U s))

/-- The actual full original source units precompose the genuine entire fixed-label cocone. -/
def reindexedHomCocone : Cocone (homDiagram U x y) :=
  (Cocone.precompose (unitHomComparison U s hs x y)).obj (unitHomCocone U s hs x y)

/-- The SAME full original coefficient cocone has the genuine filtered colimit universal property. -/
def reindexedHomIsColimit
    (h : ∀ {i j : J} (f : i ⟶ j), Function.Injective (U.map f).right.obj) :
    IsColimit (reindexedHomCocone U s hs x y) :=
  (IsColimit.precomposeHomEquiv (unitHomIso U s hs x y h) (unitHomCocone U s hs x y)).symm
    (CarrierColimit.fullHomIsColimit (carrierDiagram U) (carrierCocone U s) (carrierIsColimit U s hs)
      (rootLabel U s hs x) (rootLabel U s hs y))

/-- The original root-image equations identify the SAME full target Hom at both actual endpoints. -/
def targetHomIso : (reindexedHomCocone U s hs x y).pt ≅
    (s.pt.hom.obj x ⟶[SSet.{u}] s.pt.hom.obj y) :=
  eqToIso (congrArg₂ (fun a b : s.pt.right => a ⟶[SSet.{u}] b)
    (rootLabel_target U s hs x) (rootLabel_target U s hs y))

/-- The complete actual original coefficient cocone at the SAME terminal root images. -/
def homCocone : Cocone (homDiagram U x y) where
  pt := s.pt.hom.obj x ⟶[SSet.{u}] s.pt.hom.obj y
  ι := (reindexedHomCocone U s hs x y).ι ≫ (Functor.const J).map (targetHomIso U s hs x y).hom

/-- The genuine full coefficient colimit retains the exact terminal root Hom. -/
def homIsColimit
    (h : ∀ {i j : J} (f : i ⟶ j), Function.Injective (U.map f).right.obj) :
    IsColimit (homCocone U s hs x y) :=
  IsColimit.ofIsoColimit (reindexedHomIsColimit U s hs x y h)
    (Cocone.ext (targetHomIso U s hs x y) (fun _i => rfl))

end CategoryTheory.SimplicialEnrichment.OriginalUnderHomColimit
