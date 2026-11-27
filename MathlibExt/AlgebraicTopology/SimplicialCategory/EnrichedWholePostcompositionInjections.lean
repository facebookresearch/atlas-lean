/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.EnrichedHomEqualityTransport

/-!
# Injective whole-map postcomposition from original object and Hom maps

A whole original enriched map with injective object map and monic
full Hom maps reflects equality of whole original functors. The source,
middle and target object universes are independent; no fixed-object
restriction is made.
-/

noncomputable section
universe u v w z
open CategoryTheory

namespace CategoryTheory.EnrichedFunctor

variable {C : Type v} {D : Type w} {E : Type z}
  [EnrichedCategory SSet.{u} C] [EnrichedCategory SSet.{u} D] [EnrichedCategory SSet.{u} E]

/-- Whole original functor postcomposition is injective when the actual object and full Hom
maps are injective. -/
theorem postcomp_injective (F : EnrichedFunctor SSet.{u} D E)
    (hObj : Function.Injective F.obj) (hHom : ∀ x y : D, Mono (F.map x y)) :
    Function.Injective (fun G : EnrichedFunctor SSet.{u} C D =>
      EnrichedFunctor.comp SSet.{u} G F) := by
  intro G H he
  rcases G with ⟨gObj, gMap, gId, gComp⟩
  rcases H with ⟨hObj', hMap, hId, hComp⟩
  have ho : gObj = hObj' := funext (fun x =>
    hObj (congrArg (fun K : EnrichedFunctor SSet.{u} C E => K.obj x) he))
  subst hObj'
  apply EnrichedFunctor.ext SSet.{u} (C := C) (D := D)
    (F := ⟨gObj, gMap, gId, gComp⟩) (G := ⟨gObj, hMap, hId, hComp⟩) (fun _ => rfl)
  intro x y
  have hh := homMap_transport_of_eq he x y
  change (gMap x y ≫ F.map (gObj x) (gObj y)) ≫
    eqToHom (rfl : (F.obj (gObj x) ⟶[SSet.{u}] F.obj (gObj y)) =
      (F.obj (gObj x) ⟶[SSet.{u}] F.obj (gObj y))) =
        hMap x y ≫ F.map (gObj x) (gObj y) at hh
  have h : gMap x y ≫ F.map (gObj x) (gObj y) =
      hMap x y ≫ F.map (gObj x) (gObj y) := by
    simpa only [eqToHom_refl, Category.comp_id] using hh
  let _ := hHom (gObj x) (gObj y)
  simpa only [eqToHom_refl, Category.comp_id] using (cancel_mono _).mp h

end CategoryTheory.EnrichedFunctor
