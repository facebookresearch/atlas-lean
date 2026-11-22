/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFilteredBergnerRootWeak
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalBergnerRootLimitWeak
import MathlibExt.AlgebraicTopology.SimplicialCategory.EnrichedDwyerKanRetracts
import MathlibExt.CategoryTheory.Limits.TransfiniteSourceUnderContinuous
import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition

/-!
# Genuine general transfinite closure of the SAME original C0 and DK weak maps

The actual source-under diagram retains its original well-order colimits.
Limit induction uses the full original filtered root-Hom cocone and genuine
component representatives. Every original successor and root map remains
unchanged. The same supplied transfinite composite is therefore DK weak,
including shapes with a maximum, at independent explicitly small universes.
-/

noncomputable section
universe u v
open CategoryTheory Limits

namespace CategoryTheory.SimplicialEnrichment.Bergner
open EnrichedDwyerKan

variable {J : Type v} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  [UnivLE.{v, u}] {C D : Carrier.{u}} {f : C ⟶ D}

/-- Every SAME original root-to-stage map is weak through genuine original limit induction. -/
theorem transfinite_root_stage_weak
    (h : (cofibrations ⊓ weakEquivalences).TransfiniteCompositionOfShape J f) (j : J) :
    weakEquivalences ((h.toTransfiniteCompositionOfShape.sourceUnderDiagram).obj j).hom := by
  let t := h.toTransfiniteCompositionOfShape
  let U : J ⥤ Under C := t.sourceUnderDiagram
  have hC {i k : J} (g : i ⟶ k) : cofibrations (U.map g).right :=
    (h.ofLE (by intro X Y q hq; exact hq.1)).mem_map g
  induction j using SuccOrder.limitRecOn with
  | isMin j hj =>
    obtain rfl := hj.eq_bot
    exact weakEquivalences.of_isIso (U.obj ⊥).hom
  | succ j hj ih =>
    let g : j ⟶ Order.succ j := homOfLE (Order.le_succ j)
    have he : (U.obj j).hom ≫ (U.map g).right = (U.obj (Order.succ j)).hom := (U.map g).w
    exact he ▸ weakEquivalences.comp_mem _ _ ih (h.map_mem j hj).2
  | isSuccLimit j hj ih =>
    exact OriginalFilteredRoot.weak_at_limit U j hj (fun g => hC g) (fun i hi => ih i hi)

/-- The SAME actual original transfinite C0 and DK weak composite is genuinely DK weak. -/
theorem weak_of_transfinite
    (h : (cofibrations ⊓ weakEquivalences).TransfiniteCompositionOfShape J f) :
    weakEquivalences f := by
  let t := h.toTransfiniteCompositionOfShape
  let U : J ⥤ Under C := t.sourceUnderDiagram
  exact OriginalFilteredRoot.weak_of_cofibrations.{u, v, v} U t.sourceUnderCocone t.sourceUnderIsColimit
    (fun g => (h.ofLE (by intro X Y q hq; exact hq.1)).mem_map g)
      (transfinite_root_stage_weak h)

/-- The SAME original C0 and DK weak intersection is stable under all genuine explicitly small well-order shapes. -/
instance cofibrationWeak_transfinite :
    (cofibrations.{u} ⊓ weakEquivalences).IsStableUnderTransfiniteCompositionOfShape J where
  le X Y f hf := by
    obtain ⟨h⟩ := hf
    exact ⟨cofibrations.transfiniteCompositionsOfShape_le _ _
      (h.ofLE (by intro X Y q hq; exact hq.1)).mem, weak_of_transfinite h⟩

end CategoryTheory.SimplicialEnrichment.Bergner
