/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalEquivalenceCountableIntervalReadback

/-!
# Literal original reindexed projection and core coefficient readbacks

The actual fixed-core inclusion fixes the SAME labels and retains its
entire original Hom subcomplex inclusion. Reindexed full projection
composes each original fixed Hom map with precisely the proved endpoint
equality. These actual maps preserve the original independent target
universe and provide direct original coefficient readbacks.
-/

noncomputable section
universe u v
open CategoryTheory MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.SimplicialEnrichment.ComponentEquivalenceCore
open FixedObjects
variable (C : Carrier.{u})

/-- The SAME actual full core inclusion is an original fixed-label map on exactly those original vertices. -/
def fixedInclusion : fixedTarget C ⟶ CarrierReindexing.source C :=
  ⟨inclusion C, by
    apply IsHomLift.of_fac' forgetObjects (𝟙 (C : Type u)) (inclusion C)
      (fixedTarget C).property (CarrierReindexing.source C).property
    rfl⟩

/-- Every full original fixed-core Hom map is the SAME original Hom subcomplex inclusion. -/
theorem fixedInclusion_hom (x y : C) :
    homMap (fixedInclusion C) x y = inclusionHom C x y := by
  change inclusionHom C x y ≫ eqToHom _ = inclusionHom C x y
  exact Category.comp_id _

end CategoryTheory.SimplicialEnrichment.ComponentEquivalenceCore

namespace CategoryTheory.SimplicialEnrichment.OriginalEquivalenceTwoLabelReindexing
open FixedObjects OriginalWalkingArrowFreeSingleHomIso
variable {C : Type v} [EnrichedCategory SSet.{u} C] (a : walking.{u} → C)

/-- The SAME original enrichment placed over its literal original two labels. -/
abbrev fixedTarget : FixedObjects walking.{u} := ⟨object a, rfl⟩

/-- Every complete original projection of a fixed-label map retains the SAME Hom map with its exact endpoint transport.
-/
theorem projected_hom {H : FixedObjects walking.{u}} (F : H ⟶ fixedTarget a)
    (x y : walking.{u}) :
    (EnrichedFunctor.comp SSet.{u} F.val (projection a)).map (vertex H x) (vertex H y) ≫
      eqToHom (congrArg₂ (fun s t : C => s ⟶[SSet.{u}] t)
        (congrArg a (map_vertex F x)) (congrArg a (map_vertex F y))) =
      homMap F x y := by
  change (F.val.map (vertex H x) (vertex H y) ≫ 𝟙 _) ≫ eqToHom _ =
    F.val.map (vertex H x) (vertex H y) ≫ eqToHom _
  simp only [Category.comp_id]

end CategoryTheory.SimplicialEnrichment.OriginalEquivalenceTwoLabelReindexing
