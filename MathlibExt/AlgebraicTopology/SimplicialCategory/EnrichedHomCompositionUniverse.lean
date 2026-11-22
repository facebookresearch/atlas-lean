/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.EnrichedHomCompositionWeak
import MathlibExt.AlgebraicTopology.SimplicialCategory.ComponentCategoryReindexing

/-!
# Full original Hom-family weakness with independent object universes

Restrict only the proof to three labelled original objects, by the
literal original Hom reindexing. Every coefficient, unit and composition
is unchanged. The proved matching-universe replacement comparison thus
detects the SAME entire original family in an arbitrary object universe.
No Kan condition on the original Homs or comparison outcome is assumed.
-/

noncomputable section
universe u v
open CategoryTheory MonoidalCategory

namespace CategoryTheory.SimplicialEnrichment.EnrichedHomCompositionFamilies

variable (C : Type v) [EnrichedCategory SSet.{u} C]

/-- The three supplied original objects, retained as separate labels even if some coincide. -/
def threeObjectLabels (z x y : C) (i : ULift.{u} (Fin 3)) : C :=
  Fin.cases z (Fin.cases x (fun _ => y)) i.down

/-- Every original full Hom composition graph is weak for groupoid
components, with independent object and coefficient universes and no Kan premise. -/
theorem postGraph_weak_universe [IsGroupoid (ComponentCategory.objects.{u} C)] (z x y : C) :
    SSet.realizationWeakEquivalences (postGraph z x y) := by
  let a := threeObjectLabels C z x y
  let _ : EnrichedCategory SSet.{u} (ULift.{u} (Fin 3)) := EnrichedCategory.reindex SSet.{u} a
  let _ : IsGroupoid (ComponentCategory.objects.{u} (ULift.{u} (Fin 3))) :=
    ComponentCategory.reindex_isGroupoid a
  exact postGraph_weak (ULift.{u} (Fin 3)) (ULift.up 0) (ULift.up 1) (ULift.up 2)

/-- The SAME original full composition graph at arbitrary individual
objects is retained in the literal three-label proof boundary. -/
lemma threeObject_postGraph (z x y : C) :
    let _ : EnrichedCategory SSet.{u} (ULift.{u} (Fin 3)) :=
      EnrichedCategory.reindex SSet.{u} (threeObjectLabels C z x y)
    postGraph (ULift.up (0 : Fin 3)) (ULift.up (1 : Fin 3)) (ULift.up (2 : Fin 3)) =
      postGraph z x y := rfl

end CategoryTheory.SimplicialEnrichment.EnrichedHomCompositionFamilies
