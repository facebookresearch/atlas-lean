/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedColimits
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedFreeEvaluation
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.LocallyPresentable
import Mathlib.CategoryTheory.Presentable.Adjunction

/-!
# Native marked enriched evaluation and genuine free-source presentability

Every original marked evaluated colimit is precisely the value of the
constructed pointwise enriched colimit, with the same injection maps.
Thus evaluation preserves colimits at the unchanged coefficient size.
The actual free/evaluation adjunction transports genuine presentability
of marked sources to the native enriched free sources. These are
source-smallness proofs, not model or factorization outcomes.
-/

noncomputable section
universe u v
open CategoryTheory Limits Opposite

namespace SSet.Marked

attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

variable (C : Type v) [EnrichedCategory SSet.{u} C]

/-- Every entire native enriched pointwise colimit keeps the original marked colimit at evaluation. -/
theorem enrichedEvaluation_preservesColimit (x : C) {J : Type u} [Category.{u} J]
    (K : J ⥤ EnrichedDiagram C) : PreservesColimit K (enrichedDiagramEvaluation C x) := by
  let _ (y : C) : HasColimit (EnrichedColimit.evaluated K y) := inferInstance
  exact preservesColimit_of_preserves_colimit_cocone (EnrichedColimit.isColimit K)
    (colimit.isColimit (EnrichedColimit.evaluated K x))

/-- The native evaluation preserves all original coefficient-sized colimits, with no source-object size restriction. -/
theorem enrichedEvaluation_preservesColimits (x : C) :
    PreservesColimitsOfSize.{u, u} (enrichedDiagramEvaluation C x) where
  preservesColimitsOfShape := { preservesColimit := fun {K} => enrichedEvaluation_preservesColimit C x K }

/-- Every actual native free marked enriched source is genuinely presentable in the original coefficient universe. -/
theorem enrichedFree_isPresentable (c : C) (A : Marked.{u}) :
    IsPresentable.{u} (enrichedFreeDiagram C c A) := by
  let _ : IsLocallyPresentable.{u} Marked.{u} := isLocallyPresentable
  obtain ⟨κ, hκ, hA⟩ := (inferInstance : IsPresentable.{u} A).exists_cardinal
  let _ : Fact κ.IsRegular := hκ
  let _ : IsCardinalPresentable A κ := hA
  let _ : PreservesColimitsOfSize.{u, u} (enrichedDiagramEvaluation C c) :=
    enrichedEvaluation_preservesColimits C c
  let _ : (enrichedDiagramEvaluation C c).IsCardinalAccessible κ := inferInstance
  let _ : IsCardinalPresentable (enrichedFreeDiagram C c A) κ :=
    (enrichedFreeEvaluationAdjunction C c).isCardinalPresentable_leftAdjoint_obj κ A
  exact isPresentable_of_isCardinalPresentable _ κ

end SSet.Marked
