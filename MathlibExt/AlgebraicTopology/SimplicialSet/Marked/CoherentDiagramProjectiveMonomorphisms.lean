/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentDiagramModel
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedDiagramMonomorphisms

/-!
# Actual coherent projective cofibrations are coefficient monomorphisms

Each original free mono evaluates to its genuine maximal Hom tensor,
which is an actual coefficient cofibration. The original small-object
evaluation and coefficient cell/retract closure therefore prove that
the full projective left class is coefficientwise cofibrant. Exact
coefficient cofibrations and whole component detection then give
monomorphisms of the same original enriched maps.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra MorphismProperty

namespace SSet.Marked
open CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory coefficientMarkedModelCategory

/-- Every actual original coherent projective left map evaluates to a genuine coefficient cofibration. -/
theorem coherentDiagram_projectiveLeft_evaluation_cofibration (B : SSet.{u})
    {F G : EnrichedDiagram (realization B)ᵒᵖ} (f : F ⟶ G)
    (hf : (enrichedFreeGenerators (realization B)ᵒᵖ coefficientGeneratingMonos).rlp.llp f)
    (x : (realization B)ᵒᵖ) : cofibrations Marked.{u} (f.app x) := by
  let _ : coefficientGeneratingMonos.{u}.IsSmall.{u} := coefficientGeneratingMonos_isSmall
  let _ : (cofibrations Marked.{u}).IsStableUnderCoproducts.{u} :=
    IsStableUnderCoproducts.of_llp_eq _ (trivialFibrations Marked.{u}) (trivialFibrations_llp _)
  let _ : (cofibrations Marked.{u}).IsStableUnderTransfiniteComposition.{u} := by
    rw [← trivialFibrations_llp Marked.{u}]
    infer_instance
  have hgen : coefficientGeneratingMonos.{u} ≤ cofibrations Marked.{u} := by
    rw [← trivialFibrations_llp Marked.{u}, ← coefficientGeneratingMonos_rlp]
    exact coefficientGeneratingMonos.le_llp_rlp
  have hTensor : ∀ c y : (realization B)ᵒᵖ, ∀ {A D : Marked.{u}} (g : A ⟶ D),
      coefficientGeneratingMonos g →
        cofibrations Marked.{u} (prodMap (𝟙 (max (c ⟶[SSet.{u}] y))) g) := by
    intro c y A D g hg
    exact coefficientMaxTensor_preserves_cofibrations g (hgen g hg) _
  exact enrichedFreeGenerators_left_evaluation_le (realization B)ᵒᵖ
    coefficientGeneratingMonos (cofibrations Marked.{u}) hTensor x f hf

/-- The same actual whole projective left map is monic on each complete original marked coefficient. -/
theorem coherentDiagram_projectiveLeft_component_mono (B : SSet.{u})
    {F G : EnrichedDiagram (realization B)ᵒᵖ} (f : F ⟶ G)
    (hf : (enrichedFreeGenerators (realization B)ᵒᵖ coefficientGeneratingMonos).rlp.llp f)
    (x : (realization B)ᵒᵖ) : Mono (f.app x) := by
  have h := coherentDiagram_projectiveLeft_evaluation_cofibration B f hf x
  rw [coefficientMarkedCofibrations_eq] at h
  exact h

/-- Actual coefficient monomorphisms detect the unchanged whole coherent projective left map. -/
theorem coherentDiagram_projectiveLeft_mono (B : SSet.{u})
    {F G : EnrichedDiagram (realization B)ᵒᵖ} (f : F ⟶ G)
    (hf : (enrichedFreeGenerators (realization B)ᵒᵖ coefficientGeneratingMonos).rlp.llp f) : Mono f :=
  enrichedDiagramMap_mono_of_components f (coherentDiagram_projectiveLeft_component_mono B f hf)

/-- Every actual cofibration in the original coherent marked model is monic as its same whole enriched map. -/
theorem coherentDiagram_cofibration_mono (B : SSet.{u})
    {F G : EnrichedDiagram (realization B)ᵒᵖ} (f : F ⟶ G) :
    let _ := coherentDiagramModelCategory B
    Cofibration f → Mono f := by
  let _ := coherentDiagramModelCategory B
  change Cofibration f → Mono f
  rw [cofibration_iff, coherentDiagramModel_cofibrations B]
  intro hf
  exact coherentDiagram_projectiveLeft_mono B f hf

end SSet.Marked
