/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoefficientGenerators
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoefficientTensor
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedGeneratorEvaluation
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedLimits
import MathlibExt.AlgebraicTopology.ModelCategory.EvaluationTransfer
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentAdjunction
import MathlibExt.CategoryTheory.Enriched.FunctorOpposite

/-!
# The actual coherent-base marked enriched diagram model

The index is the actual original coherent realization of the given
simplicial base, with its opposite variance. Genuine free-source
presentability constructs both small-object arguments in the original
universe. Full evaluated left acyclicity follows from the proved
maximal scalar tensor Quillen law on the actual marked coefficient
model. Native Smith recognition therefore constructs the entire model
and its original objectwise weak/fibration classes, with no model,
factorization or acyclicity outcome supplied as an input.

This is the specific enriched-diagram model needed by native marked
straightening. It does not assert a straightening Quillen equivalence
or higher-height presentation comparison.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra MorphismProperty

namespace SSet.Marked
open CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory coefficientMarkedModelCategory

/-- The literal original free mono family on the actual opposite coherent realization. -/
abbrev coherentDiagramGeneratingMonos (B : SSet.{u}) : MorphismProperty (EnrichedDiagram (realization B)ᵒᵖ) :=
  enrichedFreeGenerators (realization B)ᵒᵖ coefficientGeneratingMonos

/-- The genuine whole free weak-mono family on that same original coherent index. -/
abbrev coherentDiagramGeneratingWeakMonos (B : SSet.{u}) : MorphismProperty (EnrichedDiagram (realization B)ᵒᵖ) :=
  enrichedFreeGenerators (realization B)ᵒᵖ coefficientGeneratingWeakMonos

/-- Original marked coefficient weakness is tested on every actual coherent-realization object and whole
  component map. -/
abbrev coherentDiagramWeakEquivalences (B : SSet.{u}) : MorphismProperty (EnrichedDiagram (realization B)ᵒᵖ) :=
  EvaluationTransfer.evaluationProperty (fun c : (realization B)ᵒᵖ => enrichedDiagramEvaluation _ c)
    (weakEquivalences Marked.{u})

/-- Genuine original-universe source presentability proves the full coherent free-mono small-object argument. -/
theorem coherentDiagramGeneratingMonos_hasSmallObjectArgument (B : SSet.{u}) :
    (coherentDiagramGeneratingMonos B).HasSmallObjectArgument.{u} := by
  let _ : coefficientGeneratingMonos.{u}.IsSmall.{u} := coefficientGeneratingMonos_isSmall
  exact enrichedFreeGenerators_hasSmallObjectArgument (realization B)ᵒᵖ coefficientGeneratingMonos

/-- The same genuine source proof supplies every original coherent free weak-mono cell in the native
  small-object construction. -/
theorem coherentDiagramGeneratingWeakMonos_hasSmallObjectArgument (B : SSet.{u}) :
    (coherentDiagramGeneratingWeakMonos B).HasSmallObjectArgument.{u} := by
  let _ : coefficientGeneratingWeakMonos.{u}.IsSmall.{u} := coefficientGeneratingWeakMonos_isSmall
  exact enrichedFreeGenerators_hasSmallObjectArgument (realization B)ᵒᵖ coefficientGeneratingWeakMonos

/-- The actual full coherent free weak-mono left class is objectwise weak, by original tensor Quillen
  preservation and mapped native cell/retract closure. -/
theorem coherentDiagramGeneratingWeakMonos_left_weak (B : SSet.{u}) :
    (coherentDiagramGeneratingWeakMonos B).rlp.llp ≤ coherentDiagramWeakEquivalences B := by
  let _ : coefficientGeneratingWeakMonos.{u}.IsSmall.{u} := coefficientGeneratingWeakMonos_isSmall
  let _ : (trivialCofibrations Marked.{u}).IsStableUnderCoproducts.{u} :=
    IsStableUnderCoproducts.of_llp_eq _ (fibrations Marked.{u}) (fibrations_llp _)
  let _ : (trivialCofibrations Marked.{u}).IsStableUnderTransfiniteComposition.{u} := by
    rw [← fibrations_llp Marked.{u}]
    infer_instance
  have hTensor : ∀ c x : (realization B)ᵒᵖ, ∀ {A D : Marked.{u}} (f : A ⟶ D),
      coefficientGeneratingWeakMonos f →
        trivialCofibrations Marked.{u} (prodMap (𝟙 (max (c ⟶[SSet.{u}] x))) f) :=
    by
      intro c x A D f hf
      exact coefficientMaxTensor_preserves_trivialCofibrations f
        (coefficientGeneratingWeakMonos_le_trivialCofibrations f hf) _
  intro F G f hf
  apply (EvaluationTransfer.evaluationProperty_iff
    (fun c : (realization B)ᵒᵖ => enrichedDiagramEvaluation _ c) (weakEquivalences Marked.{u}) f).mpr
  intro c
  exact (enrichedFreeGenerators_left_evaluation_le (realization B)ᵒᵖ
    coefficientGeneratingWeakMonos (trivialCofibrations Marked.{u}) hTensor c f hf).2

/-- Both actually constructed WFS and full original class compatibility produce native Smith data for this
  specific coherent-base diagram carrier. -/
def coherentDiagramSmithData (B : SSet.{u}) :
    SmithModelStructureData.{u} (coherentDiagramGeneratingMonos B) (coherentDiagramWeakEquivalences B) := by
  let _ : (coherentDiagramGeneratingMonos B).HasSmallObjectArgument.{u} :=
    coherentDiagramGeneratingMonos_hasSmallObjectArgument B
  let _ : (coherentDiagramGeneratingWeakMonos B).HasSmallObjectArgument.{u} :=
    coherentDiagramGeneratingWeakMonos_hasSmallObjectArgument B
  exact EvaluationTransfer.evaluationRecognitionData.{u}
    (fun c : (realization B)ᵒᵖ => enrichedFreeDiagramFunctor _ c)
    (fun c : (realization B)ᵒᵖ => enrichedDiagramEvaluation _ c)
    (fun c => enrichedFreeEvaluationAdjunction _ c)
    coefficientGeneratingMonos coefficientGeneratingWeakMonos (weakEquivalences Marked.{u})
    coefficientGenerating_right_intersection (coherentDiagramGeneratingWeakMonos_left_weak B)

/-- Native Smith recognition retains exactly the actual original free weak-mono generating family. -/
theorem coherentDiagramSmithData_J (B : SSet.{u}) :
    (coherentDiagramSmithData B).J = coherentDiagramGeneratingWeakMonos B := rfl

/-- All native model axioms hold on the original coherent-base marked enriched diagram carrier, with no new
  global model choice. -/
@[instance_reducible]
def coherentDiagramModelCategory (B : SSet.{u}) : ModelCategory (EnrichedDiagram (realization B)ᵒᵖ) := by
  let _ : HasLimitsOfSize.{u, u} (EnrichedDiagram (realization B)ᵒᵖ) := EnrichedLimit.hasLimits _
  let _ : HasColimitsOfSize.{u, u} (EnrichedDiagram (realization B)ᵒᵖ) := EnrichedColimit.hasColimits _
  let _ : HasFiniteLimits (EnrichedDiagram (realization B)ᵒᵖ) := hasFiniteLimits_of_hasLimitsOfSize _
  let _ : HasFiniteColimits (EnrichedDiagram (realization B)ᵒᵖ) := hasFiniteColimits_of_hasColimitsOfSize _
  let _ : CategoryWithCofibrations (EnrichedDiagram (realization B)ᵒᵖ) :=
    ⟨(coherentDiagramGeneratingMonos B).rlp.llp⟩
  let _ : CategoryWithFibrations (EnrichedDiagram (realization B)ᵒᵖ) :=
    ⟨(coherentDiagramGeneratingWeakMonos B).rlp⟩
  let _ : CategoryWithWeakEquivalences (EnrichedDiagram (realization B)ᵒᵖ) :=
    ⟨coherentDiagramWeakEquivalences B⟩
  exact (coherentDiagramSmithData B).modelCategory
    (EvaluationTransfer.evaluationProperty_hasTwoOutOfThree _ (weakEquivalences Marked.{u})) rfl
      (congrArg MorphismProperty.rlp (coherentDiagramSmithData_J B).symm) rfl

/-- Constructed weak equivalences retain precisely all original marked coefficient weak maps. -/
theorem coherentDiagramModel_weakEquivalences (B : SSet.{u}) :
    let _ := coherentDiagramModelCategory B
    weakEquivalences (EnrichedDiagram (realization B)ᵒᵖ) = coherentDiagramWeakEquivalences B := rfl

/-- The actual projective cofibrations are the whole native free-mono left class, without a converse from
  merely objectwise monos. -/
theorem coherentDiagramModel_cofibrations (B : SSet.{u}) :
    let _ := coherentDiagramModelCategory B
    cofibrations (EnrichedDiagram (realization B)ᵒᵖ) = (coherentDiagramGeneratingMonos B).rlp.llp := rfl

/-- Every original model fibration is exactly a coefficient fibration at each actual coherent-base object. -/
theorem coherentDiagramModel_fibrations (B : SSet.{u}) :
    let _ := coherentDiagramModelCategory B
    fibrations (EnrichedDiagram (realization B)ᵒᵖ) =
      EvaluationTransfer.evaluationProperty (fun c : (realization B)ᵒᵖ => enrichedDiagramEvaluation _ c)
        (fibrations Marked.{u}) := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  change (coherentDiagramGeneratingWeakMonos B).rlp = _
  change (adjointFamilyGenerators (fun c : (realization B)ᵒᵖ => enrichedFreeDiagramFunctor _ c)
    coefficientGeneratingWeakMonos).rlp = _
  rw [EvaluationTransfer.evaluatedGenerators_rlp_eq _ _ (fun c => enrichedFreeEvaluationAdjunction _ c),
    coefficientGeneratingWeakMonos_rlp]

/-- The original trivial-fibration class is exactly coefficient trivial fibrations on every whole marked component. -/
theorem coherentDiagramModel_trivialFibrations (B : SSet.{u}) :
    let _ := coherentDiagramModelCategory B
    trivialFibrations (EnrichedDiagram (realization B)ᵒᵖ) =
      EvaluationTransfer.evaluationProperty (fun c : (realization B)ᵒᵖ => enrichedDiagramEvaluation _ c)
        (trivialFibrations Marked.{u}) := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  rw [trivialFibrations, coherentDiagramModel_fibrations, coherentDiagramModel_weakEquivalences]
  exact (EvaluationTransfer.evaluationProperty_inf _ (fibrations Marked.{u}) (weakEquivalences Marked.{u})).symm

/-- The actual full trivial-cofibration class is precisely the same genuine free weak-mono left class. -/
theorem coherentDiagramModel_trivialCofibrations (B : SSet.{u}) :
    let _ := coherentDiagramModelCategory B
    trivialCofibrations (EnrichedDiagram (realization B)ᵒᵖ) =
      (coherentDiagramGeneratingWeakMonos B).rlp.llp := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  rw [← fibrations_llp (EnrichedDiagram (realization B)ᵒᵖ)]
  rfl

end SSet.Marked
