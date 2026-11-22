/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentDiagramModel
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoefficientIntrinsicFibrancy

/-!
# Actual coherent-model fibrancy retains every original fibrant coefficient

The original projective fibration class is evaluated coefficientwise.
The genuine free/evaluation adjunction shows that its evaluated terminal
object is terminal, so the SAME original coefficient is fibrant. Its
unchanged marking is consequently its exact original equivalence set.
All coherent Hom actions and the original value universe are retained.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra Opposite
open scoped Simplicial

namespace SSet.Marked
open CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory coefficientMarkedModelCategory

/-- Actual projective fibrancy makes every SAME original coefficient fibrant, through the genuine original
free/evaluation adjunction. -/
theorem coherentDiagramCoefficient_isFibrant (B : SSet.{u})
    (F : EnrichedDiagram (realization B)ᵒᵖ) (c : (realization B)ᵒᵖ) :
    let _ := coherentDiagramModelCategory B
    IsFibrant F → IsFibrant (F.obj c) := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hF
  let R := enrichedDiagramEvaluation (realization B)ᵒᵖ c
  let adj := enrichedFreeEvaluationAdjunction (realization B)ᵒᵖ c
  have hf : fibrations Marked.{u} (R.map (terminal.from F)) := by
    have h := (fibration_iff (terminal.from F)).mp hF
    rw [coherentDiagramModel_fibrations B] at h
    exact (EvaluationTransfer.evaluationProperty_iff _ _ _).mp h c
  have ht : IsTerminal (R.obj (⊤_ EnrichedDiagram (realization B)ᵒᵖ)) := by
    refine IsTerminal.ofUniqueHom
      (fun A => (adj.homEquiv A _).toFun (terminal.from _)) ?_
    intro A f
    exact (Equiv.apply_symm_apply (adj.homEquiv A _) f).symm.trans
      (congrArg (adj.homEquiv A _).toFun (Subsingleton.elim _ _))
  exact (isFibrant_iff_of_isTerminal (R.map (terminal.from F)) ht).mpr
    ((fibration_iff _).mpr hf)

/-- Every SAME original coefficient of an actual fibrant coherent diagram is a quasicategory. -/
theorem coherentDiagramCoefficient_quasicategory (B : SSet.{u})
    (F : EnrichedDiagram (realization B)ᵒᵖ) (c : (realization B)ᵒᵖ) :
    let _ := coherentDiagramModelCategory B
    IsFibrant F → Quasicategory (F.obj c).toSSet := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hF
  exact coefficientFibrant_quasicategory _ (coherentDiagramCoefficient_isFibrant B F c hF)

/-- The SAME original coefficient marking of an actual coherent-model fibrant diagram is exactly its original
equivalence-edge set. -/
theorem coherentDiagramCoefficient_marking_iff (B : SSet.{u})
    (F : EnrichedDiagram (realization B)ᵒᵖ) (c : (realization B)ᵒᵖ) :
    let _ := coherentDiagramModelCategory B
    IsFibrant F → ∀ e : (F.obj c).toSSet _⦋1⦌,
      e ∈ (F.obj c).marking ↔ (Edge.mk' e).IsEquivalence := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hF e
  exact coefficientFibrant_marking_iff _ (coherentDiagramCoefficient_isFibrant B F c hF) e

end SSet.Marked
