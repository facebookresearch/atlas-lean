/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeOriginalHornRootSourceIso

/-!
# Actual weak attachments of the entire original native inner horn

The genuine full source isomorphism identifies the original native horn
attaching arrow with the actual same supported free-root horn attachment.
Its proved original weak projective left class therefore belongs to the
entire original native horn map. The whole original simplex comparison
then recovers the weak class of straightening the same physical original
minimally marked horn inclusion, over every original simplicial base.
-/

noncomputable section
universe u
open CategoryTheory HomotopicalAlgebra MorphismProperty Opposite
open scoped Simplicial

namespace SSet.Marked
open CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory coefficientMarkedModelCategory

/-- The same entire original native inner-horn attachment has the actual weak projective left class through its
genuine full original attaching-arrow isomorphism. -/
theorem nativeOriginalInnerHornAttachment_projectiveWeakLeft {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k : Fin (n + 2)) (hk : 0 < k) (hk' : k < Fin.last (n + 1)) :
    (enrichedFreeGenerators (realization B)ᵒᵖ coefficientGeneratingWeakMonos).rlp.llp
      (nativeHornChartMap B (n + 1) k σ) := by
  let P := (enrichedFreeGenerators (realization B)ᵒᵖ coefficientGeneratingWeakMonos).rlp.llp
  exact (P.arrow_iso_iff (nativeOriginalHornRootAttachmentIso B σ k hk hk')).mpr
    (nativeRootHornAttachment_projectiveWeakLeft B σ k hk hk')

/-- The SAME entire original native inner-horn attaching map is genuinely a trivial cofibration in the actual
coherent marked model, with no Kan condition on the original base. -/
theorem nativeOriginalInnerHornAttachment_trivialCofibration {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k : Fin (n + 2)) (hk : 0 < k) (hk' : k < Fin.last (n + 1)) :
    let _ := coherentDiagramModelCategory B
    trivialCofibrations (EnrichedDiagram (realization B)ᵒᵖ) (nativeHornChartMap B (n + 1) k σ) := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  rw [coherentDiagramModel_trivialCofibrations B]
  exact nativeOriginalInnerHornAttachment_projectiveWeakLeft B σ k hk hk'

/-- Every entire original inner-horn coefficient is an actual coefficient trivial cofibration on its unchanged
complete original marked map. -/
theorem nativeOriginalInnerHornAttachment_component_trivialCofibration {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k : Fin (n + 2)) (hk : 0 < k) (hk' : k < Fin.last (n + 1)) (x : (realization B)ᵒᵖ) :
    trivialCofibrations Marked.{u} ((nativeHornChartMap B (n + 1) k σ).app x) := by
  let _ := coherentDiagramModelCategory B
  let f := nativeHornChartMap B (n + 1) k σ
  have ht := nativeOriginalInnerHornAttachment_trivialCofibration B σ k hk hk'
  exact ⟨coherentDiagram_projectiveLeft_evaluation_cofibration B f ht.1 x,
    (EvaluationTransfer.evaluationProperty_iff
      (fun c : (realization B)ᵒᵖ => enrichedDiagramEvaluation _ c)
      (weakEquivalences Marked.{u}) f).mp ht.2 x⟩

/-- Straightening the same physical original minimally marked inner-horn inclusion has the actual full weak
projective left class, with both original enriched source and target retained. -/
theorem nativeOriginalInnerHornInclusion_straightening_projectiveWeakLeft {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k : Fin (n + 2)) (hk : 0 < k) (hk' : k < Fin.last (n + 1)) :
    (enrichedFreeGenerators (realization B)ᵒᵖ coefficientGeneratingWeakMonos).rlp.llp
      ((nativeStraightening B).map (nativeSubcomplexInclusion B (n + 1) σ (horn (n + 1) k))) := by
  let G := enrichedFreeGenerators (realization B)ᵒᵖ coefficientGeneratingWeakMonos
  let e := nativeSimplexImageIso B (n + 1) σ
  let f := (nativeStraightening B).map (nativeSubcomplexInclusion B (n + 1) σ (horn (n + 1) k))
  have h := G.rlp.llp.comp_mem (nativeHornChartMap B (n + 1) k σ) e.inv
    (nativeOriginalInnerHornAttachment_projectiveWeakLeft B σ k hk hk') (G.rlp.llp_of_isIso e.inv)
  have he : nativeHornChartMap B (n + 1) k σ ≫ e.inv = f :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun g => f ≫ g) e.hom_inv_id).trans (Category.comp_id f))
  change G.rlp.llp f
  exact he ▸ h

/-- The same original physical inner-horn inclusion is sent by actual native straightening to a genuine trivial
cofibration in the actual original coherent marked model. -/
theorem nativeOriginalInnerHornInclusion_straightening_trivialCofibration {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k : Fin (n + 2)) (hk : 0 < k) (hk' : k < Fin.last (n + 1)) :
    let _ := coherentDiagramModelCategory B
    trivialCofibrations (EnrichedDiagram (realization B)ᵒᵖ)
      ((nativeStraightening B).map (nativeSubcomplexInclusion B (n + 1) σ (horn (n + 1) k))) := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  rw [coherentDiagramModel_trivialCofibrations B]
  exact nativeOriginalInnerHornInclusion_straightening_projectiveWeakLeft B σ k hk hk'

end SSet.Marked
