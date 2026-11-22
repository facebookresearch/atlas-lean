/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeOriginalCriticalAttachmentIso

/-!
# Actual weak image of the SAME ORIGINAL critically marked horn cell

The genuine full marked attaching Arrow Iso retains both original
physical native source and target and their actual complete maps.
The proved supported critical weak attachment therefore transfers to
straightening the SAME original critically marked terminal horn over
every whole original base map, with no Kan hypothesis on that base.
-/

noncomputable section
universe u
open CategoryTheory HomotopicalAlgebra MorphismProperty Opposite
open scoped Simplicial

namespace SSet.Marked
open CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory coefficientMarkedModelCategory

/-- The SAME physical ORIGINAL critical marked horn cell has its actual native weak projective left class through
the genuine full marked attaching Arrow Iso. -/
theorem nativeOriginalCriticalCell_straightening_projectiveWeakLeft (B : SSet.{u}) (n : ℕ)
    (r : cartesianCriticalTarget n ⟶ max B) :
    (enrichedFreeGenerators (realization B)ᵒᵖ coefficientGeneratingWeakMonos).rlp.llp
      ((nativeStraightening B).map (cartesianCriticalOver n r)) := by
  let P := (enrichedFreeGenerators (realization B)ᵒᵖ coefficientGeneratingWeakMonos).rlp.llp
  exact (P.arrow_iso_iff (nativeOriginalCriticalAttachmentIso B n r)).mpr
    (nativeCriticalSupportedHornChartMap_projectiveWeakLeft B n (SSet.yonedaEquiv r.hom))

/-- Straightening the SAME entire ORIGINAL critical marked terminal horn is genuinely a trivial cofibration in the
actual coherent marked model over every arbitrary original base. -/
theorem nativeOriginalCriticalCell_straightening_trivialCofibration (B : SSet.{u}) (n : ℕ)
    (r : cartesianCriticalTarget n ⟶ max B) :
    let _ := coherentDiagramModelCategory B
    trivialCofibrations (EnrichedDiagram (realization B)ᵒᵖ)
      ((nativeStraightening B).map (cartesianCriticalOver n r)) := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  rw [coherentDiagramModel_trivialCofibrations B]
  exact nativeOriginalCriticalCell_straightening_projectiveWeakLeft B n r

/-- Every original complete native coefficient of the SAME physical critical cell is an actual coefficient trivial
cofibration. -/
theorem nativeOriginalCriticalCell_straightening_component_trivialCofibration (B : SSet.{u}) (n : ℕ)
    (r : cartesianCriticalTarget n ⟶ max B) (x : (realization B)ᵒᵖ) :
    trivialCofibrations Marked.{u} (((nativeStraightening B).map (cartesianCriticalOver n r)).app x) := by
  let _ := coherentDiagramModelCategory B
  let f := (nativeStraightening B).map (cartesianCriticalOver n r)
  have ht := nativeOriginalCriticalCell_straightening_trivialCofibration B n r
  exact ⟨coherentDiagram_projectiveLeft_evaluation_cofibration B f ht.1 x,
    (EvaluationTransfer.evaluationProperty_iff
      (fun c : (realization B)ᵒᵖ => enrichedDiagramEvaluation _ c) (weakEquivalences Marked.{u}) f).mp ht.2 x⟩

end SSet.Marked
