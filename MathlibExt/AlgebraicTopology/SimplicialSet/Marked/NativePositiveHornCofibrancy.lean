/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootHornCofibrancy
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeOriginalHornRootSourceIso

/-!
# Original supported native horn cofibrations and whole comparison monicity

The same original free-root marked mono class left-extends over the
whole unchanged original base simplex. The original supported horn
attachment is therefore projectively left at every omitted coordinate,
including the terminal coordinate. Its full original attaching
factorization gives monicity of the native support comparison with the
same full original boundary. These are cofibration statements.
-/

noncomputable section
universe u
open CategoryTheory HomotopicalAlgebra Opposite
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The same entire original supported native horn attachment has the actual full projective mono left class for
every original omitted coordinate and arbitrary original base. -/
theorem nativeSupportedRootHornChartMap_projectiveLeft {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k : Fin (n + 2)) :
    (enrichedFreeGenerators (realization B)ᵒᵖ coefficientGeneratingMonos).rlp.llp
      (nativeSupportedRootHornChartMap B σ k) :=
  enrichedLeftKan_freeLeft (EnrichedFunctor.opposite (simplexInto B σ)) coefficientGeneratingMonos
    (coneRootHornDiagramInclusion k) (coneRootHornInclusion_projectiveLeft k)

/-- Every same entire original supported native horn map is genuinely monic through its actual projective mono class. -/
theorem nativeSupportedRootHornChartMap_mono_all {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k : Fin (n + 2)) : Mono (nativeSupportedRootHornChartMap B σ k) :=
  coherentDiagram_projectiveLeft_mono B _ (nativeSupportedRootHornChartMap_projectiveLeft B σ k)

/-- The same entire original supported horn comparison with the full native boundary is monic at every original
omitted coordinate, through its actual unchanged whole attaching factorization. -/
theorem nativeSupportedRootHornToBoundary_mono_all {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k : Fin (n + 2)) : Mono (nativeSupportedRootHornToBoundary B σ k) := by
  let _ : Mono (nativeSupportedRootHornChartMap B σ k) := nativeSupportedRootHornChartMap_mono_all B σ k
  exact mono_of_mono_fac (nativeSupportedRootHornToBoundary_attachment B σ k)

/-- Every entire original supported native horn coefficient is genuinely monic on its same full marked carrier,
including the original terminal coordinate. -/
theorem nativeSupportedRootHornChartMap_component_mono_all {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k : Fin (n + 2)) (x : (realization B)ᵒᵖ) : Mono ((nativeSupportedRootHornChartMap B σ k).app x) :=
  coherentDiagram_projectiveLeft_component_mono B _ (nativeSupportedRootHornChartMap_projectiveLeft B σ k) x

/-- Every whole original supported horn-to-boundary coefficient is monic by its same actual complete native
attaching factorization. -/
theorem nativeSupportedRootHornToBoundary_component_mono_all {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k : Fin (n + 2)) (x : (realization B)ᵒᵖ) : Mono ((nativeSupportedRootHornToBoundary B σ k).app x) := by
  let _ : Mono ((nativeSupportedRootHornChartMap B σ k).app x) := nativeSupportedRootHornChartMap_component_mono_all
    B σ k x
  exact mono_of_mono_fac (congrArg (fun f => f.app x) (nativeSupportedRootHornToBoundary_attachment B σ k))

end SSet.Marked
