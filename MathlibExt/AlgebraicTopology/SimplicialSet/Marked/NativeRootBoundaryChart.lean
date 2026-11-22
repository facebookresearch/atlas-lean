/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootBoundaryPushout
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedLeftKanCofibrations
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeChartWholeOperator

/-!
# The native chart of the actual complete root-boundary diagram

The same original coherent simplex into an arbitrary original base
left-extends the actual supported diagram and its unchanged inclusion.
Its actual adjunction preserves the genuine free-root pushout and
projective left class. This chart has not yet been identified with
straightening of the original simplex boundary.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The actual original supported cone is left-extended over the same whole original base simplex. -/
def nativeRootBoundaryChart (B : SSet.{u}) (n : ℕ) (σ : B _⦋n⦌) :
    EnrichedDiagram (realization B)ᵒᵖ :=
  (EnrichedLeftKan.leftExtension (EnrichedFunctor.opposite (simplexInto B σ))).obj
    (coneRootBoundaryDiagram n)

/-- The actual supported chart enters the original full simplex chart by its unchanged left-extended inclusion. -/
def nativeRootBoundaryChartMap (B : SSet.{u}) (n : ℕ) (σ : B _⦋n⦌) :
    nativeRootBoundaryChart B n σ ⟶ nativeSimplexChart B n σ :=
  (EnrichedLeftKan.leftExtension (EnrichedFunctor.opposite (simplexInto B σ))).map
    (coneRootBoundaryDiagramInclusion n)

/-- The actual native root-boundary square is the same whole original free-cell square left-extended over its actual
base. -/
def nativeRootBoundaryCocone (B : SSet.{u}) (n : ℕ) (σ : B _⦋n⦌) :
    Cocone ((span (coneRootBoundaryCellFreeMap n) (coneRootBoundaryFreeLeg n)) ⋙
      EnrichedLeftKan.leftExtension (EnrichedFunctor.opposite (simplexInto B σ))) :=
  (EnrichedLeftKan.leftExtension (EnrichedFunctor.opposite (simplexInto B σ))).mapCocone
    (coneRootBoundaryEnrichedCocone n)

/-- The complete native root-boundary square is a genuine whole marked enriched colimit over every original base,
without any native latching outcome premise. -/
def nativeRootBoundaryIsColimit (B : SSet.{u}) (n : ℕ) (σ : B _⦋n⦌) :
    IsColimit (nativeRootBoundaryCocone B n σ) := by
  let j := EnrichedFunctor.opposite (simplexInto B σ)
  let L := EnrichedLeftKan.leftExtension j
  let _ : PreservesColimitsOfShape WalkingSpan L :=
    ((EnrichedLeftKan.adjunction j).leftAdjoint_preservesColimits :
      PreservesColimitsOfSize.{0, 0} L).preservesColimitsOfShape
  let hPres : PreservesColimit (span (coneRootBoundaryCellFreeMap n) (coneRootBoundaryFreeLeg n)) L :=
    (inferInstance : PreservesColimitsOfShape WalkingSpan L).preservesColimit
  exact (hPres.preserves (coneRootBoundaryEnrichedIsColimit n)).some

/-- The same actual left-extended supported inclusion has genuine projective left lifting in all dimensions over
arbitrary original non-Kan bases. -/
theorem nativeRootBoundaryChartMap_projectiveLeft (B : SSet.{u}) (n : ℕ) (σ : B _⦋n⦌) :
    (enrichedFreeGenerators (realization B)ᵒᵖ coefficientGeneratingMonos).rlp.llp
      (nativeRootBoundaryChartMap B n σ) :=
  enrichedLeftKan_freeLeft (EnrichedFunctor.opposite (simplexInto B σ)) coefficientGeneratingMonos
    (coneRootBoundaryDiagramInclusion n) (coneRootBoundaryInclusion_projectiveLeft n)

/-- The actual target unit reads the same original supported inclusion under the whole native adjunction. -/
theorem nativeRootBoundaryChartMap_homEquiv (B : SSet.{u}) (n : ℕ) (σ : B _⦋n⦌) :
    EnrichedLeftKan.universalHomEquiv (EnrichedFunctor.opposite (simplexInto B σ))
      (coneRootBoundaryDiagram n) (nativeSimplexChart B n σ) (nativeRootBoundaryChartMap B n σ) =
        coneRootBoundaryDiagramInclusion n ≫
          EnrichedLeftKan.unit (EnrichedFunctor.opposite (simplexInto B σ)) (coneDiagram n) :=
  EnrichedLeftKan.map_homEquiv (EnrichedFunctor.opposite (simplexInto B σ))
    (coneRootBoundaryDiagramInclusion n)

end SSet.Marked
