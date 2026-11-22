/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeCriticalHornPushout
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeRootBoundaryChart
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentDiagramProjectiveMonomorphisms

/-!
# Actual native weak attachment of the same supported critically marked horn

The genuine full original marked enriched critical horn pushout is
left-extended over its SAME entire original base simplex. Its actual
weak projective left class gives a genuine coherent-model trivial
cofibration on the complete supported critically marked source and
target. Identification with the original native marking pushouts keeps
the original critical edge and remains a separate source construction.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra Opposite
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The same entire original critically marked supported horn is left-extended over its actual unchanged whole
original base simplex. -/
def nativeCriticalSupportedHornChart (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    EnrichedDiagram (realization B)ᵒᵖ :=
  (EnrichedLeftKan.leftExtension (EnrichedFunctor.opposite (simplexInto B σ))).obj (coneCriticalHornDiagram n)

/-- The same whole original critically marked target cone is left-extended over its unchanged original full base
simplex. -/
def nativeCriticalSupportedSimplexChart (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    EnrichedDiagram (realization B)ᵒᵖ :=
  (EnrichedLeftKan.leftExtension (EnrichedFunctor.opposite (simplexInto B σ))).obj (coneCriticalDiagram n)

/-- The same entire original critically marked supported horn attachment retains its complete original source,
target and base maps under actual native left extension. -/
def nativeCriticalSupportedHornChartMap (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    nativeCriticalSupportedHornChart B n σ ⟶ nativeCriticalSupportedSimplexChart B n σ :=
  (EnrichedLeftKan.leftExtension (EnrichedFunctor.opposite (simplexInto B σ))).map (coneCriticalHornInclusion n)

/-- The same full original critical free-root marked attaching square is left-extended over its unchanged whole
original base simplex. -/
def nativeCriticalSupportedHornCocone (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    Cocone ((span (coneCriticalHornCellFreeMap n) (coneCriticalHornFreeLeg n)) ⋙
      EnrichedLeftKan.leftExtension (EnrichedFunctor.opposite (simplexInto B σ))) :=
  (EnrichedLeftKan.leftExtension (EnrichedFunctor.opposite (simplexInto B σ))).mapCocone
    (coneCriticalHornEnrichedCocone n)

/-- The same entire original native critically marked free-root square is genuinely a full marked enriched colimit
over every original base. -/
def nativeCriticalSupportedHornIsColimit (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    IsColimit (nativeCriticalSupportedHornCocone B n σ) := by
  let j := EnrichedFunctor.opposite (simplexInto B σ)
  let L := EnrichedLeftKan.leftExtension j
  let _ : PreservesColimitsOfShape WalkingSpan L :=
    ((EnrichedLeftKan.adjunction j).leftAdjoint_preservesColimits : PreservesColimitsOfSize.{0, 0}
      L).preservesColimitsOfShape
  let h : PreservesColimit (span (coneCriticalHornCellFreeMap n) (coneCriticalHornFreeLeg n)) L :=
    (inferInstance : PreservesColimitsOfShape WalkingSpan L).preservesColimit
  exact (h.preserves (coneCriticalHornEnrichedIsColimit n)).some

/-- The SAME entire original native supported critically marked horn attachment has the genuine weak projective left
class through its actual original full coefficient and enriched pushout. -/
theorem nativeCriticalSupportedHornChartMap_projectiveWeakLeft (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    (enrichedFreeGenerators (realization B)ᵒᵖ coefficientGeneratingWeakMonos).rlp.llp
      (nativeCriticalSupportedHornChartMap B n σ) :=
  enrichedLeftKan_freeLeft (EnrichedFunctor.opposite (simplexInto B σ)) coefficientGeneratingWeakMonos
    (coneCriticalHornInclusion n) (coneCriticalHornInclusion_projectiveWeakLeft n)

/-- The same whole original native supported critically marked horn map is an actual coherent-model trivial
cofibration over every original simplicial base, with no Kan condition. -/
theorem nativeCriticalSupportedHornChartMap_trivialCofibration (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    let _ := coherentDiagramModelCategory B
    trivialCofibrations (EnrichedDiagram (realization B)ᵒᵖ) (nativeCriticalSupportedHornChartMap B n σ) := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  rw [coherentDiagramModel_trivialCofibrations B]
  exact nativeCriticalSupportedHornChartMap_projectiveWeakLeft B n σ

end SSet.Marked
