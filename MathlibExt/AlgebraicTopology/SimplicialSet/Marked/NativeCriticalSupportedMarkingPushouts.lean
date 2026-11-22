/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeCriticalWholeEdgeMarkingPushouts
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeCriticalMarkedHornPushout
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativePositiveHornSourceIso

/-!
# The same full critical interval marking pushouts over every original base simplex

Actual enriched left extension along the supplied whole original base
simplex preserves both entire interval marking pushouts. Their points
are exactly the critically marked native supported horn and simplex,
retaining every original edge operator and the same attaching map.
No original physical source or target identification is assumed here.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The full original minimal critical interval chart extended along the SAME original base simplex. -/
def nativeCriticalMinimalEdgeChart (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    EnrichedDiagram (realization B)ᵒᵖ :=
  EnrichedLeftKan.object (EnrichedFunctor.opposite (simplexInto B σ)) (coneCriticalEdgeMinimalChart n)

/-- The full original sharp critical interval chart over precisely that SAME original base simplex. -/
def nativeCriticalSharpEdgeChart (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    EnrichedDiagram (realization B)ᵒᵖ :=
  EnrichedLeftKan.object (EnrichedFunctor.opposite (simplexInto B σ)) (coneCriticalEdgeSharpChart n)

/-- The exact full original critical interval marking chart map after actual native extension. -/
def nativeCriticalEdgeMarkingChartMap (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    nativeCriticalMinimalEdgeChart B n σ ⟶ nativeCriticalSharpEdgeChart B n σ :=
  (EnrichedLeftKan.leftExtension (EnrichedFunctor.opposite (simplexInto B σ))).map (coneCriticalEdgeMarkingChartMap n)

/-- The SAME full original minimal critical interval enters the whole native simplex by its actual original operator
mate. -/
def nativeCriticalConeEdgeMap (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    nativeCriticalMinimalEdgeChart B n σ ⟶ nativeSimplexChart B (n + 2) σ :=
  (EnrichedLeftKan.leftExtension (EnrichedFunctor.opposite (simplexInto B σ))).map (coneCriticalConeEdgeMap n)

/-- The SAME entire original sharp critical interval enters the critically marked native simplex. -/
def nativeCriticalConeSharpEdgeMap (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    nativeCriticalSharpEdgeChart B n σ ⟶ nativeCriticalSupportedSimplexChart B n σ :=
  (EnrichedLeftKan.leftExtension (EnrichedFunctor.opposite (simplexInto B σ))).map (coneCriticalConeSharpEdgeMap n)

/-- The full original simplex marking map keeps the SAME critically marked native target. -/
def nativeCriticalSimplexMarkingChartMap (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    nativeSimplexChart B (n + 2) σ ⟶ nativeCriticalSupportedSimplexChart B n σ :=
  (EnrichedLeftKan.leftExtension (EnrichedFunctor.opposite (simplexInto B σ))).map (coneCriticalDiagramMark n)

/-- The SAME whole original minimal critical interval enters the entire original native supported terminal horn. -/
def nativeCriticalHornEdgeMap (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    nativeCriticalMinimalEdgeChart B n σ ⟶ nativeSupportedRootHornChart B σ (Fin.last (n + 2)) :=
  (EnrichedLeftKan.leftExtension (EnrichedFunctor.opposite (simplexInto B σ))).map (coneCriticalHornEdgeMap n)

/-- The whole original sharp critical interval enters the SAME critically marked native supported horn. -/
def nativeCriticalHornSharpEdgeMap (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    nativeCriticalSharpEdgeChart B n σ ⟶ nativeCriticalSupportedHornChart B n σ :=
  (EnrichedLeftKan.leftExtension (EnrichedFunctor.opposite (simplexInto B σ))).map (coneCriticalHornSharpEdgeMap n)

/-- The entire original supported terminal horn gains its SAME original critical marking under actual native
extension. -/
def nativeCriticalHornMarkingChartMap (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    nativeSupportedRootHornChart B σ (Fin.last (n + 2)) ⟶ nativeCriticalSupportedHornChart B n σ :=
  (EnrichedLeftKan.leftExtension (EnrichedFunctor.opposite (simplexInto B σ))).map (coneCriticalHornDiagramMark n)

/-- The original whole simplex marking square remains its SAME native interval marking square. -/
theorem nativeCriticalConeEdgeMarking_condition (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    nativeCriticalEdgeMarkingChartMap B n σ ≫ nativeCriticalConeSharpEdgeMap B n σ =
      nativeCriticalConeEdgeMap B n σ ≫ nativeCriticalSimplexMarkingChartMap B n σ := by
  let L := EnrichedLeftKan.leftExtension (EnrichedFunctor.opposite (simplexInto B σ))
  exact (L.map_comp _ _).symm.trans
    ((congrArg L.map (coneCriticalConeEdgeMarking_condition n)).trans (L.map_comp _ _))

/-- The SAME original whole horn marking square keeps precisely its actual native interval marking maps. -/
theorem nativeCriticalHornEdgeMarking_condition (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    nativeCriticalEdgeMarkingChartMap B n σ ≫ nativeCriticalHornSharpEdgeMap B n σ =
      nativeCriticalHornEdgeMap B n σ ≫ nativeCriticalHornMarkingChartMap B n σ := by
  let L := EnrichedLeftKan.leftExtension (EnrichedFunctor.opposite (simplexInto B σ))
  exact (L.map_comp _ _).symm.trans
    ((congrArg L.map (coneCriticalHornEdgeMarking_condition n)).trans (L.map_comp _ _))

/-- The entire critically marked native supported simplex is the actual pushout of the SAME full original interval
marking chart. -/
theorem nativeCriticalWholeConeEdgeMarking_isPushout (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    IsPushout (nativeCriticalEdgeMarkingChartMap B n σ) (nativeCriticalConeEdgeMap B n σ)
      (nativeCriticalConeSharpEdgeMap B n σ) (nativeCriticalSimplexMarkingChartMap B n σ) := by
  let j := EnrichedFunctor.opposite (simplexInto B σ)
  let L := EnrichedLeftKan.leftExtension j
  let _ : PreservesColimitsOfSize.{u, u} L := (EnrichedLeftKan.adjunction j).leftAdjoint_preservesColimits
  exact (coneCriticalWholeConeEdgeMarking_isPushout n).map L

/-- The SAME entire critically marked native supported horn is its genuine full original interval chart marking
pushout. -/
theorem nativeCriticalWholeHornEdgeMarking_isPushout (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    IsPushout (nativeCriticalEdgeMarkingChartMap B n σ) (nativeCriticalHornEdgeMap B n σ)
      (nativeCriticalHornSharpEdgeMap B n σ) (nativeCriticalHornMarkingChartMap B n σ) := by
  let j := EnrichedFunctor.opposite (simplexInto B σ)
  let L := EnrichedLeftKan.leftExtension j
  let _ : PreservesColimitsOfSize.{u, u} L := (EnrichedLeftKan.adjunction j).leftAdjoint_preservesColimits
  exact (coneCriticalWholeHornEdgeMarking_isPushout n).map L

/-- The critically marked native simplex retains the complete SAME original interval marking cocone. -/
def nativeCriticalWholeConeEdgeMarkingCocone (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    PushoutCocone (nativeCriticalEdgeMarkingChartMap B n σ) (nativeCriticalConeEdgeMap B n σ) :=
  PushoutCocone.mk (nativeCriticalConeSharpEdgeMap B n σ) (nativeCriticalSimplexMarkingChartMap B n σ)
    (nativeCriticalConeEdgeMarking_condition B n σ)

/-- The SAME complete critically marked native simplex cocone is its actual full colimit. -/
def nativeCriticalWholeConeEdgeMarkingIsColimit (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    IsColimit (nativeCriticalWholeConeEdgeMarkingCocone B n σ) :=
  (nativeCriticalWholeConeEdgeMarking_isPushout B n σ).isColimit

/-- The SAME whole critically marked native horn keeps its complete original interval marking cocone. -/
def nativeCriticalWholeHornEdgeMarkingCocone (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    PushoutCocone (nativeCriticalEdgeMarkingChartMap B n σ) (nativeCriticalHornEdgeMap B n σ) :=
  PushoutCocone.mk (nativeCriticalHornSharpEdgeMap B n σ) (nativeCriticalHornMarkingChartMap B n σ)
    (nativeCriticalHornEdgeMarking_condition B n σ)

/-- The entire SAME critically marked native horn cocone is its genuine full enriched colimit. -/
def nativeCriticalWholeHornEdgeMarkingIsColimit (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    IsColimit (nativeCriticalWholeHornEdgeMarkingCocone B n σ) :=
  (nativeCriticalWholeHornEdgeMarking_isPushout B n σ).isColimit

end SSet.Marked
