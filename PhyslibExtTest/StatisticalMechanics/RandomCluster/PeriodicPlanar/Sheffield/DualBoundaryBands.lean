/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.DualBoundaryBands

/-!
# Tests for `Sheffield.DualBoundaryBands`

Module under test: `Sheffield.DualBoundaryBands` in
`PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar`.

* The hypotheses `IsFKG`, translation invariance and almost-sure uniqueness (where present) are
  discharged together by the Dirac mass on the all-open configuration of any connected infinite
  periodic graph (`isFKG_dirac`, `allOpen_translationInvariant`, `allOpen_unique`, proved here).
  The primal and dual hypotheses of
  `exists_pairedUniformConnectorRadii_with_commonHalfWidthData` are discharged this way for two
  connected infinite periodic graphs.
* `exists_pairedAlignedMarginSchedule` for arbitrary band families and zero requirements, and
  `exists_pairedMixedBoundaryScores` with both translation-invariance hypotheses discharged.
* `PeriodicPlanarDualPair.exists_canonicalConnectorReadyData_of_common` elaborates (check-only).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield
namespace DualBoundaryBands

open _root_.StatMech _root_.StatMech.FK.PeriodicPlanar MeasureTheory Filter

/-- The all-open bond configuration. -/
def allOpen {V : Type*} : ConfigSpace (Sym2 V) := fun _ => true

/-- Every Dirac mass on bond configurations is FKG. -/
theorem isFKG_dirac {V : Type*} (ω : ConfigSpace (Sym2 V)) : IsFKG (Measure.dirac ω) := by
  intro A B hA hB _ _
  rw [Measure.real, Measure.real, Measure.real, Measure.dirac_apply' _ hA,
    Measure.dirac_apply' _ hB, Measure.dirac_apply' _ (hA.inter hB)]
  by_cases hωA : ω ∈ A <;> by_cases hωB : ω ∈ B <;> simp [hωA, hωB]

/-- The Dirac mass on the all-open configuration is translation invariant. -/
theorem allOpen_translationInvariant {V : Type*} [DecidableEq V] (P : PeriodicGraph V) :
    P.IsTranslationInvariant (Measure.dirac allOpen) := fun z =>
  ⟨P.measurable_configTranslate z, by
    rw [Measure.map_dirac' (P.measurable_configTranslate z)]
    rfl⟩

/-- On a connected infinite periodic graph, the all-open configuration has a unique infinite
cluster, so its Dirac mass gives the uniqueness event probability one. -/
theorem allOpen_unique {V : Type*} [DecidableEq V] [Infinite V] (P : PeriodicGraph V)
    (hconn : P.graph.Connected) :
    Measure.dirac allOpen {ω | P.HasUniqueInfiniteCluster ω} = 1 := by
  have hG : P.openSubgraph allOpen = P.graph := by
    ext x y
    simp [PeriodicGraph.openSubgraph, allOpen]
  have hcl : ∀ x, P.cluster allOpen x = Set.univ := fun x => by
    ext y
    simp only [PeriodicGraph.cluster, hG, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact hconn.preconnected x y
  refine Measure.dirac_apply_of_mem ⟨⟨hconn.nonempty.some, ?_⟩, fun x y _ _ => ?_⟩
  · rw [hcl]
    exact Set.infinite_univ
  · rw [hG]
    exact hconn.preconnected x y

variable {V W : Type*} [DecidableEq V] [DecidableEq W] [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

-- Paired connector radii with common half-width data for the all-open Dirac masses.
example [Infinite V] [Infinite W] (E : PeriodicPlaneEmbedding P)
    (Edual : PeriodicPlaneEmbedding Pdual) (hconn : P.graph.Connected)
    (hconnDual : Pdual.graph.Connected) :=
  exists_pairedUniformConnectorRadii_with_commonHalfWidthData E Edual (Measure.dirac allOpen)
    (Measure.dirac allOpen) (isFKG_dirac _) (allOpen_translationInvariant P)
    (allOpen_unique P hconn) (isFKG_dirac _) (allOpen_translationInvariant Pdual)
    (allOpen_unique Pdual hconnDual)

-- A paired margin schedule with zero requirements.
example (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    {mu : Measure (ConfigSpace (Sym2 V))} {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : ℝ}
    (family : E.NormalBoundaryBandFamily mu S p)
    (familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual) :=
  exists_pairedAlignedMarginSchedule E Edual family familyDual (fun _ => 0) (fun _ => 0)

-- Paired mixed boundary scores for the all-open Dirac masses.
example (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    {S : Finset V} {Sdual : Finset W} {p pDual : ℝ}
    (family : E.NormalBoundaryBandFamily (Measure.dirac allOpen) S p)
    (familyDual : Edual.NormalBoundaryBandFamily (Measure.dirac allOpen) Sdual pDual)
    (vr hr : ℕ → ℕ) (schedule : PairedAlignedMarginSchedule E Edual family familyDual vr hr) :=
  exists_pairedMixedBoundaryScores E Edual _ _ (allOpen_translationInvariant P)
    (allOpen_translationInvariant Pdual) family familyDual schedule

open PeriodicPlanarDualPair in
example := @exists_canonicalConnectorReadyData_of_common

end DualBoundaryBands
end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield
