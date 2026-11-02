/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.NormalRotatedSlack

/-!
# Tests for `Sheffield.NormalRotatedSlack`

Module under test: `Sheffield.NormalRotatedSlack` in
`PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar`.

* The primal and dual hypotheses (`IsFKG`, translation invariance, almost-sure uniqueness) of
  `nonempty_normalRotatedInsetLimitData_of_unique` are discharged by the Dirac masses on the
  all-open configurations of two connected infinite periodic graphs (`isFKG_dirac`,
  `allOpen_translationInvariant`, `allOpen_unique`, proved here), giving limit data with padding
  `0`; `NormalRotatedInsetLimitData.exists_primalDualFixedBranchesSubsequence` is applied to it.
* `PeriodicPlaneEmbedding.exists_uniformOrbitBoxMixedRadius_alignedExact_dualLimit` with the dual
  hypotheses discharged the same way.
* `exists_pairedAlignedNormalRotatedConnectorSlack` elaborates (check-only).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield
namespace NormalRotatedSlack

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

-- Normal/rotated inset limit data exist for the all-open Dirac masses.
example [Infinite V] [Infinite W] (E : PeriodicPlaneEmbedding P)
    (Edual : PeriodicPlaneEmbedding Pdual) (hconn : P.graph.Connected)
    (hconnDual : Pdual.graph.Connected) :
    Nonempty (NormalRotatedInsetLimitData E Edual (Measure.dirac allOpen)
      (Measure.dirac allOpen) 0) :=
  nonempty_normalRotatedInsetLimitData_of_unique E Edual _ _ (isFKG_dirac _)
    (allOpen_translationInvariant P) (allOpen_unique P hconn) (isFKG_dirac _)
    (allOpen_translationInvariant Pdual) (allOpen_unique Pdual hconnDual) 0

-- A subsequence with fixed primal and dual branches for any such data.
example (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (data : NormalRotatedInsetLimitData E Edual (Measure.dirac allOpen)
      (Measure.dirac allOpen) 0) :=
  data.exists_primalDualFixedBranchesSubsequence

-- The dual limit along exact-extent grids, dual hypotheses discharged.
example [Infinite W] (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (hconnDual : Pdual.graph.Connected) :=
  E.exists_uniformOrbitBoxMixedRadius_alignedExact_dualLimit Edual (Measure.dirac allOpen)
    (Measure.dirac allOpen) (isFKG_dirac _) (allOpen_translationInvariant Pdual)
    (allOpen_unique Pdual hconnDual)

-- `exists_pairedAlignedNormalRotatedConnectorSlack` elaborates.
example := @exists_pairedAlignedNormalRotatedConnectorSlack

end NormalRotatedSlack
end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield
