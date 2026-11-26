/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.AdjacentHeight

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.AdjacentHeight`

* The hypotheses `IsFKG`, translation invariance and almost-sure uniqueness (where present) are
  discharged together by the Dirac mass on the all-open configuration of any connected infinite
  periodic graph (`isFKG_dirac`, `allOpen_translationInvariant`, `allOpen_unique`, proved here).
* `PeriodicPlanarDualPair.exists_common_nat_edgeArc_displacement_bound` for an arbitrary dual
  pair.
* `PeriodicPlaneEmbedding.adjacentHeightVerticalCrossing_ge_approxPreferredSide_transfer` and
  `outwardVerticalCrossing_ge_approxPreferredSide_transfer` (unit square, shift `0`, `ε = 0`) and
  `exists_uniformTemplate_outwardBoundaryScores_crossing_max_tendsto_one` (zero pads; the
  template-hit limit stays a hypothesis) applied to that measure.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.AdjacentHeight

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

-- A common natural arc bound for both embeddings of a dual pair.
example (D : PeriodicPlanarDualPair P Pdual) :=
  D.exists_common_nat_edgeArc_displacement_bound

-- The adjacent-height transfer on the unit square with shift `0`.
example (E : PeriodicPlaneEmbedding P) (L R : Finset V) :=
  E.adjacentHeightVerticalCrossing_ge_approxPreferredSide_transfer (Measure.dirac allOpen)
    (isFKG_dirac _) (allOpen_translationInvariant P) 0 1 0 1 0 le_rfl L R 0

-- The outward transfer on the unit square with pad `0`.
example (E : PeriodicPlaneEmbedding P) (L R : Finset V) :=
  E.outwardVerticalCrossing_ge_approxPreferredSide_transfer (Measure.dirac allOpen)
    (isFKG_dirac _) (allOpen_translationInvariant P) 0 1 0 1 0 le_rfl L R 0

-- Outward boundary scores with zero pads.
example [Infinite V] (E : PeriodicPlaneEmbedding P) (hconn : P.graph.Connected)
    (template : ℕ → Finset V)
    (htemplateHit : Tendsto (fun n => (Measure.dirac allOpen).real
      (P.setHitsInfinite (template n : Set V))) atTop (nhds 1)) :=
  E.exists_uniformTemplate_outwardBoundaryScores_crossing_max_tendsto_one (Measure.dirac allOpen)
    (isFKG_dirac _) (allOpen_translationInvariant P) (allOpen_unique P hconn) template
    htemplateHit (fun _ => 0) (fun _ => le_rfl)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.AdjacentHeight
