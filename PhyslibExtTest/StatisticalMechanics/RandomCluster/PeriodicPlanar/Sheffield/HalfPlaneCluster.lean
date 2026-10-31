/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.HalfPlaneCluster

/-!
# Tests for `Sheffield.HalfPlaneCluster`

Module under test: `Sheffield.HalfPlaneCluster` in
`PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar`.

* The hypotheses `IsFKG`, translation invariance and almost-sure uniqueness (where present) are
  discharged together by the Dirac mass on the all-open configuration of any connected infinite
  periodic graph (`isFKG_dirac`, `allOpen_translationInvariant`, `allOpen_unique`, proved here).
* `PeriodicGraph.measurableSet_clusterWithinSet_infinite` on the square lattice, and
  `PeriodicGraph.clusterWithinSet` as a vertex set.
* `PeriodicPlaneEmbedding.rightHalfPlaneHasInfiniteCluster_measure_eq_boundary` for the all-open
  Dirac mass with boundaries `r = 0` and `s = 1`.
* `PeriodicPlaneEmbedding.rightHalfPlaneHasInfiniteCluster_measure_eq_zero_or_one` elaborates
  (check-only).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield
namespace HalfPlaneCluster

open _root_.StatMech _root_.StatMech.FK _root_.StatMech.FK.PeriodicPlanar MeasureTheory Filter

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

variable {V : Type*} [DecidableEq V] [Countable V] {P : PeriodicGraph V}

-- The cluster of the origin inside the right half of the square lattice, at the all-open
-- configuration, is a vertex set, and "it is infinite" is measurable.
example : MeasurableSet {omega : ConfigSpace (Sym2 (StatMech.Lattice.Site 2)) |
    (PeriodicPlanar.square.clusterWithinSet omega {z | 0 ≤ z 0} 0).Infinite} :=
  PeriodicPlanar.square.measurableSet_clusterWithinSet_infinite _ 0

-- `clusterWithinSet` at the all-open configuration.
example : Set (StatMech.Lattice.Site 2) :=
  PeriodicPlanar.square.clusterWithinSet allOpen {z | 0 ≤ z 0} 0

-- Half-planes at boundaries `0` and `1` have an infinite cluster with equal probability.
example (E : PeriodicPlaneEmbedding P) :
    Measure.dirac allOpen (E.rightHalfPlaneHasInfiniteCluster 0) =
      Measure.dirac allOpen (E.rightHalfPlaneHasInfiniteCluster 1) :=
  E.rightHalfPlaneHasInfiniteCluster_measure_eq_boundary _ (allOpen_translationInvariant P) 0 1

-- `PeriodicPlaneEmbedding.rightHalfPlaneHasInfiniteCluster_measure_eq_zero_or_one` elaborates.
example := @PeriodicPlaneEmbedding.rightHalfPlaneHasInfiniteCluster_measure_eq_zero_or_one

end HalfPlaneCluster
end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield
