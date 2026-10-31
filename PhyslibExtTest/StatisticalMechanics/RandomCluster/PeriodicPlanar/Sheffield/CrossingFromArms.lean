/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.CrossingFromArms

/-!
# Tests for `Sheffield.CrossingFromArms`

Module under test: `Sheffield.CrossingFromArms` in
`PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar`.

* `PeriodicPlaneEmbedding.finiteStripJoinedBoundaryArmEvent_subset_verticalCrossing` with arc
  bound `1` and the explicit gap `c = 0`, `d = 4` (`3 B < d - c`).
* The hypotheses `IsFKG`, translation invariance and almost-sure uniqueness are discharged
  together by the Dirac mass on the all-open configuration of any connected infinite periodic
  graph (`isFKG_dirac`, `allOpen_translationInvariant`, `allOpen_unique`, proved here).
* `PeriodicPlaneEmbedding.exists_cofinal_verticalCrossing_tendsto_one_of_unique` applied to that
  measure with arc bound `1` and `t = 4`.
* `PeriodicPlanarDualPair.exists_cofinal_complementaryDual_verticalCrossing_tendsto_one`
  elaborates (check-only).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield
namespace CrossingFromArms

open _root_.StatMech _root_.StatMech.FK.PeriodicPlanar MeasureTheory

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

-- Joined strip arms give a vertical crossing of the middle third `[4/3, 8/3]`.
example (E : PeriodicPlaneEmbedding P)
    (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ 1)
    (r : ℝ) (n : ℕ) (L R : Finset V) :
    E.finiteStripJoinedBoundaryArmEvent r 0 4 n L R ⊆
      E.verticalCrossingEvent r (r + n) ((2 * 0 + 4) / 3) ((0 + 2 * 4) / 3) :=
  E.finiteStripJoinedBoundaryArmEvent_subset_verticalCrossing hB zero_le_one (by norm_num)

-- Cofinal vertical crossings for the all-open Dirac mass (arc bound `1`, `t = 4`).
example [Infinite V] (E : PeriodicPlaneEmbedding P) (hconn : P.graph.Connected)
    (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (u) (i : Fin 2),
      |E.coordinates (E.edgeArc hxy u - E.vertex x) i| ≤ 1) (r s : ℝ) :=
  E.exists_cofinal_verticalCrossing_tendsto_one_of_unique (Measure.dirac allOpen)
    (isFKG_dirac _) (allOpen_translationInvariant P) (allOpen_unique P hconn) r 1 s zero_le_one
    hB 4 (by norm_num)

open PeriodicPlanarDualPair in
example := @exists_cofinal_complementaryDual_verticalCrossing_tendsto_one

end CrossingFromArms
end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield
