/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.RectangleLimit

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.RectangleLimit`

* The hypotheses `IsFKG`, translation invariance and almost-sure uniqueness (where present) are
  discharged together by the Dirac mass on the all-open configuration of any connected infinite
  periodic graph (`isFKG_dirac`, `allOpen_translationInvariant`, `allOpen_unique`, proved here).
* `PeriodicGraph.exists_uniform_pairMergeRadius` (one target family, `ι = Fin 1`),
  `PeriodicPlaneEmbedding.exists_uniform_kingOffset_mergeError_tendsto_zero`,
  `exists_uniform_connectorRadius_crossing_max_tendsto_one` and
  `crossing_branch_of_preference_witness` (orbit-box radius `0`, unit square) applied to that
  measure.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.RectangleLimit

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

variable {V : Type*} [DecidableEq V] [Countable V] {P : PeriodicGraph V}

-- Uniform pair-merge radii (a periodic-graph statement).
example [Infinite V] (hconn : P.graph.Connected) (L : ℕ → Finset V)
    (R : ℕ → Fin 1 → Finset V) :=
  P.exists_uniform_pairMergeRadius (Measure.dirac allOpen) (allOpen_unique P hconn) L R

-- King-offset merge errors tend to zero.
example [Infinite V] (E : PeriodicPlaneEmbedding P) (hconn : P.graph.Connected) :=
  E.exists_uniform_kingOffset_mergeError_tendsto_zero (Measure.dirac allOpen)
    (allOpen_translationInvariant P) (allOpen_unique P hconn)

-- A uniform connector radius.
example [Infinite V] (E : PeriodicPlaneEmbedding P) (hconn : P.graph.Connected) :=
  E.exists_uniform_connectorRadius_crossing_max_tendsto_one (Measure.dirac allOpen)
    (isFKG_dirac _) (allOpen_translationInvariant P) (allOpen_unique P hconn)

-- The crossing branch from a preference witness, radius `0`, unit square.
example (E : PeriodicPlaneEmbedding P) (x xV xH : StatMech.Lattice.Site 2) :=
  E.crossing_branch_of_preference_witness (Measure.dirac allOpen)
    (isFKG_dirac _) (allOpen_translationInvariant P) 0 0 1 0 1 x xV xH

end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.RectangleLimit
