/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.OpenBoundaryCorridor

/-!
# Tests for `Sheffield.OpenBoundaryCorridor`

Module under test: `Sheffield.OpenBoundaryCorridor` in
`PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar`.

* The hypotheses `IsFKG`, translation invariance and almost-sure uniqueness (where present) are
  discharged together by the Dirac mass on the all-open configuration of any connected infinite
  periodic graph (`isFKG_dirac`, `allOpen_translationInvariant`, `allOpen_unique`, proved here).
* `PeriodicPlaneEmbedding.infiniteOpenLowerBoundaryConnection_tendsto_add` and
  `infiniteOpenUpperBoundaryConnection_tendsto_sub` for the all-open Dirac mass.
* `PeriodicPlaneEmbedding.exists_finite_infiniteOpenBoundaryConnection_gt` (`r = R`, `ε = 1/2`) and
  `exists_finite_opposite_infiniteOpenBoundaryRays_gt` (`c = 0`, `d = 1`) applied to that measure.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield
namespace OpenBoundaryCorridor

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

-- Lower boundary rays exhaust the open boundary connection.
example (E : PeriodicPlaneEmbedding P) (r s : ℝ) (S : Set V) :=
  E.infiniteOpenLowerBoundaryConnection_tendsto_add (Measure.dirac allOpen)
     r s S

-- Upper boundary rays exhaust the open boundary connection.
example (E : PeriodicPlaneEmbedding P) (r s : ℝ) (S : Set V) :=
  E.infiniteOpenUpperBoundaryConnection_tendsto_sub (Measure.dirac allOpen)
     r s S

-- A finite source with probability above `1/2`.
example [Infinite V] (E : PeriodicPlaneEmbedding P) (hconn : P.graph.Connected) (R : ℝ) :=
  E.exists_finite_infiniteOpenBoundaryConnection_gt (Measure.dirac allOpen)
    (isFKG_dirac _) (allOpen_translationInvariant P) (allOpen_unique P hconn)
    (le_refl R) (by norm_num : (0 : ℝ) < 1 / 2)

-- Opposite open boundary rays at `c = 0`, `d = 1`.
example [Infinite V] (E : PeriodicPlaneEmbedding P) (hconn : P.graph.Connected) (R : ℝ) :=
  E.exists_finite_opposite_infiniteOpenBoundaryRays_gt (Measure.dirac allOpen)
    (isFKG_dirac _) (allOpen_translationInvariant P) (allOpen_unique P hconn)
    (c := 0) (d := 1) (le_refl R) (by norm_num : (0 : ℝ) < 1 / 2)

end OpenBoundaryCorridor
end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield
