/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.OpenBoundarySource

/-!
# Tests for `Sheffield.OpenBoundarySource`

Module under test: `Sheffield.OpenBoundarySource` in
`PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar`.

* The hypotheses `IsFKG`, translation invariance and almost-sure uniqueness (where present) are
  discharged together by the Dirac mass on the all-open configuration of any connected infinite
  periodic graph (`isFKG_dirac`, `allOpen_translationInvariant`, `allOpen_unique`, proved here).
* `PeriodicPlaneEmbedding.infiniteOpenBoundaryConnection_measureReal_ge_sq_of_translate`,
  `exists_infiniteOpenBoundaryConnection_sequence_tendsto_one` and
  `exists_infiniteOpenBoundaryRay_max_sequence_tendsto_one` (rays at height `0`) applied to that
  measure.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield
namespace OpenBoundarySource

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

-- The squared hitting bound for a source and its translate.
example [Infinite V] (E : PeriodicPlaneEmbedding P) (hconn : P.graph.Connected)
    (r : ℝ) (S : Set V)
    (z : StatMech.Lattice.Site 2) (hS : S ⊆ E.rightHalfPlaneVertices r)
    (hT : P.shift z '' S ⊆ (E.rightHalfPlaneVertices r)ᶜ) :=
  E.infiniteOpenBoundaryConnection_measureReal_ge_sq_of_translate (Measure.dirac allOpen)
    (isFKG_dirac _) (allOpen_translationInvariant P) (allOpen_unique P hconn) r S z hS hT

-- Open boundary connections tending to one.
example [Infinite V] (E : PeriodicPlaneEmbedding P) (hconn : P.graph.Connected) (r : ℝ) :=
  E.exists_infiniteOpenBoundaryConnection_sequence_tendsto_one (Measure.dirac allOpen)
    (isFKG_dirac _) (allOpen_translationInvariant P) (allOpen_unique P hconn) r

-- Open boundary-ray maxima tending to one, rays at height `0`.
example [Infinite V] (E : PeriodicPlaneEmbedding P) (hconn : P.graph.Connected) (r : ℝ) :=
  E.exists_infiniteOpenBoundaryRay_max_sequence_tendsto_one (Measure.dirac allOpen)
    (isFKG_dirac _) (allOpen_translationInvariant P) (allOpen_unique P hconn) r
    fun _ => 0

end OpenBoundarySource
end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield
