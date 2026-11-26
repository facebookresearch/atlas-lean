/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.HalfPlaneTranslation

/-!
# Tests for `Sheffield.HalfPlaneTranslation`

Module under test: `Sheffield.HalfPlaneTranslation` in
`PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar`.

* All four headline lemmas applied to the Dirac mass on the all-open configuration, whose
  translation invariance is proved here (`allOpen_translationInvariant`): vertical translation
  of lower and upper boundary-ray connections by `t = 2`, and the two shift limits.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield
namespace HalfPlaneTranslation

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

-- Lower boundary rays, shift `2`.
example (E : PeriodicPlaneEmbedding P) (r s : ℝ) (S : Set V) :=
  E.lowerBoundaryRay_connection_measureReal_vertical (Measure.dirac allOpen)
    (allOpen_translationInvariant P) 2 r s S

-- Upper boundary rays, shift `2`.
example (E : PeriodicPlaneEmbedding P) (r s : ℝ) (S : Set V) :=
  E.upperBoundaryRay_connection_measureReal_vertical (Measure.dirac allOpen)
    (allOpen_translationInvariant P) 2 r s S

-- Shifting down along lower rays.
example (E : PeriodicPlaneEmbedding P) (r : ℝ) (S : Set V) :=
  E.shift_down_lowerBoundaryRay_measureReal_tendsto (Measure.dirac allOpen)
    (allOpen_translationInvariant P) r S

-- Shifting up along upper rays.
example (E : PeriodicPlaneEmbedding P) (r : ℝ) (S : Set V) :=
  E.shift_up_upperBoundaryRay_measureReal_tendsto (Measure.dirac allOpen)
    (allOpen_translationInvariant P) r S

end HalfPlaneTranslation
end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield
