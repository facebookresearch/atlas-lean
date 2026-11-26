/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.DeepConnectorRows

/-!
# Tests for `Sheffield.DeepConnectorRows`

Module under test: `Sheffield.DeepConnectorRows` in
`PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar`.

* The hypotheses `IsFKG`, translation invariance and almost-sure uniqueness are discharged
  together by the Dirac mass on the all-open configuration of any connected infinite periodic
  graph (`isFKG_dirac`, `allOpen_translationInvariant`, `allOpen_unique`, proved here).
* `PeriodicPlanarDualPair.complementaryDual_rightHalfPlane_measure_eq_zero_of_separatedRows` and
  `finiteDeepConnectorBandSchedule_of_separatedRows` (with `r = R`) applied to that measure; the
  dual and disjointness hypotheses stay arguments of the specialization.
* `PeriodicPlaneEmbedding.`
  `exists_separated_finiteDeepOpenExitedJoinedBoundaryArmEvent_measureReal_gt` elaborates
  (check-only).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield
namespace DeepConnectorRows

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

variable {V W : Type*} [DecidableEq V] [DecidableEq W] [Countable V] [Countable W] [Infinite V]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

-- The separated-rows measure-zero statement for the all-open Dirac mass.
example (D : PeriodicPlanarDualPair P Pdual) :=
  D.complementaryDual_rightHalfPlane_measure_eq_zero_of_separatedRows (Measure.dirac allOpen)
    (isFKG_dirac _) (allOpen_translationInvariant P) (allOpen_unique P D.primal_connected)

-- The band schedule for the all-open Dirac mass, with `r = R`.
noncomputable example (D : PeriodicPlanarDualPair P Pdual) (rDual R s : ℝ) (band : ℕ) (t : ℤ) :=
  D.finiteDeepConnectorBandSchedule_of_separatedRows (Measure.dirac allOpen) (isFKG_dirac _)
    (allOpen_translationInvariant P) (allOpen_unique P D.primal_connected) rDual band
    (le_refl R) s t

open PeriodicPlaneEmbedding in
example := @exists_separated_finiteDeepOpenExitedJoinedBoundaryArmEvent_measureReal_gt

end DeepConnectorRows
end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield
