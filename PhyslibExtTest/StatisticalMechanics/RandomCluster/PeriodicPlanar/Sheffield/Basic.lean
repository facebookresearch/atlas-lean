/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.Basic

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.Basic`

* `IsFKG` is satisfiable: every Dirac mass on configurations is FKG (non-vacuity witness).
* `PeriodicGraph.IsTranslationInvariant` is satisfiable: the Dirac mass on the all-open
  configuration of the square lattice `PeriodicPlanar.square` is translation invariant.
* `measurable_sqrt_trick` applied to that FKG Dirac mass and the increasing event `univ`.
* `min_tendsto_zero_of_matched_exclusion` on explicit constant sequences (primal `0`, dual `1`).
* `PeriodicPlaneEmbedding.exists_edgeArc_displacement_bound` and
  `PeriodicPlanarDualPair.matchedCrossingEvents_disjoint` elaborate (check-only; no concrete plane
  embedding is available).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.Basic

open _root_.StatMech _root_.StatMech.FK _root_.StatMech.FK.PeriodicPlanar MeasureTheory Filter

/-- Every Dirac mass on bond configurations is FKG. -/
theorem isFKG_dirac {V : Type*} (ω : ConfigSpace (Sym2 V)) : IsFKG (Measure.dirac ω) := by
  intro A B hA hB _ _
  rw [Measure.real, Measure.real, Measure.real, Measure.dirac_apply' _ hA,
    Measure.dirac_apply' _ hB, Measure.dirac_apply' _ (hA.inter hB)]
  by_cases hωA : ω ∈ A <;> by_cases hωB : ω ∈ B <;> simp [hωA, hωB]

/-- The Dirac mass on the all-open configuration of the square lattice is translation
invariant. -/
theorem square_allOpen_translationInvariant :
    PeriodicPlanar.square.IsTranslationInvariant
      (Measure.dirac (fun _ => true : ConfigSpace (Sym2 (StatMech.Lattice.Site 2)))) := by
  intro z
  refine ⟨PeriodicPlanar.square.measurable_configTranslate z, ?_⟩
  rw [Measure.map_dirac' (PeriodicPlanar.square.measurable_configTranslate z)]
  rfl

-- The square-root trick for the FKG Dirac mass and the increasing event `univ`.
example (ω : ConfigSpace (Sym2 (Fin 2))) :
    1 - Real.sqrt (1 - (Measure.dirac ω).real (Set.univ ∪ Set.univ)) ≤
      max ((Measure.dirac ω).real Set.univ) ((Measure.dirac ω).real Set.univ) :=
  measurable_sqrt_trick _ (isFKG_dirac ω) (fun _ _ _ _ => trivial) (fun _ _ _ _ => trivial)
    MeasurableSet.univ MeasurableSet.univ

-- Matched exclusion: primal probabilities `0`, dual probabilities `1`.
example : Tendsto (fun n : ℕ => min ((fun _ => (0 : ℝ)) n) ((fun _ => (0 : ℝ)) n))
    atTop (nhds 0) :=
  min_tendsto_zero_of_matched_exclusion (fun _ => 0) (fun _ => 0) (fun _ => 1) (fun _ => 1)
    (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => by norm_num) (fun _ => by norm_num)
    (by simp)

-- `PeriodicPlaneEmbedding.exists_edgeArc_displacement_bound` elaborates.
example := @PeriodicPlaneEmbedding.exists_edgeArc_displacement_bound

-- `PeriodicPlanarDualPair.matchedCrossingEvents_disjoint` elaborates.
example := @PeriodicPlanarDualPair.matchedCrossingEvents_disjoint

end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.Basic
