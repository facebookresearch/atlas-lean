/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.HalfPlane

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.HalfPlane`

* `three_event_intersection_lower_bound` for a Dirac mass and three copies of `univ`.
* `directional_sqrt_trick` for a Dirac mass (FKG, proved here) and the increasing event `univ`.
* `PeriodicGraph.connectedWithinSet` is inhabited: on the square lattice the all-open
  configuration connects `x` to itself inside `{x}`; `connectedWithinSet_isIncreasing` applies.
* `PeriodicPlaneEmbedding.exists_shift_halfPlanePairMergeError_measureReal_lt` elaborates
  (check-only; no concrete plane embedding is available).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.HalfPlane

open _root_.StatMech _root_.StatMech.FK _root_.StatMech.FK.PeriodicPlanar MeasureTheory

/-- Every Dirac mass on bond configurations is FKG. -/
theorem isFKG_dirac {V : Type*} (ω : ConfigSpace (Sym2 V)) : IsFKG (Measure.dirac ω) := by
  intro A B hA hB _ _
  rw [Measure.real, Measure.real, Measure.real, Measure.dirac_apply' _ hA,
    Measure.dirac_apply' _ hB, Measure.dirac_apply' _ (hA.inter hB)]
  by_cases hωA : ω ∈ A <;> by_cases hωB : ω ∈ B <;> simp [hωA, hωB]

-- Bonferroni for a Dirac mass and `A = B = C = univ`.
example (ω : ConfigSpace (Sym2 (Fin 2))) :
    (Measure.dirac ω).real Set.univ + (Measure.dirac ω).real Set.univ +
        (Measure.dirac ω).real Set.univ - 2 ≤
      (Measure.dirac ω).real ((Set.univ ∩ Set.univ) ∩ Set.univ) :=
  three_event_intersection_lower_bound _ MeasurableSet.univ MeasurableSet.univ

-- The directional square-root trick for a Dirac mass.
example (ω : ConfigSpace (Sym2 (Fin 2))) :
    1 - Real.sqrt (1 - (Measure.dirac ω).real (Set.univ ∪ Set.univ)) ≤
      (Measure.dirac ω).real Set.univ :=
  directional_sqrt_trick _ (isFKG_dirac ω) (fun _ _ _ _ => trivial) (fun _ _ _ _ => trivial)
    MeasurableSet.univ MeasurableSet.univ le_rfl

-- The all-open configuration connects `x` to itself inside `{x}` (empty continuation list).
example (x : StatMech.Lattice.Site 2) :
    (fun _ => true) ∈ PeriodicPlanar.square.connectedWithinSet {x} x x :=
  ⟨[], List.isChain_singleton _, rfl, by simp⟩

-- Connection inside a set is an increasing event.
example (x y : StatMech.Lattice.Site 2) :
    IsIncreasing (PeriodicPlanar.square.connectedWithinSet {x, y} x y) :=
  PeriodicPlanar.square.connectedWithinSet_isIncreasing _ x y

-- `PeriodicPlaneEmbedding.exists_shift_halfPlanePairMergeError_measureReal_lt` elaborates.
example := @PeriodicPlaneEmbedding.exists_shift_halfPlanePairMergeError_measureReal_lt

end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.HalfPlane
