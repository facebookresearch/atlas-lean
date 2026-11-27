/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.BurtonKeaneMerge

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.BurtonKeaneMerge`

On the square lattice `square` (periodic graph on `ℤ²`):
* `forceOpenFinset` opens an edge of `F` in the all-closed configuration, and
  `forceOpenFinset_le` compares it with the original;
* `exists_forceOpen_walk` applies (the square lattice is connected) and yields an open path from
  `0` to `(1, 1)` after forcing finitely many edges open in the all-closed configuration;
* the Dirac mass at the all-open configuration is ergodic and has finite energy
  (`HasFiniteEnergy` is non-vacuous), so `numInfiniteClusters_zero_one_or_top` applies to it.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.BurtonKeaneMerge

open MeasureTheory _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.FK.PeriodicPlanar

/-- The all-open configuration. -/
def allOpen : ConfigSpace (Sym2 (Site 2)) := fun _ => true

/-- The all-closed configuration. -/
def allClosed : ConfigSpace (Sym2 (Site 2)) := fun _ => false

/-- The square lattice is connected. -/
theorem square_connected : square.graph.Connected :=
  ⟨fun x y => hypercubicLattice_two_reachable x y⟩

-- Forcing the edge `s(0, (1, 0))` open opens it, even in the all-closed configuration.
example : forceOpenFinset {s(0, ![1, 0])} allClosed s(0, ![1, 0]) = true :=
  forceOpenFinset_of_mem (Finset.mem_singleton_self _) allClosed

-- Forcing edges open can only add open edges.
example : allClosed ≤ forceOpenFinset {s(0, ![1, 0])} allClosed :=
  forceOpenFinset_le _ _

-- On the connected square lattice, finitely many forced edges join `0` to `(1, 1)`.
example : ∃ F : Finset (Sym2 (Site 2)),
    (square.openSubgraph (forceOpenFinset F allClosed)).Reachable 0 ![1, 1] := by
  obtain ⟨F, hF⟩ := square.exists_forceOpen_walk square_connected 0 ![1, 1]
  exact ⟨F, hF allClosed⟩

/-- The Dirac mass at the all-open configuration is ergodic. -/
theorem isErgodic_dirac_allOpen : square.IsErgodic (Measure.dirac allOpen) := by
  refine ⟨fun z => ?_, fun s hs _ => ?_⟩
  · refine ⟨square.measurable_configTranslate z, ?_⟩
    rw [Measure.map_dirac' (square.measurable_configTranslate z)]
    rfl
  · by_cases h : allOpen ∈ s
    · exact Or.inr (Measure.dirac_apply_of_mem h)
    · left
      rw [Measure.dirac_apply' _ hs, Set.indicator_of_notMem h]

/-- The Dirac mass at the all-open configuration has finite energy: forcing edges open fixes it. -/
theorem hasFiniteEnergy_dirac_allOpen : HasFiniteEnergy (Measure.dirac allOpen) := by
  intro F
  rw [Measure.map_dirac' (measurable_forceOpenFinset F)]
  have h : forceOpenFinset F allOpen = allOpen := by
    funext e
    by_cases he : e ∈ F
    · exact forceOpenFinset_of_mem he allOpen
    · exact forceOpenFinset_of_notMem he allOpen
  rw [h]

-- The infinite-cluster count is almost surely `0`, `1` or `∞` under the Dirac mass.
example : ∃ k : ℕ∞, Measure.dirac allOpen {ω | square.numInfiniteClusters ω = k} = 1 ∧
    (k = 0 ∨ k = 1 ∨ k = ⊤) :=
  square.numInfiniteClusters_zero_one_or_top square_connected _ isErgodic_dirac_allOpen
    hasFiniteEnergy_dirac_allOpen

end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.BurtonKeaneMerge
