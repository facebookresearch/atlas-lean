/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.CanonicalFiniteEnergy

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.CanonicalFiniteEnergy`

On the square lattice `square` at `p = 1/2`, `q = 1`:
* `freeBufferedInfiniteVolume_setPattern_absolutelyContinuous` applies to the pattern opening the
  single edge `s(0, (1, 0))`;
* `freeBufferedInfiniteVolume_hasFiniteEnergy` and `wiredBufferedInfiniteVolume_hasFiniteEnergy`
  apply to `square`; the free one is used at the forced edge set `{s(0, (1, 0))}`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.CanonicalFiniteEnergy

open MeasureTheory _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.FK.PeriodicPlanar

/-- The all-open configuration. -/
def allOpen : ConfigSpace (Sym2 (Site 2)) := fun _ => true

/-- The all-closed configuration. -/
def allClosed : ConfigSpace (Sym2 (Site 2)) := fun _ => false

/-- In the all-open configuration every cluster is the whole lattice. -/
theorem cluster_allOpen (x : Site 2) : square.cluster allOpen x = Set.univ := by
  have hopen : square.openSubgraph allOpen = hypercubicLattice 2 := by
    ext a b
    simp only [PeriodicGraph.openSubgraph_adj, allOpen, and_true]
    rfl
  ext y
  simp only [PeriodicGraph.cluster, hopen, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  exact hypercubicLattice_two_reachable x y

/-- The cluster of every vertex in the all-open configuration is infinite. -/
theorem cluster_allOpen_infinite (x : Site 2) : (square.cluster allOpen x).Infinite := by
  rw [cluster_allOpen]; exact Set.infinite_univ

/-- The free buffered infinite-volume FK measure on `square` at `p = 1/2`, `q = 1`. -/
noncomputable abbrev muFree : Measure (ConfigSpace (Sym2 (Site 2))) :=
  (square.freeBufferedInfiniteVolume (p := 1 / 2) (q := 1) (by norm_num) (by norm_num)
    (zero_lt_one.trans_le le_rfl) : Measure _)

/-- The wired buffered infinite-volume FK measure on `square` at `p = 1/2`, `q = 1`. -/
noncomputable abbrev muWired : Measure (ConfigSpace (Sym2 (Site 2))) :=
  (square.wiredBufferedInfiniteVolume (p := 1 / 2) (q := 1) (by norm_num) (by norm_num)
    (zero_lt_one.trans_le le_rfl) : Measure _)

/-- The event that the edge `e` is open. -/
def edgeOpen (e : Sym2 (Site 2)) : Set (ConfigSpace (Sym2 (Site 2))) := {ω | ω e = true}

/-- The event that an edge is open is increasing. -/
theorem edgeOpen_isIncreasing (e : Sym2 (Site 2)) : IsIncreasing (edgeOpen e) := by
  intro x y hxy hx
  have h := hxy e
  simp only [edgeOpen, Set.mem_ofPred_eq] at hx ⊢
  rw [hx] at h
  exact top_le_iff.mp h

/-- The event that an edge is open is clopen. -/
theorem edgeOpen_isClopen (e : Sym2 (Site 2)) : IsClopen (edgeOpen e) :=
  (isClopen_discrete {true}).preimage (continuous_apply e)

/-- The event that an edge is open is measurable. -/
theorem edgeOpen_measurableSet (e : Sym2 (Site 2)) : MeasurableSet (edgeOpen e) :=
  show MeasurableSet ((fun ω : ConfigSpace (Sym2 (Site 2)) => ω e) ⁻¹' {true}) from
    measurable_pi_apply e (measurableSet_singleton true)

/-- The single-edge set `{s(0, (1, 0))}`. -/
def I0 : Finset (Sym2 (Site 2)) := {s(0, ![1, 0])}

-- Opening the edge `s(0, (1, 0))` maps the free limit to an absolutely continuous measure.
example : muFree.map (_root_.StatMech.FK.setPattern I0 fun _ => true) ≪ muFree :=
  square.freeBufferedInfiniteVolume_setPattern_absolutelyContinuous _ _ le_rfl I0 _

-- Forcing `I0` open maps the free limit to an absolutely continuous measure.
example : muFree.map (forceOpenFinset I0) ≪ muFree :=
  square.freeBufferedInfiniteVolume_hasFiniteEnergy _ _ le_rfl I0

-- The wired limit on `square` has finite energy.
example : HasFiniteEnergy muWired := square.wiredBufferedInfiniteVolume_hasFiniteEnergy _ _ le_rfl

end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.CanonicalFiniteEnergy
