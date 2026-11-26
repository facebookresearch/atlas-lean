/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.CanonicalTranslation

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.CanonicalTranslation`

On the square lattice `square` at `p = 1/2`, `q = 1`:
* `freeBufferedInfiniteVolume_multiOpen_shift` equates the free-limit probabilities that the edge
  `s(0, (1, 0))` is open and that its translate `s((1, 0), (2, 0))` is open;
* `freeBufferedInfiniteVolume_isTranslationInvariant` applies to `square`, and translating the event
  "`s(0, (1, 0))` is open" by `(0, 1)` keeps its probability.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.CanonicalTranslation

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

-- The all-open event of an edge has the same mass as that of its translate.
example : muFree (_root_.StatMech.FK.fmu_multiOpen {s(0, ![1, 0])}) =
    muFree (_root_.StatMech.FK.fmu_multiOpen
      (({s(0, ![1, 0])} : Finset (Sym2 (Site 2))).image (Sym2.map (square.shift ![1, 0])))) :=
  square.freeBufferedInfiniteVolume_multiOpen_shift ![1, 0] _ _ _ le_rfl

-- The free limit on `square` is translation invariant.
example : square.IsTranslationInvariant muFree :=
  square.freeBufferedInfiniteVolume_isTranslationInvariant _ _ le_rfl

-- Translating an edge event by `(0, 1)` keeps its probability.
example : muFree (square.configTranslate ![0, 1] ⁻¹' edgeOpen s(0, ![1, 0])) =
    muFree (edgeOpen s(0, ![1, 0])) :=
  (square.freeBufferedInfiniteVolume_isTranslationInvariant _ _ le_rfl ![0, 1]).measure_preimage
    (edgeOpen_measurableSet _).nullMeasurableSet

end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.CanonicalTranslation
