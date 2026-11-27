/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.CanonicalSheffieldFKG

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.CanonicalSheffieldFKG`

On the square lattice `square` at `p = 1/2`, `q = 1`, with `S = {0}` and `T = {(1, 0)}`:
* `freeBufferedInfiniteVolume_fkg_setHitsInfinite` and
  `wiredBufferedInfiniteVolume_fkg_setHitsInfinite` give FKG for "`S` meets an infinite cluster"
  and "`T` meets an infinite cluster";
* the all-open configuration lies in the first event (it is non-vacuous);
* given a periodic plane embedding of `square` (conditional form),
  `freeBufferedInfiniteVolume_fkg_rectSideConnection` applies to the unit rectangle.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.CanonicalSheffieldFKG

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

-- FKG for hitting an infinite cluster from `{0}` and from `{(1, 0)}`, free limit.
example : muFree.real (square.setHitsInfinite ({0} : Finset (Site 2))) *
      muFree.real (square.setHitsInfinite ({![1, 0]} : Finset (Site 2))) ≤
    muFree.real (square.setHitsInfinite ({0} : Finset (Site 2)) ∩
      square.setHitsInfinite ({![1, 0]} : Finset (Site 2))) :=
  square.freeBufferedInfiniteVolume_fkg_setHitsInfinite _ _ le_rfl {0} {![1, 0]}

-- The same under the wired limit.
example : muWired.real (square.setHitsInfinite ({0} : Finset (Site 2))) *
      muWired.real (square.setHitsInfinite ({![1, 0]} : Finset (Site 2))) ≤
    muWired.real (square.setHitsInfinite ({0} : Finset (Site 2)) ∩
      square.setHitsInfinite ({![1, 0]} : Finset (Site 2))) :=
  square.wiredBufferedInfiniteVolume_fkg_setHitsInfinite _ _ le_rfl {0} {![1, 0]}

-- The all-open configuration meets an infinite cluster from `{0}`.
example : allOpen ∈ square.setHitsInfinite ({0} : Finset (Site 2)) :=
  ⟨0, Finset.mem_coe.2 (Finset.mem_singleton_self 0), cluster_allOpen_infinite 0⟩

-- Given a plane embedding of `square`, FKG for side connections of the unit rectangle.
example (E : PeriodicPlaneEmbedding square) (sideS sideT : Set (Site 2)) :
    muFree.real (E.rectSideConnectionEvent 0 1 0 1 ((({0} : Finset (Site 2))) : Set _) sideS) *
        muFree.real (E.rectSideConnectionEvent 0 1 0 1 (({![1, 0]} : Finset (Site 2)) : Set _)
          sideT) ≤
      muFree.real (E.rectSideConnectionEvent 0 1 0 1 (({0} : Finset (Site 2)) : Set _) sideS ∩
        E.rectSideConnectionEvent 0 1 0 1 (({![1, 0]} : Finset (Site 2)) : Set _) sideT) :=
  E.freeBufferedInfiniteVolume_fkg_rectSideConnection _ _ le_rfl 0 1 0 1 {0} {![1, 0]} sideS sideT

end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.CanonicalSheffieldFKG
