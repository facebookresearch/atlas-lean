/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.EnclosedAreaWitness

/-!
# Winding witnesses from exterior connectivity of the whole complement

Let `mpl_orbitLoop K a` be the face loop of a boundary orbit of a set `K` of sites. Assume that
every site outside `K` is joined, by a lattice path avoiding the loop, to a site left of the whole
loop (the hypothesis `hExt` below, the unfolded form of `ior_ExteriorConnected K a`). Then every
site outside `K` has even ray count, so the inside of the loop is contained in `K`; if moreover the
loop is a cycle, some site has odd ray count and is a winding witness.

The hypothesis `hExt` is very strong: it fails whenever the loop passes through a site outside `K`,
for instance for the unit cell (`exc_oldExteriorConnected_false`) and for the domino. The results
below are therefore conditional on a hypothesis that is false in the basic examples. The corrected
hypotheses are `exc_OffSupportReachesExterior` and `exc_SupportOddInK`.

## Main results

* `StatMech.Lattice.wwc_outside_even_of_exterior`: under `hExt`, sites outside `K` have even ray
  count.
* `StatMech.Lattice.wwc_interiorSubset_of_exterior`: under `hExt`, `eaw_InteriorSubset K a` holds.
* `StatMech.Lattice.wwc_windingWitness_of_cycle_exterior`: under `hExt`, a cycle loop gives a
  winding witness.
-/

@[expose] public section

open Set SimpleGraph Function

namespace StatMech

namespace Lattice

/-- If every site outside `K` is joined off the face loop to a site weakly left of the loop, then
every site outside `K` has even ray count. See also `StatMech.Lattice.oee_outsideHalf_of_exteriorEq`
for the loop `olb_orbitLoop`. The exterior hypothesis `hExt` fails
whenever the loop passes through a site outside `K` (see the module docstring). -/
theorem wwc_outside_even_of_exterior (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (hExt : ∀ z, z ∉ K → ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0,
      (∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support) ∧
      (∀ q ∈ (mpl_orbitLoop K a).support, z0 0 ≤ q 0)) :
    ∀ z, z ∉ K → Even (jec_rayCount z (mpl_orbitLoop K a)) := by
  intro z hz
  obtain ⟨z0, p, hp, hfar⟩ := hExt z hz
  have hbase : Even (jec_rayCount z0 (mpl_orbitLoop K a)) := by
    rw [jec_rayCount_eq_zero_of_right z0 (mpl_orbitLoop K a) hfar]
    exact Nat.even_iff.mpr rfl
  exact (oee_rayParity_const_along_walk (mpl_orbitLoop K a) p hp).mpr hbase

/-- Under the exterior hypothesis `hExt`, the inside of the face loop is contained in `K`. The
exterior hypothesis `hExt` fails whenever the loop passes through a site outside `K` (see the module
docstring). -/
theorem wwc_leftRegion_subset_of_exterior (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (hExt : ∀ z, z ∉ K → ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0,
      (∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support) ∧
      (∀ q ∈ (mpl_orbitLoop K a).support, z0 0 ≤ q 0)) :
    jec_leftRegion (mpl_orbitLoop K a) ⊆ K := by
  intro z hz
  rw [jec_mem_leftRegion] at hz
  by_contra hzK
  exact hz (wwc_outside_even_of_exterior K a hExt z hzK)

/-- Under the exterior hypothesis `hExt`, every site of odd ray count lies in `K`. The exterior
hypothesis `hExt` fails whenever the loop passes through a site outside `K` (see the module
docstring). -/
theorem wwc_interiorSubset_of_exterior (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (hExt : ∀ z, z ∉ K → ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0,
      (∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support) ∧
      (∀ q ∈ (mpl_orbitLoop K a).support, z0 0 ≤ q 0)) :
    eaw_InteriorSubset K a :=
  fun z hz => wwc_leftRegion_subset_of_exterior K a hExt (jec_mem_leftRegion _ z |>.mpr hz)

/-- If the face loop is a cycle (period at least three, distinct faces), the exterior hypothesis
gives a winding witness: a site of `K` with odd ray count. The exterior hypothesis `hExt` fails
whenever the loop passes through a site outside `K` (see the module docstring). -/
theorem wwc_windingWitness_of_cycle_exterior (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (hp : 3 ≤ dartOrbitPeriod K a)
    (hinj : Set.InjOn (fun k => dartFace ((dartNext K)^[k] a.1))
      (Set.Iio (dartOrbitPeriod K a)))
    (hExt : ∀ z, z ∉ K → ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0,
      (∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support) ∧
      (∀ q ∈ (mpl_orbitLoop K a).support, z0 0 ≤ q 0)) :
    wei_WindingWitness K a := by
  have hcyc : (mpl_orbitLoop K a).IsCycle := mpl_orbitLoop_isCycle K a hp hinj
  obtain ⟨z0, hz0⟩ := eaw_cycle_oddCell' (mpl_orbitLoop K a) hcyc
  exact ⟨z0, wwc_leftRegion_subset_of_exterior K a hExt ((jec_mem_leftRegion _ z0).mpr hz0), hz0⟩

/-- The same as `wwc_windingWitness_of_cycle_exterior`, with distinct faces replaced by the absence
of pinched faces. The exterior hypothesis `hExt` fails
whenever the loop passes through a site outside `K` (see the module docstring). -/
theorem wwc_windingWitness_of_noPinch_exterior (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (hp : 3 ≤ dartOrbitPeriod K a) (hnp : OrbitFaceNoPinch K a)
    (hExt : ∀ z, z ∉ K → ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0,
      (∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support) ∧
      (∀ q ∈ (mpl_orbitLoop K a).support, z0 0 ≤ q 0)) :
    wei_WindingWitness K a :=
  wwc_windingWitness_of_cycle_exterior K a hp (orbitFace_injOn_of_noPinch K a hnp) hExt

/-- The three conjuncts of `eaw_LoopWindsRegion` for one orbit, under the exterior hypothesis. The
exterior hypothesis `hExt` fails whenever the loop passes through a site outside `K` (see the module
docstring). -/
theorem wwc_loopWindsRegion_conjuncts_of_exterior (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (hp : 3 ≤ dartOrbitPeriod K a) (hnp : OrbitFaceNoPinch K a)
    (hExt : ∀ z, z ∉ K → ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0,
      (∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support) ∧
      (∀ q ∈ (mpl_orbitLoop K a).support, z0 0 ≤ q 0)) :
    3 ≤ dartOrbitPeriod K a ∧ OrbitFaceNoPinch K a ∧ eaw_InteriorSubset K a :=
  ⟨hp, hnp, wwc_interiorSubset_of_exterior K a hExt⟩

end Lattice

end StatMech
