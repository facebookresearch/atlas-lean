/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.EnclosedAreaWitness

/-!
# Parity of the ray count off the face loop of a boundary orbit

For a boundary orbit of a set `K` of sites, let `mpl_orbitLoop K a` be its closed face loop. A site
joined, by a lattice path avoiding the loop, to a site left of the whole loop has even ray count,
so it lies outside the loop. The inclusion of the inside of the loop in `K`
(`eaw_InteriorSubset K a`) is the inclusion `jec_leftRegion (mpl_orbitLoop K a) ⊆ K`, and an odd
ray count at the tail of some dart of the orbit gives a site of `K` inside the loop.

## Main definitions

* `StatMech.Lattice.ior_ExteriorConnected K a`: every site outside `K` is joined to a site left of
  the loop by a path avoiding the loop. This fails as soon as the loop passes through a site
  outside `K` (for the unit cell, `StatMech.Lattice.exc_oldExteriorConnected_false`); the corrected
  form is `StatMech.Lattice.exc_OffSupportReachesExterior`.

## Main results

* `StatMech.Lattice.ior_exterior_even`: sites joined to a far-left site off the loop have even ray
  count.
* `StatMech.Lattice.ior_interiorSubset_iff_leftRegion_subset`: `eaw_InteriorSubset K a` says that
  the inside of the loop is contained in `K`.
* `StatMech.Lattice.ior_windingWitness_of_tail_odd`: an orbit dart whose tail has odd ray count
  gives a winding witness.
-/

@[expose] public section

open Set SimpleGraph Function

namespace StatMech

namespace Lattice

/-- A site weakly left of every site of the loop has even ray count. See also
`StatMech.Lattice.oee_farLeft_even` for the loop `olb_orbitLoop`. -/
theorem ior_farLeft_even (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (z : Site 2)
    (hfar : ∀ p ∈ (mpl_orbitLoop K a).support, z 0 ≤ p 0) :
    Even (jec_rayCount z (mpl_orbitLoop K a)) := by
  rw [jec_rayCount_eq_zero_of_right z (mpl_orbitLoop K a) hfar]; exact Nat.even_iff.mpr rfl

/-- A site joined by a path avoiding the loop to a site weakly left of the loop has even ray count.
See also `StatMech.Lattice.oee_exterior_even` for the loop `olb_orbitLoop`. -/
theorem ior_exterior_even (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    {z z0 : Site 2} (p : (hypercubicLattice 2).Walk z z0)
    (hp : ∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support)
    (hfar : ∀ q ∈ (mpl_orbitLoop K a).support, z0 0 ≤ q 0) :
    Even (jec_rayCount z (mpl_orbitLoop K a)) := by
  have hbase : Even (jec_rayCount z0 (mpl_orbitLoop K a)) := ior_farLeft_even K a z0 hfar
  exact (oee_rayParity_const_along_walk (mpl_orbitLoop K a) p hp).mpr hbase

/-- Every site outside `K` is joined, by a lattice path avoiding the face loop of the orbit of `a`,
to a site weakly left of the whole loop.

This asks it also for sites outside `K` that lie on the loop, so it fails whenever the loop passes
through a site outside `K`: for the unit cell (`StatMech.Lattice.exc_oldExteriorConnected_false`)
and for the domino. `StatMech.Lattice.exc_OffSupportReachesExterior` is the corrected form. -/
def ior_ExteriorConnected (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) : Prop :=
  ∀ z, z ∉ K → ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0,
    (∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support) ∧
    (∀ q ∈ (mpl_orbitLoop K a).support, z0 0 ≤ q 0)

/-- `eaw_InteriorSubset K a` (every site of odd ray count lies in `K`) says that the inside of the
face loop is contained in `K`. -/
theorem ior_interiorSubset_iff_leftRegion_subset (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    eaw_InteriorSubset K a ↔ jec_leftRegion (mpl_orbitLoop K a) ⊆ K := by
  constructor
  · intro h z hz
    exact h z ((jec_mem_leftRegion (mpl_orbitLoop K a) z).mp hz)
  · intro h z hodd
    exact h ((jec_mem_leftRegion (mpl_orbitLoop K a) z).mpr hodd)

/-- If the tail of some dart of the orbit of `a` has odd ray count, that tail is a winding witness:
a site of `K` inside the face loop. See also `StatMech.Lattice.wwit_winding_witness_of_tailOdd` for
the loop `olb_orbitLoop`. -/
theorem ior_windingWitness_of_tail_odd (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (htail : ∃ i : ℕ, ¬ Even (jec_rayCount ((dartNext K)^[i] a.1).tail (mpl_orbitLoop K a))) :
    wei_WindingWitness K a := by
  obtain ⟨i, hodd⟩ := htail
  exact ⟨((dartNext K)^[i] a.1).tail, (iterate_isBoundaryDart K a.1 a.2 i).tail_mem, hodd⟩

end Lattice

end StatMech
