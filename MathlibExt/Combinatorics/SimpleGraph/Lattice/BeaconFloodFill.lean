/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.OffWalkExteriorEscape

/-!
# The flood fill of the beacon outside a closed walk

Let `Vc` be a closed walk in the square lattice `ℤ²` whose vertices lie in the box `[-R, R]²`, and
let the beacon be the corner site `(R + 1, R + 1)` of the exterior. The flood fill of the beacon
avoiding `Vc` (the sites joined to the beacon by lattice paths avoiding `Vc`) contains the whole
exterior of the box and every site off `Vc` at height at least `R`, and lies outside `Vc` in the
even–odd sense. A site is in this flood fill exactly when it reaches the exterior avoiding `Vc`.

The flood fill never covers the outside of `Vc`: some vertex of `Vc` is outside, and vertices of
`Vc` are not in the flood fill (`StatMech.Lattice.ocov_not_beaconCovers`).

## Main results

* `StatMech.Lattice.ocov_exterior_subset_beaconFill`: the exterior lies in the beacon flood fill.
* `StatMech.Lattice.ocov_row_ge_R_in_beaconFill`: so does every site off `Vc` at height `≥ R`.
* `StatMech.Lattice.ocov_beaconFill_subset_outside`: the beacon flood fill lies outside `Vc`.
* `StatMech.Lattice.ocov_reachesExterior_iff_in_beaconFill`: membership in the beacon flood fill is
  reaching the exterior avoiding `Vc`.
* `StatMech.Lattice.ocov_not_beaconCovers`: the beacon flood fill never contains the whole outside.
-/

@[expose] public section

open Set SimpleGraph Function

namespace StatMech

namespace Lattice

variable {a : Site 2}

/-- The beacon `(R + 1, R + 1)` is in the exterior of the box `[-R, R]²`. -/
theorem ocov_beacon_mem_exterior (R : ℕ) : beacon 2 R ∈ exterior 2 R :=
  beacon_mem_exterior R (by norm_num)

theorem ocov_beacon_offSupport (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) :
    beacon 2 R ∉ Vc.support :=
  arcxc_exterior_offSupport hsupp (ocov_beacon_mem_exterior R)

theorem ocov_exterior_in_beaconFill (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) {z : Site 2} (hz : z ∈ exterior 2 R) :
    z ∈ ffc_floodFill (oc_supportSet Vc) (beacon 2 R) := by
  rw [ffc_mem_floodFill]
  exact (arcxc_exterior_reachable_offSupport hsupp (ocov_beacon_mem_exterior R) hz)

/-- The exterior of a box containing `Vc` lies in the flood fill of the beacon avoiding `Vc`. -/
theorem ocov_exterior_subset_beaconFill (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) :
    exterior 2 R ⊆ ffc_floodFill (oc_supportSet Vc) (beacon 2 R) :=
  fun _ hz => ocov_exterior_in_beaconFill Vc R hsupp hz

theorem ocov_in_beaconFill_of_reaches_exterior (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) {z e : Site 2} (he : e ∈ exterior 2 R)
    (hze : (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z e) :
    z ∈ ffc_floodFill (oc_supportSet Vc) (beacon 2 R) := by
  rw [ffc_mem_floodFill]
  have hbe : (ffc_offSupportLattice (oc_supportSet Vc)).Reachable (beacon 2 R) e :=
    arcxc_exterior_reachable_offSupport hsupp (ocov_beacon_mem_exterior R) he
  exact hbe.trans hze.symm

/-- Sites off `Vc` at height at least `R` are in the beacon flood fill. -/
theorem ocov_row_ge_R_in_beaconFill (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) {z : Site 2}
    (hzrow : (R : ℤ) ≤ z 1) (hzoff : z ∉ Vc.support) :
    z ∈ ffc_floodFill (oc_supportSet Vc) (beacon 2 R) := by
  obtain ⟨e, he, hze⟩ := oc_reachesExterior_of_row_ge_R Vc R hsupp hzrow hzoff
  exact ocov_in_beaconFill_of_reaches_exterior Vc R hsupp he hze

theorem ocov_beacon_outside (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R) :
    beacon 2 R ∉ jec_leftRegion Vc :=
  egf_exterior_outside Vc R hsupp (ocov_beacon_mem_exterior R)

theorem ocov_beaconFill_mem_outside (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R) {z : Site 2}
    (hz : z ∈ ffc_floodFill (oc_supportSet Vc) (beacon 2 R)) :
    z ∉ jec_leftRegion Vc := by
  rw [ffc_mem_floodFill] at hz
  have hsupp' : oc_supportSet Vc ⊆ box 2 R := fun p hp => hsupp p hp
  obtain ⟨pw, hpw⟩ :=
    (ffc_reachable_iff_offSupportWalk (B := oc_supportSet Vc)
      (ocov_beacon_offSupport Vc R hsupp')).mp hz
  have hsame := jlri_sameRegion_along_offSupport_walk Vc pw hpw
  intro hzin
  exact ocov_beacon_outside Vc R hsupp (hsame.mpr hzin)

/-- The flood fill of the beacon avoiding `Vc` lies outside `Vc`: paths avoiding `Vc` keep the
parity of the ray count, and the beacon is outside. -/
theorem ocov_beaconFill_subset_outside (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R) :
    ffc_floodFill (oc_supportSet Vc) (beacon 2 R) ⊆ (jec_leftRegion Vc)ᶜ :=
  fun _ hz => ocov_beaconFill_mem_outside Vc R hsupp hz

theorem ocov_reachesExterior_of_in_beaconFill (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    {z : Site 2} (hz : z ∈ ffc_floodFill (oc_supportSet Vc) (beacon 2 R)) :
    ∃ e : Site 2, e ∈ exterior 2 R ∧
      (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z e := by
  rw [ffc_mem_floodFill] at hz
  exact ⟨beacon 2 R, ocov_beacon_mem_exterior R, hz.symm⟩

/-- A site reaches the exterior avoiding `Vc` if and only if it is in the beacon flood fill. -/
theorem ocov_reachesExterior_iff_in_beaconFill (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) {z : Site 2} :
    (∃ e : Site 2, e ∈ exterior 2 R ∧
        (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z e)
      ↔ z ∈ ffc_floodFill (oc_supportSet Vc) (beacon 2 R) := by
  constructor
  · rintro ⟨e, he, hze⟩
    exact ocov_in_beaconFill_of_reaches_exterior Vc R hsupp he hze
  · intro hz
    exact ocov_reachesExterior_of_in_beaconFill Vc R hz

/-- `StatMech.Lattice.oc_OutsideReachesExterior` is the beacon flood fill covering the outside of
`Vc`. Both sides are always false for `Vc` in the box (`StatMech.Lattice.ocov_not_beaconCovers`). -/
theorem ocov_outsideReachesExterior_iff_beaconCovers (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) :
    oc_OutsideReachesExterior Vc R ↔
      (jec_leftRegion Vc)ᶜ ⊆ ffc_floodFill (oc_supportSet Vc) (beacon 2 R) := by
  constructor
  · intro h z hz
    have hz' : z ∉ jec_leftRegion Vc := hz
    exact (ocov_reachesExterior_iff_in_beaconFill Vc R hsupp).mp (h z hz')
  · intro hcov z hz
    exact (ocov_reachesExterior_iff_in_beaconFill Vc R hsupp).mpr (hcov hz)

/-- The beacon flood fill equals the outside of `Vc` iff it covers it. Both sides are always
false (`StatMech.Lattice.ocov_not_beaconCovers`). -/
theorem ocov_beaconFill_eq_outside_iff (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R) :
    ffc_floodFill (oc_supportSet Vc) (beacon 2 R) = (jec_leftRegion Vc)ᶜ ↔
      (jec_leftRegion Vc)ᶜ ⊆ ffc_floodFill (oc_supportSet Vc) (beacon 2 R) := by
  constructor
  · intro h; rw [h]
  · intro hcov
    exact le_antisymm (ocov_beaconFill_subset_outside Vc R hsupp) hcov

/-- The flood fill of the beacon avoiding `Vc` never contains the whole outside of `Vc`: a vertex of
`Vc` in its leftmost column is outside, but it is isolated in the lattice with `Vc` removed and is
not the beacon. -/
theorem ocov_not_beaconCovers (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) :
    ¬ (jec_leftRegion Vc)ᶜ ⊆ ffc_floodFill (oc_supportSet Vc) (beacon 2 R) := by
  intro hcov
  obtain ⟨v, hv, hout, -⟩ := oc_exists_support_not_leftRegion Vc
  have hvb := oc_ffc_reachable_eq_of_mem (B := oc_supportSet Vc) hv
    ((ffc_mem_floodFill.mp (hcov hout)).symm)
  exact ocov_beacon_offSupport Vc R hsupp (hvb ▸ hv)

end Lattice

end StatMech
