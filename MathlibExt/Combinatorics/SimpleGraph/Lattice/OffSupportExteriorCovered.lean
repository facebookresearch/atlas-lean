/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.InsideConnected
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.OffWalkExteriorEscape

/-!
# Covering the outside of a closed walk by one off-walk component

For a closed walk `Vc` in the square lattice `ℤ²`, two descriptions of the lattice with the vertices
of `Vc` removed are in use, `StatMech.Lattice.offSupport Vc` and
`StatMech.Lattice.ffc_offSupportLattice` of the vertex set; this file transfers reachability
between them. It also shows that a site escapes to the exterior of a box along any of the four
straight segments that miss `Vc`.

The covering predicate `orc_ExteriorCovered Vc beacon` (the whole outside of `Vc` lies in the
off-walk component of `beacon`) never holds, for any closed walk and any `beacon`
(`StatMech.Lattice.orc_not_exteriorCovered`): outside sites on `Vc` are isolated off `Vc`.

## Main definitions

* `StatMech.Lattice.orc_ExteriorCovered Vc beacon`: the outside of `Vc` lies in the component of
  `beacon` in the lattice with the vertices of `Vc` removed.

## Main results

* `StatMech.Lattice.orc_offSupportLattice_reachable_of_offSupport`,
  `StatMech.Lattice.orc_offSupport_reachable_of_offSupportLattice`: the two off-walk lattices have
  the same reachability.
* `StatMech.Lattice.orc_not_exteriorCovered`: the covering predicate is unsatisfiable.
* `StatMech.Lattice.orc_reachesExterior_of_anyClear`: a clear straight segment to the exterior gives
  an escape.
-/

@[expose] public section

open Set SimpleGraph Function

namespace StatMech

namespace Lattice

variable {a : Site 2}

/-- The lattice with the vertices of `Vc` removed, `StatMech.Lattice.offSupport Vc`, is
definitionally `StatMech.Lattice.ffc_offSupportLattice` of the vertex set of `Vc`. -/
theorem orc_offSupport_eq_ffc_offSupportLattice (Vc : (hypercubicLattice 2).Walk a a) :
    offSupport Vc = ffc_offSupportLattice (oc_supportSet Vc) := rfl

/-- Reachability in `StatMech.Lattice.offSupport Vc` gives reachability in
`StatMech.Lattice.ffc_offSupportLattice` of the vertex set of `Vc` (the same graph). -/
theorem orc_offSupportLattice_reachable_of_offSupport (Vc : (hypercubicLattice 2).Walk a a)
    {x y : Site 2} (hx : x ∉ Vc.support) (h : (offSupport Vc).Reachable x y) :
    (ffc_offSupportLattice (oc_supportSet Vc)).Reachable x y := by
  obtain ⟨p, hp⟩ := offSupport_reachable_to_offSupportWalk Vc h hx
  exact (ffc_reachable_iff_offSupportWalk (B := oc_supportSet Vc) hx).mpr ⟨p, hp⟩

/-- Reachability in `StatMech.Lattice.ffc_offSupportLattice` of the vertex set of `Vc` gives
reachability in `StatMech.Lattice.offSupport Vc`. -/
theorem orc_offSupport_reachable_of_offSupportLattice (Vc : (hypercubicLattice 2).Walk a a)
    {x y : Site 2} (hx : x ∉ Vc.support)
    (h : (ffc_offSupportLattice (oc_supportSet Vc)).Reachable x y) :
    (offSupport Vc).Reachable x y := by
  obtain ⟨p, hp⟩ := (ffc_reachable_iff_offSupportWalk (B := oc_supportSet Vc) hx).mp h
  exact offSupportWalk_to_offSupport_reachable Vc p hp

/-- The outside of the closed walk `Vc` (even ray count) lies in the component of `beacon` in the
lattice with the vertices of `Vc` removed. This never holds
(`StatMech.Lattice.orc_not_exteriorCovered`). -/
def orc_ExteriorCovered (Vc : (hypercubicLattice 2).Walk a a) (beacon : Site 2) : Prop :=
  (jec_leftRegion Vc)ᶜ ⊆ offSupportComponent Vc beacon

/-- `StatMech.Lattice.orc_ExteriorCovered` never holds. If the beacon is off `Vc`, its component
contains only sites off `Vc`, but a vertex of `Vc` in its leftmost column is outside. If the beacon
is on `Vc`, its component is the beacon alone, but the site just left of that vertex is outside and
off `Vc`. -/
theorem orc_not_exteriorCovered (Vc : (hypercubicLattice 2).Walk a a) (beacon : Site 2) :
    ¬ orc_ExteriorCovered Vc beacon := by
  intro hcov
  obtain ⟨v, hv, hout, hmin⟩ := oc_exists_support_not_leftRegion Vc
  by_cases hb : beacon ∈ Vc.support
  · set w : Site 2 := ![v 0 - 1, v 1] with hw
    have hw0 : w 0 = v 0 - 1 := by simp [hw]
    have hwoff : w ∉ Vc.support := fun h => by have := hmin w h; omega
    have hwout : w ∉ jec_leftRegion Vc := by
      rw [jec_mem_leftRegion, not_not,
        jec_rayCount_eq_zero_of_right w Vc (fun p hp => by have := hmin p hp; omega)]
      exact ⟨0, rfl⟩
    have hbw := oc_ffc_reachable_eq_of_mem (B := oc_supportSet Vc) hb
      ((mem_offSupportComponent Vc).mp (hcov hwout))
    exact hwoff (hbw ▸ hb)
  · exact offSupportComponent_offSupport Vc hb (hcov hout) hv

/-- `StatMech.Lattice.orc_ExteriorCovered` and `StatMech.Lattice.oc_OutsideReachesExterior` agree
for `Vc` in the box: both are always false (`StatMech.Lattice.orc_not_exteriorCovered`,
`StatMech.Lattice.oc_not_outsideReachesExterior`). -/
theorem orc_exteriorCovered_iff_outsideReachesExterior (Vc : (hypercubicLattice 2).Walk a a)
    (R : ℕ) (hsupp : oc_supportSet Vc ⊆ box 2 R)
    {beacon : Site 2} (_hbExt : beacon ∈ exterior 2 R) (_hbOff : beacon ∉ Vc.support) :
    orc_ExteriorCovered Vc beacon ↔ oc_OutsideReachesExterior Vc R :=
  ⟨fun h => (orc_not_exteriorCovered Vc beacon h).elim,
    fun h => (oc_not_outsideReachesExterior Vc R hsupp h).elim⟩

/-- A site reaches the exterior of the box `[-R, R]²` avoiding `Vc` if one of the four straight
segments from it (up, down, right, left) to row or column `±(R + 1)` misses `Vc`. -/
theorem orc_reachesExterior_of_anyClear (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ) {z : Site 2}
    (hclear :
      (∀ w ∈ (sw_vertSeg (z 0) (z 1) ((R : ℤ) + 1)).support, w ∉ Vc.support) ∨
      (∀ w ∈ (sw_vertSeg (z 0) (z 1) (-((R : ℤ) + 1))).support, w ∉ Vc.support) ∨
      (∀ w ∈ (sw_horizSeg (z 1) (z 0) ((R : ℤ) + 1)).support, w ∉ Vc.support) ∨
      (∀ w ∈ (sw_horizSeg (z 1) (z 0) (-((R : ℤ) + 1))).support, w ∉ Vc.support)) :
    ∃ e : Site 2, e ∈ exterior 2 R ∧
      (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z e := by
  rcases hclear with h | h | h | h
  · exact oc_reachesExterior_of_vertUpClear Vc R h
  · exact oc_reachesExterior_of_vertDownClear Vc R h
  · exact oc_reachesExterior_of_horizRightClear Vc R h
  · exact oc_reachesExterior_of_horizLeftClear Vc R h

end Lattice

end StatMech
