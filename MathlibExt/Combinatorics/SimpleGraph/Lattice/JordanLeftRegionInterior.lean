/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.ClosedContourSeparation
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.MinimalPeriodLoop
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.OrbitExteriorEven

/-!
# Off-walk paths stay on one side of a closed walk

Lattice paths that avoid a closed walk `Vc` never change the parity of the ray count, so they stay
inside or outside `jec_leftRegion Vc`; such paths survive the removal of the boundary edges of the
inside. The same statements are specialized to the face loop of a boundary orbit.

Connectivity of the outside by paths avoiding `Vc` never holds, because some vertex of `Vc` is
outside (`StatMech.Lattice.oc_not_hOutOff`); connectivity of a nonempty inside by such paths never
holds either (`StatMech.Lattice.oc_not_hInOff`).

## Main results

* `StatMech.Lattice.jlri_sameRegion_along_offSupport_walk`: paths off `Vc` stay on one side.
* `StatMech.Lattice.jlri_no_bdEdge_off_support`: an edge with both endpoints off `Vc` is not a
  boundary edge of the inside.
* `StatMech.Lattice.jlri_offSupport_walk_in_barrier`: a path off `Vc` is a path in the cut
  lattice.
-/

@[expose] public section

open Set SimpleGraph Function

namespace StatMech

namespace Lattice

theorem jlri_sameRegion_along_offSupport_walk {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x y : Site 2} (p : (hypercubicLattice 2).Walk x y)
    (hp : ∀ z ∈ p.support, z ∉ Vc.support) :
    (x ∈ jec_leftRegion Vc ↔ y ∈ jec_leftRegion Vc) := by
  have hpar := oee_rayParity_const_along_walk Vc p hp
  simp only [jec_mem_leftRegion]
  exact not_congr hpar

theorem jlri_no_bdEdge_off_support {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v)
    (hu : u ∉ Vc.support) (hv : v ∉ Vc.support) :
    ¬ bdEdge (jec_leftRegion Vc) s(u, v) := by
  have hsame : (u ∈ jec_leftRegion Vc ↔ v ∈ jec_leftRegion Vc) :=
    jlri_sameRegion_along_offSupport_walk Vc (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil)
      (by
        intro z hz
        rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil] at hz
        rcases List.mem_cons.mp hz with h | h
        · exact h ▸ hu
        · rcases List.mem_singleton.mp h with h'; exact h' ▸ hv)
  rw [bdEdge_mk]
  tauto

theorem jlri_offSupport_adj_in_barrier {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v)
    (hu : u ∉ Vc.support) (hv : v ∉ Vc.support) :
    (latticeMinusBarrier (jec_leftRegion Vc)).Adj u v :=
  ⟨hadj, jlri_no_bdEdge_off_support Vc hadj hu hv⟩

theorem jlri_offSupport_walk_in_barrier {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x y : Site 2} (p : (hypercubicLattice 2).Walk x y)
    (hp : ∀ z ∈ p.support, z ∉ Vc.support) :
    (latticeMinusBarrier (jec_leftRegion Vc)).Reachable x y := by
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons u w c hadj q ih =>
    have hu : u ∉ Vc.support := hp u (by simp)
    have hw : w ∉ Vc.support := hp w (by simp [SimpleGraph.Walk.support_cons])
    have htail : ∀ z ∈ q.support, z ∉ Vc.support := by
      intro z hz
      exact hp z (by rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_of_mem _ hz)
    exact (jlri_offSupport_adj_in_barrier Vc hadj hu hw).reachable.trans (ih htail)

/-- If any two inside sites are joined by a lattice path avoiding `Vc` (`hInOff`), they are
connected in the lattice cut along the boundary edges of the inside. The hypothesis `hInOff`
holds only when the inside is empty: taking `s = t` it puts every inside site off `Vc`, which
fails for a nonempty inside (`StatMech.Lattice.oc_not_hInOff`). -/
theorem jlri_inside_reachable_of_offSupport {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hInOff : ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc →
        ∃ p : (hypercubicLattice 2).Walk s t, ∀ z ∈ p.support, z ∉ Vc.support) :
    ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc →
      (latticeMinusBarrier (jec_leftRegion Vc)).Reachable s t := by
  intro s t hs ht
  obtain ⟨p, hp⟩ := hInOff s t hs ht
  exact jlri_offSupport_walk_in_barrier Vc p hp

theorem jlri_minimalLoop_sameRegion (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    {x y : Site 2} (p : (hypercubicLattice 2).Walk x y)
    (hp : ∀ z ∈ p.support, z ∉ (mpl_orbitLoop K a).support) :
    (x ∈ jec_leftRegion (mpl_orbitLoop K a) ↔ y ∈ jec_leftRegion (mpl_orbitLoop K a)) :=
  jlri_sameRegion_along_offSupport_walk (mpl_orbitLoop K a) p hp

theorem jlri_minimalLoop_no_bdEdge_off_support (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v)
    (hu : u ∉ (mpl_orbitLoop K a).support) (hv : v ∉ (mpl_orbitLoop K a).support) :
    ¬ bdEdge (jec_leftRegion (mpl_orbitLoop K a)) s(u, v) :=
  jlri_no_bdEdge_off_support (mpl_orbitLoop K a) hadj hu hv

theorem jlri_minimalLoop_offSupport_walk_in_barrier (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) {x y : Site 2} (p : (hypercubicLattice 2).Walk x y)
    (hp : ∀ z ∈ p.support, z ∉ (mpl_orbitLoop K a).support) :
    (latticeMinusBarrier (jec_leftRegion (mpl_orbitLoop K a))).Reachable x y :=
  jlri_offSupport_walk_in_barrier (mpl_orbitLoop K a) p hp

end Lattice

end StatMech
