/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.InteriorOrientation

/-!
# Sites outside a set reach the exterior off its boundary loop

Let `mpl_orbitLoop K a` be the face loop of a boundary orbit of a set `K` of sites. The loop passes
through sites outside `K` (for the unit cell, the site `(0, -1)`), so asking every site outside `K`
to escape without touching the loop is false (`exc_oldExteriorConnected_false`). The corrected
hypothesis `exc_OffSupportReachesExterior` asks it only for sites outside `K` and off the loop:
each such site is joined, avoiding the loop, to the exterior of a box containing the loop. Together
with `exc_SupportOddInK` (sites of the loop with odd ray count lie in `K`) it gives the inclusion of
the inside of the loop in `K`.

## Main definitions

* `StatMech.Lattice.exc_OffSupportReachesExterior K a`: every site outside `K` and off the loop is
  joined off the loop to the exterior of a box containing the loop.
* `StatMech.Lattice.exc_SupportOddInK K a`: every site of the loop with odd ray count lies in `K`.

## Main results

* `StatMech.Lattice.exc_oldExteriorConnected_false`: `ior_ExteriorConnected` fails for the unit
  cell.
* `StatMech.Lattice.exc_exterior_reaches_farLeft`: a site outside a box containing `F` is joined,
  avoiding `F`, to a site left of `F`.
* `StatMech.Lattice.exc_offSupport_of_reaches`: under `exc_OffSupportReachesExterior`, sites outside
  `K` and off the loop reach a site left of the loop without touching it.
* `StatMech.Lattice.exc_interiorSubset_of_reaches_and_support`: the two hypotheses give
  `eaw_InteriorSubset K a`.
-/

@[expose] public section

open Set SimpleGraph

namespace StatMech

namespace Lattice

/-- The site `(0, -1)` lies on the face loop of the unit cell. -/
theorem exc_unitCell_offK_on_support :
    (![0, -1] : Site 2) ∈ (mpl_orbitLoop unitCell ucBase).support := by
  rw [mpl_orbitLoop_support]
  have hedge : s((![0, 0] : Site 2), ![0, -1]) ∈ (mpl_orbitFaceLoop unitCell ucBase).edges := by
    rw [mpl_unitCell_faceLoop_edges]; simp
  exact (mpl_orbitFaceLoop unitCell ucBase).snd_mem_support_of_mem_edges hedge

/-- The site `(0, -1)` is not in the unit cell. -/
theorem exc_unitCell_offK_notMem : (![0, -1] : Site 2) ∉ unitCell := by
  rw [unitCell, Set.mem_singleton_iff]
  intro hh
  have := congrFun hh 1
  simp at this

/-- `ior_ExteriorConnected` fails for the unit cell: the site `(0, -1)` lies outside the unit cell
and on its face loop, so no path starting there avoids the loop. -/
theorem exc_oldExteriorConnected_false : ¬ ior_ExteriorConnected unitCell ucBase := by
  intro h
  obtain ⟨z0, p, hp, _⟩ := h _ exc_unitCell_offK_notMem
  exact hp _ p.start_mem_support exc_unitCell_offK_on_support

/-- Reachability in the lattice induced on `Fᶜ` gives a lattice walk avoiding `F`. See also
`StatMech.Lattice.offSupport_reachable_iff_offSupportWalk` for the support of a closed walk. -/
theorem exc_reachable_compl_to_offSupport_walk (F : Set (Site 2)) {x y : Site 2}
    (hx : x ∈ Fᶜ) (hy : y ∈ Fᶜ)
    (h : ((hypercubicLattice 2).induce Fᶜ).Reachable ⟨x, hx⟩ ⟨y, hy⟩) :
    ∃ p : (hypercubicLattice 2).Walk x y, ∀ w ∈ p.support, w ∉ F := by
  obtain ⟨q⟩ := h
  refine ⟨q.map (SimpleGraph.Embedding.induce (G := hypercubicLattice 2) Fᶜ).toHom, ?_⟩
  intro w hw
  have hw2 : w ∈ List.map (⇑(SimpleGraph.Embedding.induce (G := hypercubicLattice 2) Fᶜ).toHom)
      q.support := by rwa [← SimpleGraph.Walk.support_map]
  obtain ⟨v, _, hvw⟩ := List.mem_map.mp hw2
  rw [← hvw]; exact v.2

/-- The site `(-(R + 1), 0)` lies outside the box `[-R, R]²`. -/
theorem exc_farLeft_mem_exterior (R : ℕ) : (![-((R : ℤ) + 1), 0] : Site 2) ∈ exterior 2 R := by
  refine ⟨0, ?_⟩
  change R < ((-((R : ℤ) + 1))).natAbs
  rw [show (-((R : ℤ) + 1)).natAbs = R + 1 by rw [Int.natAbs_eq_iff]; right; push_cast; ring]
  omega

/-- If `F` lies in the box `[-R, R]²`, every site outside the box is joined, by a lattice path
avoiding `F`, to a site weakly left of every site of `F`. -/
theorem exc_exterior_reaches_farLeft (F : Set (Site 2)) (R : ℕ) (hR : F ⊆ box 2 R)
    (z : Site 2) (hz : z ∈ exterior 2 R) :
    ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0,
      (∀ w ∈ p.support, w ∉ F) ∧ (∀ q ∈ F, z0 0 ≤ q 0) := by
  set z0 : Site 2 := ![-((R : ℤ) + 1), 0] with hz0
  have hz0ext : z0 ∈ exterior 2 R := exc_farLeft_mem_exterior R
  have hsub : exterior 2 R ⊆ Fᶜ := exterior_subset_compl F R hR
  have hreach := box_exterior_connected R (by norm_num) z z0 hz hz0ext
  have hreachF : ((hypercubicLattice 2).induce Fᶜ).Reachable ⟨z, hsub hz⟩ ⟨z0, hsub hz0ext⟩ := by
    have := hreach.map ((hypercubicLattice 2).induceHomOfLE hsub).toHom
    exact this
  obtain ⟨p, hp⟩ := exc_reachable_compl_to_offSupport_walk F (hsub hz) (hsub hz0ext) hreachF
  refine ⟨z0, p, hp, ?_⟩
  intro qq hqq
  have hqbox := hR hqq
  rw [mem_box] at hqbox
  simp only [hz0, Matrix.cons_val_zero]
  have hnat : (qq 0).natAbs ≤ R := hqbox 0
  have h2 : |qq 0| ≤ (R : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast hnat
  rw [abs_le] at h2; omega

/-- The sites of the face loop lie in some box `[-R, R]²`. -/
theorem exc_exists_loopSupportBox (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    ∃ R : ℕ, ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R :=
  finite_subset_box _ (List.finite_toSet _)

/-- For some box `[-R, R]²` containing the face loop of the orbit of `a`, every site outside `K`
and off the loop is joined, by a lattice path avoiding the loop, to a site outside the box. -/
def exc_OffSupportReachesExterior (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    Prop :=
  ∃ R : ℕ, ∃ hRbox : ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R,
    ∀ z, z ∉ K → z ∉ (mpl_orbitLoop K a).support →
      ∃ hz : z ∈ ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2))ᶜ,
        ∃ e : Site 2, ∃ he : e ∈ exterior 2 R,
          ((hypercubicLattice 2).induce
              ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2))ᶜ).Reachable
            ⟨z, hz⟩ ⟨e, exterior_subset_compl _ R hRbox he⟩

/-- Under `exc_OffSupportReachesExterior`, every site outside `K` and off the face loop is joined,
by a path avoiding the loop, to a site weakly left of the whole loop. -/
theorem exc_offSupport_of_reaches (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (h : exc_OffSupportReachesExterior K a) :
    ∀ z, z ∉ K → z ∉ (mpl_orbitLoop K a).support →
      ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0,
        (∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support) ∧
        (∀ q ∈ (mpl_orbitLoop K a).support, z0 0 ≤ q 0) := by
  obtain ⟨R, hRbox, hreach⟩ := h
  intro z hzK hzsupp
  set F : Set (Site 2) := {z | z ∈ (mpl_orbitLoop K a).support} with hF
  obtain ⟨hz, e, he, hreach_ze⟩ := hreach z hzK hzsupp
  obtain ⟨p1, hp1⟩ := exc_reachable_compl_to_offSupport_walk F hz
    (exterior_subset_compl _ R hRbox he) hreach_ze
  obtain ⟨z0, p2, hp2, hfar⟩ := exc_exterior_reaches_farLeft F R hRbox e he
  refine ⟨z0, p1.append p2, ?_, ?_⟩
  · intro w hw
    rw [SimpleGraph.Walk.mem_support_append_iff] at hw
    rcases hw with h | h
    · exact hp1 w h
    · exact hp2 w h
  · exact hfar

/-- Every site of the face loop with odd ray count lies in `K`. -/
def exc_SupportOddInK (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) : Prop :=
  ∀ z ∈ (mpl_orbitLoop K a).support, ¬ Even (jec_rayCount z (mpl_orbitLoop K a)) → z ∈ K

/-- If sites off the loop and outside `K` escape to the exterior (`exc_OffSupportReachesExterior`)
and sites of the loop with odd ray count lie in `K` (`exc_SupportOddInK`), then every site of odd
ray count lies in `K`: the inside of the face loop is contained in `K`. -/
theorem exc_interiorSubset_of_reaches_and_support (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (hoff : exc_OffSupportReachesExterior K a)
    (hsupp : exc_SupportOddInK K a) :
    eaw_InteriorSubset K a := by
  intro z hodd
  by_cases hzsupp : z ∈ (mpl_orbitLoop K a).support
  · exact hsupp z hzsupp hodd
  · by_contra hzK
    obtain ⟨z0, p, hp, hfar⟩ := exc_offSupport_of_reaches K a hoff z hzK hzsupp
    have hbase : Even (jec_rayCount z0 (mpl_orbitLoop K a)) := by
      rw [jec_rayCount_eq_zero_of_right z0 (mpl_orbitLoop K a) (fun q hq => hfar q hq)]
      exact Nat.even_iff.mpr rfl
    exact hodd ((oee_rayParity_const_along_walk (mpl_orbitLoop K a) p hp).mpr hbase)

/-- The unit cell satisfies `exc_SupportOddInK`. -/
theorem exc_unitCell_supportOddInK : exc_SupportOddInK unitCell ucBase := by
  intro z _ hodd
  exact eaw_unitCell_interiorSubset z hodd

end Lattice

end StatMech
