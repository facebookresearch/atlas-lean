/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.KingFacts

/-!
# King connectivity of boundary orbits

The heads of the darts in one boundary orbit of `K` are joined by king moves in `Kᶜ`. The file also
shows that the local condition `OrbitKingTransport` fails for every finite nonempty set, so the
reduction `interfaceConnected_of_kingResidues` cannot be used for such sets.

## Main results

* `StatMech.Lattice.ifg_orbit_kingReachable`: heads of darts in one orbit are king-connected in
  `Kᶜ`.
* `StatMech.Lattice.ifg_boundaryKingConnected_of_clusterConnected`: under `InterfaceConnected K`,
  boundary darts whose heads are connected in `Kᶜ` share an orbit and their heads are
  king-connected.
* `StatMech.Lattice.ifg_exists_unreached_neighbor`: a finite nonempty set has a boundary dart whose
  head has a lattice neighbour outside the set that is the head of no boundary dart.
* `StatMech.Lattice.ifg_not_orbitKingTransport_of_finite`: `OrbitKingTransport K` is false for
  every finite nonempty `K`.
-/

@[expose] public section

open SimpleGraph Function

namespace StatMech

namespace Lattice

/-- The heads of a boundary dart and of its successor are joined by king moves in `Kᶜ`. -/
theorem ifg_dartNext_head_kingReachable (K : Set (Site 2)) (e : Dart) (he : IsBoundaryDart K e) :
    (boundaryKingGraph K).Reachable
      ⟨e.head, he.2⟩ ⟨(dartNext K e).head, (dartNext_isBoundaryDart K e he).2⟩ := by
  rcases kf_dartNext_head_kingAdj_or_eq K e with hfix | hking
  · have hsub : (⟨(dartNext K e).head, (dartNext_isBoundaryDart K e he).2⟩ : ↥(Kᶜ : Set (Site 2)))
        = ⟨e.head, he.2⟩ := Subtype.ext hfix
    rw [hsub]
  · exact (((boundaryKingGraph_adj K _ _).mpr hking)).reachable

/-- The heads of a boundary dart and of its `n`-th iterate under `dartNext K` are joined by king
moves in `Kᶜ`. -/
theorem ifg_iterate_head_kingReachable (K : Set (Site 2)) (e : Dart) (he : IsBoundaryDart K e)
    (n : ℕ) :
    (boundaryKingGraph K).Reachable
      ⟨e.head, he.2⟩ ⟨((dartNext K)^[n] e).head, (iterate_isBoundaryDart K e he n).2⟩ := by
  induction n with
  | zero => exact Reachable.refl _
  | succ m ih =>
    have hbd := iterate_isBoundaryDart K e he m
    have hstep := ifg_dartNext_head_kingReachable K ((dartNext K)^[m] e) hbd
    have htrans := ih.trans hstep
    have hval : (dartNext K ((dartNext K)^[m] e)).head = ((dartNext K)^[m + 1] e).head := by
      rw [Function.iterate_succ_apply']
    have hsub :
        (⟨(dartNext K ((dartNext K)^[m] e)).head,
            (dartNext_isBoundaryDart K ((dartNext K)^[m] e) hbd).2⟩ : ↥(Kᶜ : Set (Site 2)))
          = ⟨((dartNext K)^[m + 1] e).head, (iterate_isBoundaryDart K e he (m + 1)).2⟩ :=
      Subtype.ext hval
    rwa [hsub] at htrans

/-- Heads of boundary darts in one orbit are joined by king moves in `Kᶜ`. See also
`StatMech.Lattice.sameComponent_of_sameOrbit`, which gives a lattice path in `Kᶜ` and implies this
via `kf_boundaryKingConnected`. -/
theorem ifg_orbit_kingReachable (K : Set (Site 2)) {e f : Dart}
    (he : IsBoundaryDart K e) (hf : IsBoundaryDart K f) (h : SameOrbit K e f) :
    (boundaryKingGraph K).Reachable ⟨e.head, he.2⟩ ⟨f.head, hf.2⟩ := by
  obtain ⟨n, hn⟩ := h
  have hr := ifg_iterate_head_kingReachable K e he n
  have hval : ((dartNext K)^[n] e).head = f.head := by rw [hn]
  have hsub : (⟨((dartNext K)^[n] e).head, (iterate_isBoundaryDart K e he n).2⟩
      : ↥(Kᶜ : Set (Site 2))) = ⟨f.head, hf.2⟩ := Subtype.ext hval
  rwa [hsub] at hr

/-- Under `InterfaceConnected K`, two boundary darts whose heads are connected in `Kᶜ` lie in one
orbit, and their heads are joined by king moves in `Kᶜ`. -/
theorem ifg_boundaryKingConnected_of_clusterConnected (K : Set (Site 2))
    (hsurj : InterfaceConnected K) {e f : Dart}
    (he : IsBoundaryDart K e) (hf : IsBoundaryDart K f)
    (hcomp : ((hypercubicLattice 2).induce Kᶜ).Reachable ⟨e.head, he.2⟩ ⟨f.head, hf.2⟩) :
    SameOrbit K e f ∧
      (boundaryKingGraph K).Reachable ⟨e.head, he.2⟩ ⟨f.head, hf.2⟩ := by
  have horbit : SameOrbit K e f := hsurj e f he hf hcomp
  exact ⟨horbit, ifg_orbit_kingReachable K he hf horbit⟩

/-- If `v - c` is not a unit vector, no boundary dart of the single site `c` has head `v`. -/
theorem ifg_no_facingDart_singleton (c v : Site 2) (hv : unitWt (v - c) ≠ 1)
    (d : Dart) (hd : IsBoundaryDart ({c} : Set (Site 2)) d) : d.head ≠ v := by
  intro hhead
  apply hv
  have htail : d.tail = c := by simpa using hd.1
  have : d.dir = v - c := by rw [Dart.dir_def, hhead, htail]
  rw [← this]; exact unitWt_dir d

/-- No orbit of boundary darts of `{0}` reaches the site `(2,0)`. -/
theorem ifg_not_orbitReached_two_zero (e : Dart) :
    ¬ OrbitReached ({(0 : Site 2)} : Set (Site 2)) e (![2, 0] : Site 2) := by
  rintro ⟨d, hd, hdh, _⟩
  have hwt : unitWt ((![2, 0] : Site 2) - (0 : Site 2)) ≠ 1 := by
    simp only [sub_zero, unitWt, Fin.sum_univ_two]
    decide
  exact ifg_no_facingDart_singleton (0 : Site 2) (![2, 0] : Site 2) hwt d hd hdh

/-- `OrbitKingTransport` fails for the single site `0`: the orbit reaches `(1,0)` but not its king
neighbour `(2,0)`. See `ifg_not_orbitKingTransport_of_finite` for every finite nonempty `K`. -/
theorem ifg_not_orbitKingTransport_singleton :
    ¬ OrbitKingTransport ({(0 : Site 2)} : Set (Site 2)) := by
  intro htr
  have hg : unitWt (![1, 0] : Site 2) = 1 := by simp only [unitWt, Fin.sum_univ_two]; decide
  set e : Dart := mkDart (0 : Site 2) (![1, 0] : Site 2) hg with he_def
  have hhead : e.head = (![1, 0] : Site 2) := by rw [he_def, mkDart_head]; simp
  have htail : e.tail = (0 : Site 2) := by rw [he_def, mkDart_tail]
  have hbd : IsBoundaryDart ({(0 : Site 2)} : Set (Site 2)) e := by
    refine ⟨?_, ?_⟩
    · rw [htail]; exact Set.mem_singleton _
    · rw [hhead]; intro hc
      simp only [Set.mem_singleton_iff] at hc
      have := congrFun hc 0; simp at this
  have hou : OrbitReached ({(0 : Site 2)} : Set (Site 2)) e (![1, 0] : Site 2) := by
    have := orbitReached_self ({(0 : Site 2)} : Set (Site 2)) e hbd
    rwa [hhead] at this
  have hu : (![1, 0] : Site 2) ∉ ({(0 : Site 2)} : Set (Site 2)) := by
    intro hc; simp only [Set.mem_singleton_iff] at hc; have := congrFun hc 0; simp at this
  have hv : (![2, 0] : Site 2) ∉ ({(0 : Site 2)} : Set (Site 2)) := by
    intro hc; simp only [Set.mem_singleton_iff] at hc; have := congrFun hc 0; simp at this
  have hking : KingAdj (![1, 0] : Site 2) (![2, 0] : Site 2) := by
    refine ⟨?_, ?_⟩
    · intro hc; have := congrFun hc 0; simp at this
    · intro i; fin_cases i <;> simp
  exact ifg_not_orbitReached_two_zero e (htr e hbd hu hv hking hou)

/-- For a finite nonempty `K` there is a boundary dart `e` and a lattice neighbour `v ∉ K` of its
head that is the head of no boundary dart: take `c ∈ K` with largest first coordinate,
`e` the dart from `c` to `c + (1,0)`, and `v = c + (2,0)`. -/
theorem ifg_exists_unreached_neighbor (K : Set (Site 2)) (hK : K.Finite) (hne : K.Nonempty) :
    ∃ e : Dart, IsBoundaryDart K e ∧ ∃ v : Site 2, v ∉ K ∧ (hypercubicLattice 2).Adj e.head v ∧
      ∀ d : Dart, IsBoundaryDart K d → d.head ≠ v := by
  obtain ⟨c, hc, hmax⟩ := Set.exists_max_image K (fun z : Site 2 => z 0) hK hne
  have hnot : ∀ z : Site 2, c 0 < z 0 → z ∉ K := fun z hz hzK =>
    absurd (hmax z hzK) (not_le.mpr hz)
  have hg : unitWt (![1, 0] : Site 2) = 1 := by simp only [unitWt, Fin.sum_univ_two]; decide
  refine ⟨mkDart c ![1, 0] hg, ⟨by rw [mkDart_tail]; exact hc, hnot _ (by simp)⟩,
    c + ![1, 0] + ![1, 0],
    hnot _ (by simp only [Pi.add_apply, Matrix.cons_val_zero]; omega), ?_, ?_⟩
  · rw [mkDart_head, adj_iff_unitWt_sub, sub_add_cancel_left, unitWt_neg]; exact hg
  · intro d hd hdh
    have ht : d.tail = d.head - d.dir := by rw [Dart.dir_def]; abel
    have h0 := hmax _ hd.1
    simp only [ht, hdh] at h0
    rcases ifc_unit_four_cases d.dir (unitWt_dir d) with h | h | h | h <;>
      rw [h] at h0 <;>
      simp only [Pi.add_apply, Pi.sub_apply, Matrix.cons_val_zero] at h0 <;> omega

/-- `OrbitKingTransport K` fails for every finite nonempty `K`: the orbit of the boundary dart of
`ifg_exists_unreached_neighbor` reaches its head but not the neighbour `v`. -/
theorem ifg_not_orbitKingTransport_of_finite (K : Set (Site 2)) (hK : K.Finite)
    (hne : K.Nonempty) : ¬ OrbitKingTransport K := by
  intro htr
  obtain ⟨e, he, v, hv, hadj, hno⟩ := ifg_exists_unreached_neighbor K hK hne
  obtain ⟨d, hd, hdh, -⟩ :=
    htr e he he.2 hv (kf_hyperAdj_kingAdj _ _ hadj) (orbitReached_self K e he)
  exact hno d hd hdh

end Lattice

end StatMech
