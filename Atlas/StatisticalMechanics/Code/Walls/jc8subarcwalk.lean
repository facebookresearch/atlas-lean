/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/























































import Mathlib
import Code.Lattice.OrbitEncloses
import Code.Lattice.OrbitLoopBridge
import Code.Walls.jc7getverteqdartface
import Code.Walls.jc7loopiscycle

open SimpleGraph Function Set

namespace StatMech

namespace Walls

open StatMech.Lattice













theorem jc8_loop_isCycle (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e)
    (hp : 3 ≤ jc7_choosePeriod K hK e he)
    (hinj : Set.InjOn (fun k => dartFace ((dartNext K)^[k] e))
      (Set.Iio (jc7_choosePeriod K hK e he))) :
    (olb_orbitLoop K hK e he).IsCycle :=
  jc7_LoopIsCycle K hK e he hp hinj












theorem jc8_substretch_start (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) {u v : Site 2}
    (hu : u ∈ (olb_orbitLoop K hK e he).support)
    (hv : v ∈ ((olb_orbitLoop K hK e he).dropUntil u hu).support) :
    (((olb_orbitLoop K hK e he).dropUntil u hu).takeUntil v hv).getVert 0 = u := by
  rw [Walk.getVert_zero]



theorem jc8_substretch_finish (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) {u v : Site 2}
    (hu : u ∈ (olb_orbitLoop K hK e he).support)
    (hv : v ∈ ((olb_orbitLoop K hK e he).dropUntil u hu).support) :
    (((olb_orbitLoop K hK e he).dropUntil u hu).takeUntil v hv).getVert
      (((olb_orbitLoop K hK e he).dropUntil u hu).takeUntil v hv).length = v := by
  rw [Walk.getVert_length]






theorem jc8_substretch_adj_getVert_succ (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) {u v : Site 2}
    (hu : u ∈ (olb_orbitLoop K hK e he).support)
    (hv : v ∈ ((olb_orbitLoop K hK e he).dropUntil u hu).support) {i : ℕ}
    (hi : i < (((olb_orbitLoop K hK e he).dropUntil u hu).takeUntil v hv).length) :
    (hypercubicLattice 2).Adj
      ((((olb_orbitLoop K hK e he).dropUntil u hu).takeUntil v hv).getVert i)
      ((((olb_orbitLoop K hK e he).dropUntil u hu).takeUntil v hv).getVert (i + 1)) :=
  Walk.adj_getVert_succ _ hi






theorem jc8_substretch_isSubwalk (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) {u v : Site 2}
    (hu : u ∈ (olb_orbitLoop K hK e he).support)
    (hv : v ∈ ((olb_orbitLoop K hK e he).dropUntil u hu).support) :
    (((olb_orbitLoop K hK e he).dropUntil u hu).takeUntil v hv).IsSubwalk
      (olb_orbitLoop K hK e he) :=
  (Walk.isSubwalk_takeUntil _ hv).trans (Walk.isSubwalk_dropUntil _ hu)













theorem jc8_dropUntil_support_sublist (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) {u : Site 2}
    (hu : u ∈ (olb_orbitLoop K hK e he).support) :
    ((olb_orbitLoop K hK e he).dropUntil u hu).support.Sublist
      (olb_orbitLoop K hK e he).support := by
  rw [Walk.dropUntil_eq_drop, Walk.support_copy, Walk.drop_support_eq_support_drop_min]
  exact List.drop_sublist _ _









theorem jc8_substretch_support_sublist (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) {u v : Site 2}
    (hu : u ∈ (olb_orbitLoop K hK e he).support)
    (hv : v ∈ ((olb_orbitLoop K hK e he).dropUntil u hu).support) :
    (((olb_orbitLoop K hK e he).dropUntil u hu).takeUntil v hv).support.Sublist
      (olb_orbitLoop K hK e he).support :=
  (Walk.support_takeUntil_prefix_support _ hv).sublist.trans
    (jc8_dropUntil_support_sublist K hK e he hu)





theorem jc8_substretch_support_subset (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) {u v : Site 2}
    (hu : u ∈ (olb_orbitLoop K hK e he).support)
    (hv : v ∈ ((olb_orbitLoop K hK e he).dropUntil u hu).support) :
    (((olb_orbitLoop K hK e he).dropUntil u hu).takeUntil v hv).support ⊆
      (olb_orbitLoop K hK e he).support := fun _ hx =>
  Walk.support_dropUntil_subset _ hu (Walk.support_takeUntil_subset_support _ hv hx)



theorem jc8_substretch_darts_subset (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) {u v : Site 2}
    (hu : u ∈ (olb_orbitLoop K hK e he).support)
    (hv : v ∈ ((olb_orbitLoop K hK e he).dropUntil u hu).support) :
    (((olb_orbitLoop K hK e he).dropUntil u hu).takeUntil v hv).darts ⊆
      (olb_orbitLoop K hK e he).darts := fun _ hx =>
  Walk.darts_dropUntil_subset _ hu (Walk.darts_takeUntil_subset _ hv hx)



theorem jc8_substretch_edges_subset (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) {u v : Site 2}
    (hu : u ∈ (olb_orbitLoop K hK e he).support)
    (hv : v ∈ ((olb_orbitLoop K hK e he).dropUntil u hu).support) :
    (((olb_orbitLoop K hK e he).dropUntil u hu).takeUntil v hv).edges ⊆
      (olb_orbitLoop K hK e he).edges := fun _ hx =>
  Walk.edges_dropUntil_subset _ hu (Walk.edges_takeUntil_subset _ hv hx)
























theorem jc8_getVert_dropUntil (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) {u : Site 2}
    (hu : u ∈ (olb_orbitLoop K hK e he).support) (k : ℕ) :
    ((olb_orbitLoop K hK e he).dropUntil u hu).getVert k =
      (olb_orbitLoop K hK e he).getVert ((olb_orbitLoop K hK e he).support.idxOf u + k) := by
  rw [Walk.dropUntil_eq_drop, Walk.getVert_copy, Walk.drop_getVert]









theorem jc8_idxOf_add_le_length (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) {u v : Site 2}
    (hu : u ∈ (olb_orbitLoop K hK e he).support)
    (hv : v ∈ ((olb_orbitLoop K hK e he).dropUntil u hu).support) (k : ℕ)
    (hk : k ≤ (((olb_orbitLoop K hK e he).dropUntil u hu).takeUntil v hv).length) :
    (olb_orbitLoop K hK e he).support.idxOf u + k ≤ (olb_orbitLoop K hK e he).length := by
  have h1 : (((olb_orbitLoop K hK e he).dropUntil u hu).takeUntil v hv).length
      ≤ ((olb_orbitLoop K hK e he).dropUntil u hu).length :=
    Walk.length_takeUntil_le _ hv
  have h2 : ((olb_orbitLoop K hK e he).dropUntil u hu).length
      = (olb_orbitLoop K hK e he).length - (olb_orbitLoop K hK e he).support.idxOf u :=
    Walk.length_dropUntil _ hu
  have h3 : (olb_orbitLoop K hK e he).support.idxOf u ≤ (olb_orbitLoop K hK e he).length := by
    have := List.idxOf_lt_length_of_mem hu
    rw [Walk.length_support] at this
    omega
  omega












theorem jc8_substretch_getVert_eq_dartFace (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) {u v : Site 2}
    (hu : u ∈ (olb_orbitLoop K hK e he).support)
    (hv : v ∈ ((olb_orbitLoop K hK e he).dropUntil u hu).support) (k : ℕ)
    (hk : k ≤ (((olb_orbitLoop K hK e he).dropUntil u hu).takeUntil v hv).length) :
    (((olb_orbitLoop K hK e he).dropUntil u hu).takeUntil v hv).getVert k =
      dartFace ((dartNext K)^[(olb_orbitLoop K hK e he).support.idxOf u + k] e) := by
  rw [Walk.getVert_takeUntil hv hk, jc8_getVert_dropUntil K hK e he hu k,
    jc7_getVert_eq_dartFace K hK e he _ (jc8_idxOf_add_le_length K hK e he hu hv k hk)]















theorem jc8_substretch_support_eq_map (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) {u v : Site 2}
    (hu : u ∈ (olb_orbitLoop K hK e he).support)
    (hv : v ∈ ((olb_orbitLoop K hK e he).dropUntil u hu).support) :
    (((olb_orbitLoop K hK e he).dropUntil u hu).takeUntil v hv).support =
      (List.range
        ((((olb_orbitLoop K hK e he).dropUntil u hu).takeUntil v hv).length + 1)).map
        (fun k => dartFace ((dartNext K)^[(olb_orbitLoop K hK e he).support.idxOf u + k] e)) := by
  apply List.ext_getElem
  · rw [Walk.length_support, List.length_map, List.length_range]
  · intro n h1 _h2
    rw [Walk.length_support] at h1
    rw [List.getElem_map, List.getElem_range,
      ← Walk.getVert_eq_support_getElem _ (by omega)]
    exact jc8_substretch_getVert_eq_dartFace K hK e he hu hv n (by omega)












theorem jc8_idxOf_eq_takeUntil_length (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) {u : Site 2}
    (hu : u ∈ (olb_orbitLoop K hK e he).support) :
    (olb_orbitLoop K hK e he).support.idxOf u = ((olb_orbitLoop K hK e he).takeUntil u hu).length :=
  (Walk.length_takeUntil _ hu).symm





theorem jc8_substretch_getVert_zero_eq_dartFace (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) {u v : Site 2}
    (hu : u ∈ (olb_orbitLoop K hK e he).support)
    (hv : v ∈ ((olb_orbitLoop K hK e he).dropUntil u hu).support) :
    (((olb_orbitLoop K hK e he).dropUntil u hu).takeUntil v hv).getVert 0 =
      dartFace ((dartNext K)^[(olb_orbitLoop K hK e he).support.idxOf u] e) := by
  have := jc8_substretch_getVert_eq_dartFace K hK e he hu hv 0 (Nat.zero_le _)
  simpa using this







































end Walls

end StatMech
