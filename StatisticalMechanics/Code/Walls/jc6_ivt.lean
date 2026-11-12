/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






















































































import Mathlib
import Code.Lattice.PathVisitsRow
import Code.Lattice.OrbitLoopBridge

open Set SimpleGraph Function

namespace StatMech

namespace Walls

open StatMech.Lattice















theorem jc6_walk_step_coord_le_one {a b : Site 2} (w : (hypercubicLattice 2).Walk a b)
    {i : ℕ} (hi : i < w.length) (k : Fin 2) :
    ((w.getVert i) k - (w.getVert (i + 1)) k).natAbs ≤ 1 :=
  pvr_adj_coord_diff_le_one (w.adj_getVert_succ hi) k
















theorem jc6_walk_visits_row {a b : Site 2} (w : (hypercubicLattice 2).Walk a b)
    (r : ℤ) (hr1 : min (a 1) (b 1) ≤ r) (hr2 : r ≤ max (a 1) (b 1)) :
    ∃ p ∈ w.support, p 1 = r := by
  rcases le_total (a 1) (b 1) with h | h
  · exact pvr_visits_every_row w rfl rfl h r (by omega) (by omega)
  · obtain ⟨p, hp, hpr⟩ := pvr_visits_every_row w.reverse rfl rfl h r (by omega) (by omega)
    exact ⟨p, by rwa [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hp, hpr⟩




theorem jc6_walk_visits_col {a b : Site 2} (w : (hypercubicLattice 2).Walk a b)
    (r : ℤ) (hr1 : min (a 0) (b 0) ≤ r) (hr2 : r ≤ max (a 0) (b 0)) :
    ∃ p ∈ w.support, p 0 = r := by
  rcases le_total (a 0) (b 0) with h | h
  · exact pvr_visits_every_col w rfl rfl h r (by omega) (by omega)
  · obtain ⟨p, hp, hpr⟩ := pvr_visits_every_col w.reverse rfl rfl h r (by omega) (by omega)
    exact ⟨p, by rwa [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hp, hpr⟩




theorem jc6_walk_no_row_skip {a b : Site 2} (w : (hypercubicLattice 2).Walk a b)
    (r : ℤ) (hr1 : min (a 1) (b 1) ≤ r) (hr2 : r ≤ max (a 1) (b 1)) :
    ∃ p ∈ w.support, p 1 = r :=
  jc6_walk_visits_row w r hr1 hr2
















theorem jc6_walk_cannot_hop {a b : Site 2} (w : (hypercubicLattice 2).Walk a b)
    (r : ℤ) (hmiss : ∀ p ∈ w.support, p 1 ≠ r) :
    r < min (a 1) (b 1) ∨ max (a 1) (b 1) < r := by
  by_contra hc
  rw [not_or, not_lt, not_lt] at hc
  obtain ⟨p, hp, hpr⟩ := jc6_walk_visits_row w r hc.1 hc.2
  exact hmiss p hp hpr
















theorem jc6_subWalk_visits_row {a b : Site 2} (w : (hypercubicLattice 2).Walk a b)
    {u v : Site 2} (hu : u ∈ w.support) (hv : v ∈ (w.dropUntil u hu).support)
    (r : ℤ) (hr1 : min (u 1) (v 1) ≤ r) (hr2 : r ≤ max (u 1) (v 1)) :
    ∃ p ∈ w.support, p 1 = r := by
  
  obtain ⟨p, hps, hpr⟩ := jc6_walk_visits_row ((w.dropUntil u hu).takeUntil v hv) r hr1 hr2
  
  have h1 : ((w.dropUntil u hu).takeUntil v hv).support ⊆ (w.dropUntil u hu).support :=
    (w.dropUntil u hu).support_takeUntil_subset_support hv
  have h2 : (w.dropUntil u hu).support ⊆ w.support := Walk.support_dropUntil_subset w hu
  exact ⟨p, h2 (h1 hps), hpr⟩














theorem jc6_orbit_step_coord_le_one (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) {i : ℕ} (hi : i < (olb_orbitLoop K hK e he).length) (k : Fin 2) :
    (((olb_orbitLoop K hK e he).getVert i) k - ((olb_orbitLoop K hK e he).getVert (i + 1)) k).natAbs
      ≤ 1 :=
  jc6_walk_step_coord_le_one (olb_orbitLoop K hK e he) hi k













theorem jc6_orbit_subStretch_visits_row (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) {u v : Site 2}
    (hu : u ∈ (olb_orbitLoop K hK e he).support)
    (hv : v ∈ ((olb_orbitLoop K hK e he).dropUntil u hu).support)
    (r : ℤ) (hr1 : min (u 1) (v 1) ≤ r) (hr2 : r ≤ max (u 1) (v 1)) :
    ∃ p ∈ (olb_orbitLoop K hK e he).support, p 1 = r :=
  jc6_subWalk_visits_row (olb_orbitLoop K hK e he) hu hv r hr1 hr2











theorem jc6_orbit_cannot_hop_over_cell (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) {u v : Site 2}
    (hu : u ∈ (olb_orbitLoop K hK e he).support)
    (hv : v ∈ ((olb_orbitLoop K hK e he).dropUntil u hu).support)
    (f : Site 2) (hf1 : min (u 1) (v 1) ≤ f 1) (hf2 : f 1 ≤ max (u 1) (v 1)) :
    ∃ p ∈ (olb_orbitLoop K hK e he).support, p 1 = f 1 :=
  jc6_orbit_subStretch_visits_row K hK e he hu hv (f 1) hf1 hf2








theorem jc6_orbit_subStretch_cannot_hop (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) {u v : Site 2}
    (hu : u ∈ (olb_orbitLoop K hK e he).support)
    (hv : v ∈ ((olb_orbitLoop K hK e he).dropUntil u hu).support)
    (f : Site 2)
    (hmiss : ∀ p ∈ (((olb_orbitLoop K hK e he).dropUntil u hu).takeUntil v hv).support,
      p 1 ≠ f 1) :
    f 1 < min (u 1) (v 1) ∨ max (u 1) (v 1) < f 1 :=
  
  
  jc6_walk_cannot_hop (((olb_orbitLoop K hK e he).dropUntil u hu).takeUntil v hv) (f 1) hmiss








noncomputable def jc6_vArc : (hypercubicLattice 2).Walk (![0, 0] : Site 2) (![0, 2] : Site 2) :=
  (SimpleGraph.Walk.nil.cons (by
      rw [hypercubicLattice_adj]; rw [Fin.sum_univ_two]; simp)
    : (hypercubicLattice 2).Walk (![0, 1] : Site 2) (![0, 2] : Site 2)).cons
    (by rw [hypercubicLattice_adj]; rw [Fin.sum_univ_two]; simp)





theorem jc6_ivt_nonvacuous_middleRow :
    ∃ p ∈ jc6_vArc.support, p 1 = 1 := by
  apply jc6_walk_visits_row jc6_vArc 1
  · simp only [Matrix.cons_val_one, Matrix.cons_val_zero]; norm_num
  · simp only [Matrix.cons_val_one, Matrix.cons_val_zero]; norm_num





theorem jc6_ivt_nonvacuous_cannotHop :
    (5 : ℤ) < min ((![0, 0] : Site 2) 1) ((![0, 2] : Site 2) 1) ∨
      max ((![0, 0] : Site 2) 1) ((![0, 2] : Site 2) 1) < (5 : ℤ) := by
  apply jc6_walk_cannot_hop jc6_vArc 5
  
  intro p hp
  
  simp only [jc6_vArc, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
    List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;>
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero] <;> norm_num


































end Walls

end StatMech
