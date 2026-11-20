/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
























































import Mathlib
import Code.Percolation.HrouteHighDim
import Code.Walls.bkm_dccthreeaxes
import Code.Probability.MengerSplice

open Set SimpleGraph SimpleGraph.Walk
open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}












noncomputable def bc3_corridorWalk (j : Fin d) (L : ℕ) :
    (hypercubicLattice d).Walk (hrHD_rayPt j 0) (hrHD_rayPt j (L : ℤ)) := by
  induction L with
  | zero => exact SimpleGraph.Walk.nil
  | succ p ih =>
      refine ih.concat ?_
      have h := hrHD_adj_rayPt j (p : ℤ)
      have he : ((p : ℤ) + 1) = ((p + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [he] at h
      exact h


lemma bc3_corridorWalk_succ (j : Fin d) (p : ℕ) :
    bc3_corridorWalk j (p + 1) =
      (bc3_corridorWalk j p).concat (by
        have h := hrHD_adj_rayPt j (p : ℤ)
        have he : ((p : ℤ) + 1) = ((p + 1 : ℕ) : ℤ) := by push_cast; ring
        rw [he] at h; exact h) := rfl


lemma bc3_corridorWalk_support_zero (j : Fin d) :
    (bc3_corridorWalk j 0).support = [hrHD_rayPt j 0] := rfl








lemma bc3_corridorWalk_mem_support (j : Fin d) (L : ℕ) (x : Site d) :
    x ∈ (bc3_corridorWalk j L).support ↔ ∃ t : ℕ, t ≤ L ∧ x = hrHD_rayPt j (t : ℤ) := by
  induction L with
  | zero =>
      rw [bc3_corridorWalk_support_zero]
      constructor
      · intro hx
        rw [List.mem_singleton] at hx
        exact ⟨0, le_rfl, by rw [hx]; norm_num⟩
      · rintro ⟨t, ht, hx⟩
        have ht0 : t = 0 := Nat.le_zero.mp ht
        rw [hx, ht0, List.mem_singleton]; norm_num
  | succ p ih =>
      rw [bc3_corridorWalk_succ, support_concat, List.mem_append]
      constructor
      · rintro (hx | hx)
        · obtain ⟨t, ht, hxt⟩ := ih.mp hx; exact ⟨t, by omega, hxt⟩
        · rw [List.mem_singleton] at hx; exact ⟨p + 1, le_rfl, hx⟩
      · rintro ⟨t, ht, hx⟩
        rcases Nat.lt_or_ge t (p + 1) with h | h
        · left; exact ih.mpr ⟨t, by omega, hx⟩
        · right
          have ht1 : t = p + 1 := by omega
          rw [List.mem_singleton, hx, ht1]


lemma bc3_corridorWalk_support_subset (j : Fin d) (L : ℕ) :
    ∀ x ∈ (bc3_corridorWalk j L).support, x ∈ corridorRay j := by
  intro x hx
  obtain ⟨t, _, rfl⟩ := (bc3_corridorWalk_mem_support j L x).mp hx
  exact rayPt_mem_corridorRay j _


lemma bc3_origin_mem_corridorWalk_support (j : Fin d) (L : ℕ) :
    (0 : Site d) ∈ (bc3_corridorWalk j L).support :=
  (bc3_corridorWalk_mem_support j L _).mpr ⟨0, Nat.zero_le _, by norm_num⟩








lemma bc3_rayPt_inj (j : Fin d) {s t : ℤ} (h : hrHD_rayPt j s = hrHD_rayPt j t) : s = t := by
  have := congrFun h j; simpa using this




lemma bc3_corridorWalk_isPath (j : Fin d) (L : ℕ) : (bc3_corridorWalk j L).IsPath := by
  induction L with
  | zero => simp [bc3_corridorWalk]
  | succ p ih =>
      rw [bc3_corridorWalk_succ, SimpleGraph.Walk.isPath_def, support_concat, List.nodup_append]
      refine ⟨(SimpleGraph.Walk.isPath_def _).mp ih, by simp, ?_⟩
      intro a ha b hb
      rw [List.mem_singleton] at hb
      subst hb
      intro hab
      rw [hab] at ha
      obtain ⟨t, ht, het⟩ := (bc3_corridorWalk_mem_support j p _).mp ha
      have hpt : ((p + 1 : ℕ) : ℤ) = (t : ℤ) := bc3_rayPt_inj j het
      omega







lemma bc3_corridorEdges_mono (j : Fin d) {L L' : ℕ} (h : L ≤ L') :
    hrHD_corridorEdges j L ⊆ hrHD_corridorEdges j L' := by
  rw [hrHD_corridorEdges, hrHD_corridorEdges]
  exact Finset.image_subset_image (Finset.range_subset_range.mpr h)




lemma bc3_corridorWalk_edges_mem (j : Fin d) (L : ℕ) :
    ∀ e ∈ (bc3_corridorWalk j L).edges, e ∈ hrHD_corridorEdges j L := by
  induction L with
  | zero => intro e he; simp [bc3_corridorWalk] at he
  | succ p ih =>
      intro e he
      rw [bc3_corridorWalk_succ, edges_concat, List.concat_eq_append, List.mem_append] at he
      rcases he with he | he
      · exact bc3_corridorEdges_mono j (by omega) (ih e he)
      · rw [List.mem_singleton] at he
        rw [he]
        exact hrHD_mem_corridorEdges (Nat.lt_succ_self p)










theorem bc3_corridorWalk_cross_eq_origin {i j : Fin d} (h : i ≠ j) (L L' : ℕ) {x : Site d}
    (hxi : x ∈ (bc3_corridorWalk i L).support)
    (hxj : x ∈ (bc3_corridorWalk j L').support) : x = 0 := by
  have hi := bc3_corridorWalk_support_subset i L x hxi
  have hj := bc3_corridorWalk_support_subset j L' x hxj
  have : x ∈ ({(0 : Site d)} : Set (Site d)) := by
    rw [← bkm_corridorRay_inter_eq_origin h]; exact ⟨hi, hj⟩
  exact Set.mem_singleton_iff.mp this




theorem bc3_corridorWalk_disjoint_off_origin {i j : Fin d} (h : i ≠ j) (L L' : ℕ) {x : Site d}
    (hx0 : x ≠ 0) (hxi : x ∈ (bc3_corridorWalk i L).support)
    (hxj : x ∈ (bc3_corridorWalk j L').support) : False :=
  hx0 (bc3_corridorWalk_cross_eq_origin h L L' hxi hxj)







theorem bc3_corridorFamily_disjoint_off_origin {ι : Type*} (ax : ι → Fin d) (len : ι → ℕ)
    (hax : Function.Injective ax) {i i' : ι} (hii : i ≠ i') {x : Site d} (hx0 : x ≠ 0)
    (hxi : x ∈ (bc3_corridorWalk (ax i) (len i)).support)
    (hxi' : x ∈ (bc3_corridorWalk (ax i') (len i')).support) : False :=
  bc3_corridorWalk_disjoint_off_origin (fun he => hii (hax he)) _ _ hx0 hxi hxi'












theorem bc3_ray_disjoint :
    ∀ {i j : Fin d}, i ≠ j → ∀ L L' : ℕ,
      (∀ s t : ℤ, s ≠ 0 → (hrHD_rayPt i s : Site d) ≠ hrHD_rayPt j t) ∧
      (bc3_corridorWalk i L).IsPath ∧
      (∀ x : Site d, x ∈ (bc3_corridorWalk i L).support →
        x ∈ (bc3_corridorWalk j L').support → x = 0) := by
  intro i j h L L'
  exact ⟨fun _ _ hs => hrHD_rayPt_disjoint_of_ne h hs,
     bc3_corridorWalk_isPath i L,
     fun x hxi hxj => bc3_corridorWalk_cross_eq_origin h L L' hxi hxj⟩










lemma bc3_unit_mem_corridorWalk_support (j : Fin d) {L : ℕ} (hL : 1 ≤ L) :
    (hrHD_rayPt j 1 : Site d) ∈ (bc3_corridorWalk j L).support ∧
      (hrHD_rayPt j 1 : Site d) ≠ 0 := by
  refine ⟨(bc3_corridorWalk_mem_support j L _).mpr ⟨1, hL, by norm_num⟩, ?_⟩
  rw [Ne, hrHD_rayPt_eq_zero_iff]; exact one_ne_zero




theorem bc3_ray_disjoint_nonvacuous (hd : 2 ≤ d) :
    ∃ i j : Fin d, i ≠ j ∧
      (bc3_corridorWalk i 1).IsPath ∧ (bc3_corridorWalk j 1).IsPath ∧
      (hrHD_rayPt i 1 : Site d) ≠ 0 ∧ (hrHD_rayPt j 1 : Site d) ≠ 0 ∧
      (hrHD_rayPt i 1 : Site d) ∈ (bc3_corridorWalk i 1).support ∧
      (hrHD_rayPt j 1 : Site d) ∈ (bc3_corridorWalk j 1).support ∧
      (∀ x : Site d, x ∈ (bc3_corridorWalk i 1).support →
        x ∈ (bc3_corridorWalk j 1).support → x = 0) := by
  have hij : (⟨0, by omega⟩ : Fin d) ≠ ⟨1, by omega⟩ := by intro h; simp [Fin.ext_iff] at h
  refine ⟨⟨0, by omega⟩, ⟨1, by omega⟩, hij,
    bc3_corridorWalk_isPath _ 1, bc3_corridorWalk_isPath _ 1, ?_, ?_, ?_, ?_, ?_⟩
  · exact (bc3_unit_mem_corridorWalk_support _ le_rfl).2
  · exact (bc3_unit_mem_corridorWalk_support _ le_rfl).2
  · exact (bc3_unit_mem_corridorWalk_support _ le_rfl).1
  · exact (bc3_unit_mem_corridorWalk_support _ le_rfl).1
  · exact fun x hxi hxj => bc3_corridorWalk_cross_eq_origin hij 1 1 hxi hxj

end StatMech.Walls
