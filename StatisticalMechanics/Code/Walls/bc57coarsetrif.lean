/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












































































import Mathlib
import Code.Walls.bc56menger

open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation











theorem bc57_offAxisLine_no_reachesNbr :
    ¬ bc56_ClusterReachesNbr bc56_offAxisLine (bc56_lp 0) := by
  rintro ⟨a, hadj, hmem, _, _⟩
  exact bc56_offAxisLine_no_originNbr a hadj hmem









def bc57_pt (k h : ℤ) : Site 2 := ![k, h]

@[simp] theorem bc57_pt_fst (k h : ℤ) : (bc57_pt k h) 0 = k := by simp [bc57_pt]
@[simp] theorem bc57_pt_snd (k h : ℤ) : (bc57_pt k h) 1 = h := by simp [bc57_pt]

theorem bc57_pt_inj {k k' h h' : ℤ} (hk : k = k') (hh : h = h') :
    bc57_pt k h = bc57_pt k' h' := by rw [hk, hh]


theorem bc57_pt_adj (k h : ℤ) :
    (hypercubicLattice 2).Adj (bc57_pt k h) (bc57_pt (k + 1) h) := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp [bc57_pt]

open Classical in



noncomputable def bc57_evenLines : ConfigSpace (Sym2 (Site 2)) :=
  fun e => if (∃ k m : ℤ, e = s(bc57_pt k (2 * m), bc57_pt (k + 1) (2 * m))) then true else false


theorem bc57_evenLines_open (k m : ℤ) :
    bc57_evenLines s(bc57_pt k (2 * m), bc57_pt (k + 1) (2 * m)) = true := by
  classical
  rw [bc57_evenLines, if_pos]; exact ⟨k, m, rfl⟩





theorem bc57_connected_pos (m : ℤ) (j : ℕ) :
    Connected 2 bc57_evenLines (bc57_pt 0 (2 * m)) (bc57_pt (j : ℤ) (2 * m)) := by
  induction j with
  | zero => simpa using connected_refl _ (bc57_pt 0 (2 * m))
  | succ i ih =>
    have step : Connected 2 bc57_evenLines (bc57_pt (i : ℤ) (2 * m))
        (bc57_pt ((i : ℤ) + 1) (2 * m)) :=
      IsOpenEdge.connected ⟨bc57_pt_adj (i : ℤ) (2 * m), bc57_evenLines_open (i : ℤ) m⟩
    have hcast : ((i + 1 : ℕ) : ℤ) = (i : ℤ) + 1 := by push_cast; ring
    rw [hcast]; exact ih.trans step






theorem bc57_height_step {h : ℤ} {u v : Site 2} (hu : u 1 = h)
    (hadj : (openSubgraph 2 bc57_evenLines).Adj u v) : v 1 = h := by
  classical
  obtain ⟨_, hopen⟩ := hadj
  rw [bc57_evenLines] at hopen
  by_cases hk : ∃ k m : ℤ, s(u, v) = s(bc57_pt k (2 * m), bc57_pt (k + 1) (2 * m))
  · obtain ⟨k, m, hkeq⟩ := hk
    rw [Sym2.eq_iff] at hkeq
    rcases hkeq with ⟨hu', hv'⟩ | ⟨hu', hv'⟩
    · rw [hv', bc57_pt_snd]; rw [hu', bc57_pt_snd] at hu; omega
    · rw [hv', bc57_pt_snd]; rw [hu', bc57_pt_snd] at hu; omega
  · rw [if_neg hk] at hopen; exact absurd hopen (by decide)



theorem bc57_height_invariant {h : ℤ} {u y : Site 2} (hu : u 1 = h)
    (hconn : Connected 2 bc57_evenLines u y) : y 1 = h := by
  obtain ⟨w⟩ := hconn
  induction w with
  | nil => exact hu
  | @cons a b c hab w' ih => exact ih (bc57_height_step hu hab)




theorem bc57_pt_outside_box (j : ℕ) (m : ℤ) : bc57_pt ((j : ℤ) + 1) (2 * m) ∉ box 2 j := by
  rw [mem_box]; simp only [not_forall, not_le]; refine ⟨0, ?_⟩
  rw [bc57_pt_fst]
  have : ((j : ℤ) + 1).natAbs = (j + 1 : ℕ) := by omega
  omega



theorem bc57_cluster_infinite (m : ℤ) :
    (cluster 2 bc57_evenLines (bc57_pt 0 (2 * m))).Infinite := by
  rw [cluster_infinite_iff]
  intro j
  refine ⟨bc57_pt ((j : ℤ) + 1) (2 * m), bc57_pt_outside_box j m, ?_⟩
  have := bc57_connected_pos m (j + 1)
  have hcast : ((j + 1 : ℕ) : ℤ) = (j : ℤ) + 1 := by push_cast; ring
  rwa [hcast] at this


theorem bc57_pt_zero_mem_box {m : ℤ} {n : ℕ} (hm : (2 * m).natAbs ≤ n) :
    bc57_pt 0 (2 * m) ∈ box 2 n := by
  rw [mem_box]; intro i; fin_cases i
  · change ((bc57_pt 0 (2 * m)) 0).natAbs ≤ n; rw [bc57_pt_fst]; simp
  · change ((bc57_pt 0 (2 * m)) 1).natAbs ≤ n; rw [bc57_pt_snd]; exact hm






theorem bc57_cluster_ne {m m' : ℤ} (h : m ≠ m') :
    cluster 2 bc57_evenLines (bc57_pt 0 (2 * m)) ≠ cluster 2 bc57_evenLines (bc57_pt 0 (2 * m')) := by
  intro hEq
  have hmem : bc57_pt 0 (2 * m') ∈ cluster 2 bc57_evenLines (bc57_pt 0 (2 * m)) := by
    rw [hEq]; exact self_mem_cluster _ _
  rw [mem_cluster] at hmem
  have hht : (bc57_pt 0 (2 * m')) 1 = 2 * m :=
    bc57_height_invariant (by rw [bc57_pt_snd]) hmem
  rw [bc57_pt_snd] at hht
  omega


theorem bc57_cluster_family_inj :
    Function.Injective (fun m : ℤ => cluster 2 bc57_evenLines (bc57_pt 0 (2 * m))) := by
  intro m m' h
  by_contra hne
  exact bc57_cluster_ne hne h






theorem bc57_numInfiniteClusters_top :
    numInfiniteClusters 2 bc57_evenLines = ⊤ := by
  unfold numInfiniteClusters
  apply Set.Infinite.encard_eq
  apply Set.infinite_of_injective_forall_mem
    (f := fun m : ℤ => cluster 2 bc57_evenLines (bc57_pt 0 (2 * m)))
  · 
    intro m m' h
    exact bc57_cluster_family_inj h
  · 
    intro m
    exact ⟨bc57_cluster_infinite m, bc57_pt 0 (2 * m), rfl⟩









theorem bc57_no_originNbr {m : ℤ} (hm : m ≠ 0) :
    ∀ a : Site 2, (hypercubicLattice 2).Adj 0 a →
      a ∉ cluster 2 bc57_evenLines (bc57_pt 0 (2 * m)) := by
  intro a hadj hmem
  rw [mem_cluster] at hmem
  have ha2 : a 1 = 2 * m := bc57_height_invariant (by rw [bc57_pt_snd]) hmem
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
  
  have h1 : ((0 : Site 2) 1 - a 1).natAbs = (2 * m).natAbs := by
    simp only [Pi.zero_apply, ha2]; omega
  have h2 : 2 ≤ (2 * m).natAbs := by omega
  omega



theorem bc57_no_reachesNbr {m : ℤ} (hm : m ≠ 0) :
    ¬ bc56_ClusterReachesNbr bc57_evenLines (bc57_pt 0 (2 * m)) := by
  rintro ⟨a, hadj, hmemcl, _, _⟩
  exact bc57_no_originNbr hm a hadj hmemcl








theorem bc57_mem_threeMeetBox : bc57_evenLines ∈ threeMeetBox 2 6 := by
  refine ⟨bc57_numInfiniteClusters_top,
    bc57_pt 0 (2 * 1), bc57_pt 0 (2 * 2), bc57_pt 0 (2 * 3), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact bc57_pt_zero_mem_box (by decide)
  · exact bc57_pt_zero_mem_box (by decide)
  · exact bc57_pt_zero_mem_box (by decide)
  · exact bc57_cluster_infinite 1
  · exact bc57_cluster_infinite 2
  · exact bc57_cluster_infinite 3
  · exact bc57_cluster_ne (by decide)
  · exact bc57_cluster_ne (by decide)
  · exact bc57_cluster_ne (by decide)



















theorem bc57_boxClusterReachesNbr_false :
    ¬ bc56_BoxClusterReachesNbr 2 6 := by
  intro hres
  have hbox1 : bc57_pt 0 (2 * 1) ∈ box 2 6 := bc57_pt_zero_mem_box (by decide)
  have hbox2 : bc57_pt 0 (2 * 2) ∈ box 2 6 := bc57_pt_zero_mem_box (by decide)
  have hbox3 : bc57_pt 0 (2 * 3) ∈ box 2 6 := bc57_pt_zero_mem_box (by decide)
  obtain ⟨h1, _, _⟩ := hres bc57_evenLines bc57_mem_threeMeetBox
    (bc57_pt 0 (2 * 1)) (bc57_pt 0 (2 * 2)) (bc57_pt 0 (2 * 3))
    hbox1 hbox2 hbox3
    (bc57_cluster_infinite 1) (bc57_cluster_infinite 2) (bc57_cluster_infinite 3)
    (bc57_cluster_ne (by decide)) (bc57_cluster_ne (by decide)) (bc57_cluster_ne (by decide))
  exact bc57_no_reachesNbr (by decide) h1













theorem bc57_boxMengerAttachment_false :
    ¬ bmm_BoxMengerAttachment 2 6 := by
  intro hres
  have hbox1 : bc57_pt 0 (2 * 1) ∈ box 2 6 := bc57_pt_zero_mem_box (by decide)
  have hbox2 : bc57_pt 0 (2 * 2) ∈ box 2 6 := bc57_pt_zero_mem_box (by decide)
  have hbox3 : bc57_pt 0 (2 * 3) ∈ box 2 6 := bc57_pt_zero_mem_box (by decide)
  obtain ⟨a₁, a₂, a₃, W, ⟨hadj1, _, _⟩, _, ⟨ha1, _, _⟩, _, _, _⟩ :=
    hres bc57_evenLines bc57_mem_threeMeetBox
      (bc57_pt 0 (2 * 1)) (bc57_pt 0 (2 * 2)) (bc57_pt 0 (2 * 3))
      hbox1 hbox2 hbox3
      (bc57_cluster_infinite 1) (bc57_cluster_infinite 2) (bc57_cluster_infinite 3)
      (bc57_cluster_ne (by decide)) (bc57_cluster_ne (by decide)) (bc57_cluster_ne (by decide))
  exact bc57_no_originNbr (by decide : (1 : ℤ) ≠ 0) a₁ hadj1 ha1

























theorem bc57_status :
    (¬ bc56_BoxClusterReachesNbr 2 6) ∧
    (¬ bmm_BoxMengerAttachment 2 6) ∧
    (bc57_evenLines ∈ threeMeetBox 2 6) ∧
    (numInfiniteClusters 2 bc57_evenLines = ⊤) ∧
    (∀ m : ℤ, m ≠ 0 → ¬ bc56_ClusterReachesNbr bc57_evenLines (bc57_pt 0 (2 * m))) :=
  ⟨bc57_boxClusterReachesNbr_false, bc57_boxMengerAttachment_false, bc57_mem_threeMeetBox,
    bc57_numInfiniteClusters_top, fun _ hm => bc57_no_reachesNbr hm⟩

end StatMech.Walls
