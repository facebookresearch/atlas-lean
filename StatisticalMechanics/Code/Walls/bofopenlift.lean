/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

























































import Mathlib
import Code.Walls.benentryleg
import Code.Walls.bcrboxrep
import Code.Walls.bc57coarsetrif

open Set SimpleGraph Finset
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation



open Classical in




noncomputable def bof_ce : ConfigSpace (Sym2 (Site 2)) :=
  fun e =>
    if ((∃ k : ℤ, e = s(bc57_pt k 0, bc57_pt (k + 1) 0)) ∨
        (∃ k : ℤ, e = s(bc57_pt k 2, bc57_pt (k + 1) 2)) ∨
        (e = s(bc57_pt 0 0, bc57_pt 0 1)) ∨
        (e = s(bc57_pt 0 1, bc57_pt 0 2)))
      then true else false


theorem bof_ce_true_iff (e : Sym2 (Site 2)) :
    bof_ce e = true ↔
      ((∃ k : ℤ, e = s(bc57_pt k 0, bc57_pt (k + 1) 0)) ∨
       (∃ k : ℤ, e = s(bc57_pt k 2, bc57_pt (k + 1) 2)) ∨
       (e = s(bc57_pt 0 0, bc57_pt 0 1)) ∨
       (e = s(bc57_pt 0 1, bc57_pt 0 2))) := by
  classical
  unfold bof_ce
  by_cases h : ((∃ k : ℤ, e = s(bc57_pt k 0, bc57_pt (k + 1) 0)) ∨
      (∃ k : ℤ, e = s(bc57_pt k 2, bc57_pt (k + 1) 2)) ∨
      (e = s(bc57_pt 0 0, bc57_pt 0 1)) ∨
      (e = s(bc57_pt 0 1, bc57_pt 0 2)))
  · rw [if_pos h]; exact iff_of_true rfl h
  · rw [if_neg h]; exact iff_of_false (by simp) h


theorem bof_horiz0_open (k : ℤ) : bof_ce s(bc57_pt k 0, bc57_pt (k + 1) 0) = true :=
  (bof_ce_true_iff _).mpr (Or.inl ⟨k, rfl⟩)


theorem bof_horiz2_open (k : ℤ) : bof_ce s(bc57_pt k 2, bc57_pt (k + 1) 2) = true :=
  (bof_ce_true_iff _).mpr (Or.inr (Or.inl ⟨k, rfl⟩))


theorem bof_bridge1_open : bof_ce s(bc57_pt 0 0, bc57_pt 0 1) = true :=
  (bof_ce_true_iff _).mpr (Or.inr (Or.inr (Or.inl rfl)))


theorem bof_bridge2_open : bof_ce s(bc57_pt 0 1, bc57_pt 0 2) = true :=
  (bof_ce_true_iff _).mpr (Or.inr (Or.inr (Or.inr rfl)))




theorem bof_box_mem (x : Site 2) :
    x ∈ bc61_boxAround 2 0 (bc57_pt 0 1) ↔ x = bc57_pt 0 1 := by
  rw [bc61_mem_boxAround, mem_box]
  constructor
  · intro h
    funext i
    have h0 := h i
    rw [Pi.sub_apply] at h0
    omega
  · intro h i
    rw [h, Pi.sub_apply]; simp


theorem bof_line0_notMem (k : ℤ) :
    bc57_pt k 0 ∉ bc61_boxAround 2 0 (bc57_pt 0 1) := by
  rw [bof_box_mem]; intro h
  have := congrArg (fun p : Site 2 => p 1) h
  simp only [bc57_pt_snd] at this; omega


theorem bof_line2_notMem (k : ℤ) :
    bc57_pt k 2 ∉ bc61_boxAround 2 0 (bc57_pt 0 1) := by
  rw [bof_box_mem]; intro h
  have := congrArg (fun p : Site 2 => p 1) h
  simp only [bc57_pt_snd] at this; omega












theorem bof_rm_height_step {h : ℤ} {u v : Site 2} (hu : u 1 = h)
    (hadj : (openSubgraph 2 (removeSites (bc61_boxAround 2 0 (bc57_pt 0 1)) bof_ce)).Adj u v) :
    v 1 = h := by
  classical
  obtain ⟨hlat, hopen⟩ := hadj
  unfold removeSites at hopen
  by_cases hc : ∃ t ∈ bc61_boxAround 2 0 (bc57_pt 0 1), t ∈ s(u, v)
  · rw [if_pos hc] at hopen; simp at hopen
  · rw [if_neg hc] at hopen
    have hu01 : u ≠ bc57_pt 0 1 := fun he =>
      hc ⟨u, (bof_box_mem u).mpr he, Sym2.mem_mk_left u v⟩
    have hv01 : v ≠ bc57_pt 0 1 := fun he =>
      hc ⟨v, (bof_box_mem v).mpr he, Sym2.mem_mk_right u v⟩
    rcases (bof_ce_true_iff _).mp hopen with ⟨k, hk⟩ | ⟨k, hk⟩ | hk | hk
    · rw [Sym2.eq_iff] at hk
      rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        · simp only [bc57_pt_snd] at hu ⊢; omega
    · rw [Sym2.eq_iff] at hk
      rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        · simp only [bc57_pt_snd] at hu ⊢; omega
    · rw [Sym2.eq_iff] at hk
      rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact absurd rfl hv01
      · exact absurd rfl hu01
    · rw [Sym2.eq_iff] at hk
      rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact absurd rfl hu01
      · exact absurd rfl hv01



theorem bof_rm_height_inv {h : ℤ} {u y : Site 2} (hu : u 1 = h)
    (hconn : Connected 2 (removeSites (bc61_boxAround 2 0 (bc57_pt 0 1)) bof_ce) u y) :
    y 1 = h := by
  obtain ⟨w⟩ := hconn
  induction w with
  | nil => exact hu
  | @cons a b c hab w' ih => exact ih (bof_rm_height_step hu hab)




theorem bof_rm_line0_step (k : ℤ) :
    Connected 2 (removeSites (bc61_boxAround 2 0 (bc57_pt 0 1)) bof_ce)
      (bc57_pt k 0) (bc57_pt (k + 1) 0) :=
  bc61_cut_adj_connected (bc57_pt_adj k 0) (bof_horiz0_open k)
    (bof_line0_notMem k) (bof_line0_notMem (k + 1))


theorem bof_rm_line2_step (k : ℤ) :
    Connected 2 (removeSites (bc61_boxAround 2 0 (bc57_pt 0 1)) bof_ce)
      (bc57_pt k 2) (bc57_pt (k + 1) 2) :=
  bc61_cut_adj_connected (bc57_pt_adj k 2) (bof_horiz2_open k)
    (bof_line2_notMem k) (bof_line2_notMem (k + 1))


theorem bof_rm_line0_reach (j : ℕ) :
    Connected 2 (removeSites (bc61_boxAround 2 0 (bc57_pt 0 1)) bof_ce)
      (bc57_pt 5 0) (bc57_pt ((5 : ℤ) + (j : ℤ)) 0) := by
  induction j with
  | zero => simpa using connected_refl _ (bc57_pt 5 0)
  | succ i ih =>
    have step := bof_rm_line0_step ((5 : ℤ) + (i : ℤ))
    have hc : ((5 : ℤ) + ((i + 1 : ℕ) : ℤ)) = ((5 : ℤ) + (i : ℤ)) + 1 := by push_cast; ring
    rw [hc]; exact ih.trans step


theorem bof_rm_line2_reach (j : ℕ) :
    Connected 2 (removeSites (bc61_boxAround 2 0 (bc57_pt 0 1)) bof_ce)
      (bc57_pt 5 2) (bc57_pt ((5 : ℤ) + (j : ℤ)) 2) := by
  induction j with
  | zero => simpa using connected_refl _ (bc57_pt 5 2)
  | succ i ih =>
    have step := bof_rm_line2_step ((5 : ℤ) + (i : ℤ))
    have hc : ((5 : ℤ) + ((i + 1 : ℕ) : ℤ)) = ((5 : ℤ) + (i : ℤ)) + 1 := by push_cast; ring
    rw [hc]; exact ih.trans step



theorem bof_cluster_u_infinite :
    (cluster 2 (removeSites (bc61_boxAround 2 0 (bc57_pt 0 1)) bof_ce) (bc57_pt 5 0)).Infinite := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun j : ℕ => bc57_pt ((5 : ℤ) + (j : ℤ)) 0) ?_ ?_
  · intro a b hab
    have h5 := congrArg (fun p : Site 2 => p 0) hab
    simp only [bc57_pt_fst] at h5
    have : (a : ℤ) = (b : ℤ) := by omega
    exact_mod_cast this
  · intro j; exact mem_cluster.mpr (bof_rm_line0_reach j)



theorem bof_cluster_v_infinite :
    (cluster 2 (removeSites (bc61_boxAround 2 0 (bc57_pt 0 1)) bof_ce) (bc57_pt 5 2)).Infinite := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun j : ℕ => bc57_pt ((5 : ℤ) + (j : ℤ)) 2) ?_ ?_
  · intro a b hab
    have h5 := congrArg (fun p : Site 2 => p 0) hab
    simp only [bc57_pt_fst] at h5
    have : (a : ℤ) = (b : ℤ) := by omega
    exact_mod_cast this
  · intro j; exact mem_cluster.mpr (bof_rm_line2_reach j)




theorem bof_line0_from0 (n : ℤ) : Connected 2 bof_ce (bc57_pt 0 0) (bc57_pt n 0) := by
  induction n using Int.induction_on with
  | zero => exact connected_refl _ _
  | succ i ih =>
    have step : Connected 2 bof_ce (bc57_pt (i : ℤ) 0) (bc57_pt ((i : ℤ) + 1) 0) :=
      IsOpenEdge.connected ⟨bc57_pt_adj (i : ℤ) 0, bof_horiz0_open (i : ℤ)⟩
    exact ih.trans step
  | pred i ih =>
    have step : Connected 2 bof_ce (bc57_pt (-(i : ℤ) - 1) 0) (bc57_pt (-(i : ℤ)) 0) := by
      have h := IsOpenEdge.connected
        ⟨bc57_pt_adj (-(i : ℤ) - 1) 0, bof_horiz0_open (-(i : ℤ) - 1)⟩
      rwa [show (-(i : ℤ) - 1) + 1 = -(i : ℤ) by ring] at h
    exact ih.trans step.symm


theorem bof_line2_from0 (n : ℤ) : Connected 2 bof_ce (bc57_pt 0 2) (bc57_pt n 2) := by
  induction n using Int.induction_on with
  | zero => exact connected_refl _ _
  | succ i ih =>
    have step : Connected 2 bof_ce (bc57_pt (i : ℤ) 2) (bc57_pt ((i : ℤ) + 1) 2) :=
      IsOpenEdge.connected ⟨bc57_pt_adj (i : ℤ) 2, bof_horiz2_open (i : ℤ)⟩
    exact ih.trans step
  | pred i ih =>
    have step : Connected 2 bof_ce (bc57_pt (-(i : ℤ) - 1) 2) (bc57_pt (-(i : ℤ)) 2) := by
      have h := IsOpenEdge.connected
        ⟨bc57_pt_adj (-(i : ℤ) - 1) 2, bof_horiz2_open (-(i : ℤ) - 1)⟩
      rwa [show (-(i : ℤ) - 1) + 1 = -(i : ℤ) by ring] at h
    exact ih.trans step.symm




theorem bof_uv_connected :
    (openSubgraph 2 bof_ce).Reachable (bc57_pt 5 0) (bc57_pt 5 2) := by
  have hadj01 : (hypercubicLattice 2).Adj (bc57_pt 0 0) (bc57_pt 0 1) := by
    rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp [bc57_pt]
  have hadj12 : (hypercubicLattice 2).Adj (bc57_pt 0 1) (bc57_pt 0 2) := by
    rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp [bc57_pt]
  have h1 : Connected 2 bof_ce (bc57_pt 5 0) (bc57_pt 0 0) := (bof_line0_from0 5).symm
  have h2 : Connected 2 bof_ce (bc57_pt 0 0) (bc57_pt 0 1) :=
    IsOpenEdge.connected ⟨hadj01, bof_bridge1_open⟩
  have h3 : Connected 2 bof_ce (bc57_pt 0 1) (bc57_pt 0 2) :=
    IsOpenEdge.connected ⟨hadj12, bof_bridge2_open⟩
  have h4 : Connected 2 bof_ce (bc57_pt 0 2) (bc57_pt 5 2) := bof_line2_from0 5
  exact ((h1.trans h2).trans h3).trans h4






theorem bof_not_reconnect :
    ¬ (bc67_contractedLattice bof_ce 0 (bc57_pt 0 1)).Reachable (bc57_pt 5 0) (bc57_pt 5 2) := by
  intro h
  have hconn : Connected 2 (removeSites (bc61_boxAround 2 0 (bc57_pt 0 1)) bof_ce)
      (bc57_pt 5 0) (bc57_pt 5 2) := h
  have hht : (bc57_pt 5 2) 1 = (0 : ℤ) := bof_rm_height_inv (by simp) hconn
  simp only [bc57_pt_snd] at hht; omega






theorem bof_ClusterReconnect_false :
    ¬ ben_ClusterReconnect bof_ce 0 (bc57_pt 0 1) := by
  intro hrec
  exact bof_not_reconnect
    (hrec (bc57_pt 5 0) (bc57_pt 5 2) bof_uv_connected
      bof_cluster_u_infinite bof_cluster_v_infinite)



theorem bof_residue_not_universal :
    ∃ (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ) (tipj : Site 2),
      ¬ ben_ClusterReconnect ω L tipj :=
  ⟨bof_ce, 0, bc57_pt 0 1, bof_ClusterReconnect_false⟩






theorem bof_openLift_fails :
    (∃ (hu : (bc57_pt 5 0) ∉ (↑(bc61_boxAround 2 0 (bc57_pt 0 1)) : Set (Site 2)))
       (hv : (bc57_pt 5 2) ∉ (↑(bc61_boxAround 2 0 (bc57_pt 0 1)) : Set (Site 2))),
      ((hypercubicLattice 2).induce (↑(bc61_boxAround 2 0 (bc57_pt 0 1)) : Set (Site 2))ᶜ).Reachable
        ⟨bc57_pt 5 0, hu⟩ ⟨bc57_pt 5 2, hv⟩) ∧
    ¬ (bc67_contractedLattice bof_ce 0 (bc57_pt 0 1)).Reachable (bc57_pt 5 0) (bc57_pt 5 2) :=
  ⟨ben_full_reconnect_of_escapes bof_ce 0 (by norm_num) (bc57_pt 0 1) (bc57_pt 5 0) (bc57_pt 5 2)
      bof_cluster_u_infinite bof_cluster_v_infinite,
   bof_not_reconnect⟩

end StatMech.Walls
