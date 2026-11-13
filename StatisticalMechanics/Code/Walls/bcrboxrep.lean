/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




































































import Mathlib
import Code.Walls.brtrouteclose
import Code.Walls.btrtrifnotion

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}













theorem bcr_path_crosses_box (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (x : Site d) {u v : Site d}
    (p : (openSubgraph d ω).Walk u v)
    (hcut : ¬ (bc67_contractedLattice ω L x).Reachable u v) :
    ∃ w ∈ p.support, w ∈ bc61_boxAround d L x := by
  by_contra h
  push_neg at h
  exact hcut (brt_reachable_of_avoidWalk ω L x p h)





theorem bcr_boxRep_of_fullConn_cut (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (x : Site d)
    {u v : Site d}
    (hconn : (openSubgraph d ω).Reachable u v)
    (hcut : ¬ (bc67_contractedLattice ω L x).Reachable u v) :
    ∃ r ∈ bc61_boxAround d L x,
      (openSubgraph d ω).Reachable u r ∧ (openSubgraph d ω).Reachable r v := by
  classical
  obtain ⟨p⟩ := hconn
  obtain ⟨r, hrsup, hrbox⟩ := bcr_path_crosses_box ω L x p hcut
  refine ⟨r, hrbox, (p.takeUntil r hrsup).reachable, (p.dropUntil r hrsup).reachable⟩














theorem bcr_center_reaches_arm_full (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) {y : Site d}
    (hgen : btr_IsGenuineCoarseTrif ω L y) :
    ∃ a₁ a₂ a₃ : Site d,
      (openSubgraph d ω).Reachable y a₁ ∧ (openSubgraph d ω).Reachable y a₂ ∧
        (openSubgraph d ω).Reachable y a₃ := by
  obtain ⟨a₁, a₂, a₃, _, _, _, ⟨hcy1, hcy2, hcy3⟩, _, _⟩ := hgen
  exact ⟨a₁, a₂, a₃, hcy1, hcy2, hcy3⟩









theorem bcr_connectedRep_of_genuineCluster (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) {y : Site d}
    (hgen : btr_IsGenuineCoarseTrif ω L y) :
    ∃ (r : Site d) (a₁ a₂ a₃ : Site d), r ∈ bc61_boxAround d L y ∧
      (openSubgraph d ω).Reachable r y ∧
      (openSubgraph d ω).Reachable r a₁ ∧
      (openSubgraph d ω).Reachable r a₂ ∧
      (openSubgraph d ω).Reachable r a₃ := by
  obtain ⟨a₁, a₂, a₃, _, _, _, ⟨hcy1, hcy2, hcy3⟩, _, ⟨hs12, _, _⟩⟩ := hgen
  
  have h12 : (openSubgraph d ω).Reachable a₁ a₂ := hcy1.symm.trans hcy2
  
  have hcut : ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₂ := hs12
  obtain ⟨r, hrbox, hra1, hra2⟩ := bcr_boxRep_of_fullConn_cut ω L y h12 hcut
  refine ⟨r, a₁, a₂, a₃, hrbox, ?_, hra1.symm, hra2, ?_⟩
  · 
    exact hra1.symm.trans hcy1.symm
  · 
    exact ((hra1.symm.trans hcy1.symm).trans hcy3)
















theorem bcr_upperLines_not_genuineCluster (L : ℕ) (y : Site 2) :
    ¬ btr_IsGenuineCoarseTrif bc60_upperLines L y :=
  btr_bc60_not_genuineTrif L y







theorem bcr_upperLines_no_connectedRep (L : ℕ) (y : Site 2) :
    ¬ ∃ (_hgen : btr_IsGenuineCoarseTrif bc60_upperLines L y)
        (r : Site 2) (a₁ a₂ a₃ : Site 2), r ∈ bc61_boxAround 2 L y ∧
      (openSubgraph 2 bc60_upperLines).Reachable r y ∧
      (openSubgraph 2 bc60_upperLines).Reachable r a₁ ∧
      (openSubgraph 2 bc60_upperLines).Reachable r a₂ ∧
      (openSubgraph 2 bc60_upperLines).Reachable r a₃ := by
  rintro ⟨hgen, -⟩
  exact bcr_upperLines_not_genuineCluster L y hgen

















theorem bcr_hroute_via_branch (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (aj x b tip : Site d)
    (hxb : (bc67_contractedLattice ω L aj).Reachable x b)
    (hbt : (bc67_contractedLattice ω L aj).Reachable b tip) :
    (bc67_contractedLattice ω L aj).Reachable x tip :=
  hxb.trans hbt









theorem bcr_center_reaches_branch_full (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) {y arm b : Site d}
    (hcy : (openSubgraph d ω).Reachable y arm)
    (hab : (bc67_contractedLattice ω L y).Reachable arm b) :
    (openSubgraph d ω).Reachable y b :=
  hcy.trans (hab.mono (bc67_contractedLattice_le ω L y))







def bcr_RepRoute (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d) (arm : Fin 3 → Site d) : Prop :=
  ∀ i j, i ≠ j → (bc67_contractedLattice ω L (arm j)).Reachable y (arm i)










open Classical in



noncomputable def bcr_cross : ConfigSpace (Sym2 (Site 2)) :=
  fun e => if (∃ k : ℤ, e = s(bc57_pt k 0, bc57_pt (k + 1) 0)) ∨
              (∃ h : ℤ, e = s(bc57_pt 0 h, bc57_pt 0 (h + 1))) then true else false


theorem bcr_cross_horiz (k : ℤ) : bcr_cross s(bc57_pt k 0, bc57_pt (k + 1) 0) = true := by
  classical
  rw [bcr_cross, if_pos]; exact Or.inl ⟨k, rfl⟩


theorem bcr_cross_vert (h : ℤ) : bcr_cross s(bc57_pt 0 h, bc57_pt 0 (h + 1)) = true := by
  classical
  rw [bcr_cross, if_pos]; exact Or.inr ⟨h, rfl⟩


theorem bcr_vert_adj (h : ℤ) : (hypercubicLattice 2).Adj (bc57_pt 0 h) (bc57_pt 0 (h + 1)) := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp [bc57_pt]



theorem bcr_cross_open_coord {u v : Site 2} (h : bcr_cross s(u, v) = true) :
    (u 1 = 0 ∧ v 1 = 0) ∨ (u 0 = 0 ∧ v 0 = 0) := by
  classical
  have hc : (∃ k : ℤ, s(u, v) = s(bc57_pt k 0, bc57_pt (k + 1) 0)) ∨
      (∃ h : ℤ, s(u, v) = s(bc57_pt 0 h, bc57_pt 0 (h + 1))) := by
    by_contra hcon; rw [bcr_cross, if_neg hcon] at h; exact Bool.false_ne_true h
  rcases hc with ⟨k, hk⟩ | ⟨hh, hk⟩
  · left
    rw [Sym2.eq_iff] at hk
    rcases hk with ⟨hu, hv⟩ | ⟨hu, hv⟩ <;>
      rw [hu, hv] <;> simp [bc57_pt]
  · right
    rw [Sym2.eq_iff] at hk
    rcases hk with ⟨hu, hv⟩ | ⟨hu, hv⟩ <;>
      rw [hu, hv] <;> simp [bc57_pt]


theorem bcr_out {L : ℕ} {C H : ℤ} (h : L < C.natAbs ∨ L < H.natAbs) :
    bc57_pt C H ∉ bc61_boxAround 2 L (bc57_pt 0 0) := by
  rw [bc61_mem_boxAround, mem_box]
  simp only [not_forall, not_le]
  rcases h with h | h
  · exact ⟨0, by simp only [Pi.sub_apply, bc57_pt_fst, sub_zero]; exact h⟩
  · exact ⟨1, by simp only [Pi.sub_apply, bc57_pt_snd, sub_zero]; exact h⟩




theorem bcr_hreach (c : ℤ) (j : ℕ) :
    Connected 2 bcr_cross (bc57_pt c 0) (bc57_pt (c + (j : ℤ)) 0) := by
  induction j with
  | zero => simpa using connected_refl _ (bc57_pt c 0)
  | succ i ih =>
    have step : Connected 2 bcr_cross (bc57_pt (c + (i : ℤ)) 0) (bc57_pt (c + (i : ℤ) + 1) 0) :=
      IsOpenEdge.connected ⟨bc57_pt_adj _ 0, bcr_cross_horiz _⟩
    have hcast : c + ((i + 1 : ℕ) : ℤ) = c + (i : ℤ) + 1 := by push_cast; ring
    rw [hcast]; exact ih.trans step


theorem bcr_vreach_up (hgt : ℤ) (j : ℕ) :
    Connected 2 bcr_cross (bc57_pt 0 hgt) (bc57_pt 0 (hgt + (j : ℤ))) := by
  induction j with
  | zero => simpa using connected_refl _ (bc57_pt 0 hgt)
  | succ i ih =>
    have step : Connected 2 bcr_cross (bc57_pt 0 (hgt + (i : ℤ))) (bc57_pt 0 (hgt + (i : ℤ) + 1)) :=
      IsOpenEdge.connected ⟨bcr_vert_adj _, bcr_cross_vert _⟩
    have hcast : hgt + ((i + 1 : ℕ) : ℤ) = hgt + (i : ℤ) + 1 := by push_cast; ring
    rw [hcast]; exact ih.trans step


theorem bcr_vreach_down (hgt : ℤ) (j : ℕ) :
    Connected 2 bcr_cross (bc57_pt 0 hgt) (bc57_pt 0 (hgt - (j : ℤ))) := by
  induction j with
  | zero => simpa using connected_refl _ (bc57_pt 0 hgt)
  | succ i ih =>
    have key : Connected 2 bcr_cross (bc57_pt 0 (hgt - (i : ℤ) - 1)) (bc57_pt 0 (hgt - (i : ℤ) - 1 + 1)) :=
      IsOpenEdge.connected ⟨bcr_vert_adj _, bcr_cross_vert _⟩
    have he : hgt - (i : ℤ) - 1 + 1 = hgt - (i : ℤ) := by ring
    rw [he] at key
    have hcast : hgt - ((i + 1 : ℕ) : ℤ) = hgt - (i : ℤ) - 1 := by push_cast; ring
    rw [hcast]; exact ih.trans key.symm




theorem bcr_cut_hreach_pos (L : ℕ) (j : ℕ) :
    Connected 2 (removeSites (bc61_boxAround 2 L (bc57_pt 0 0)) bcr_cross)
      (bc57_pt ((L : ℤ) + 1) 0) (bc57_pt ((L : ℤ) + 1 + (j : ℤ)) 0) := by
  induction j with
  | zero => simpa using connected_refl _ (bc57_pt ((L : ℤ) + 1) 0)
  | succ i ih =>
    have hstep : Connected 2 (removeSites (bc61_boxAround 2 L (bc57_pt 0 0)) bcr_cross)
        (bc57_pt ((L : ℤ) + 1 + (i : ℤ)) 0) (bc57_pt ((L : ℤ) + 1 + (i : ℤ) + 1) 0) :=
      bc61_cut_adj_connected (bc57_pt_adj _ 0) (bcr_cross_horiz _)
        (bcr_out (Or.inl (by omega)))
        (bcr_out (Or.inl (by omega)))
    have hcast : (L : ℤ) + 1 + ((i + 1 : ℕ) : ℤ) = (L : ℤ) + 1 + (i : ℤ) + 1 := by push_cast; ring
    rw [hcast]; exact ih.trans hstep


theorem bcr_cut_vreach_up (L : ℕ) (j : ℕ) :
    Connected 2 (removeSites (bc61_boxAround 2 L (bc57_pt 0 0)) bcr_cross)
      (bc57_pt 0 ((L : ℤ) + 1)) (bc57_pt 0 ((L : ℤ) + 1 + (j : ℤ))) := by
  induction j with
  | zero => simpa using connected_refl _ (bc57_pt 0 ((L : ℤ) + 1))
  | succ i ih =>
    have hstep : Connected 2 (removeSites (bc61_boxAround 2 L (bc57_pt 0 0)) bcr_cross)
        (bc57_pt 0 ((L : ℤ) + 1 + (i : ℤ))) (bc57_pt 0 ((L : ℤ) + 1 + (i : ℤ) + 1)) :=
      bc61_cut_adj_connected (bcr_vert_adj _) (bcr_cross_vert _)
        (bcr_out (Or.inr (by omega)))
        (bcr_out (Or.inr (by omega)))
    have hcast : (L : ℤ) + 1 + ((i + 1 : ℕ) : ℤ) = (L : ℤ) + 1 + (i : ℤ) + 1 := by push_cast; ring
    rw [hcast]; exact ih.trans hstep


theorem bcr_cut_vreach_down (L : ℕ) (j : ℕ) :
    Connected 2 (removeSites (bc61_boxAround 2 L (bc57_pt 0 0)) bcr_cross)
      (bc57_pt 0 (-(L : ℤ) - 1)) (bc57_pt 0 (-(L : ℤ) - 1 - (j : ℤ))) := by
  induction j with
  | zero => simpa using connected_refl _ (bc57_pt 0 (-(L : ℤ) - 1))
  | succ i ih =>
    have key : Connected 2 (removeSites (bc61_boxAround 2 L (bc57_pt 0 0)) bcr_cross)
        (bc57_pt 0 (-(L : ℤ) - 1 - (i : ℤ) - 1)) (bc57_pt 0 (-(L : ℤ) - 1 - (i : ℤ) - 1 + 1)) :=
      bc61_cut_adj_connected (bcr_vert_adj _) (bcr_cross_vert _)
        (bcr_out (Or.inr (by omega)))
        (bcr_out (Or.inr (by omega)))
    have he : -(L : ℤ) - 1 - (i : ℤ) - 1 + 1 = -(L : ℤ) - 1 - (i : ℤ) := by ring
    rw [he] at key
    have hcast : -(L : ℤ) - 1 - ((i + 1 : ℕ) : ℤ) = -(L : ℤ) - 1 - (i : ℤ) - 1 := by push_cast; ring
    rw [hcast]; exact ih.trans key.symm






theorem bcr_inv_flat (L : ℕ) {u v : Site 2}
    (hconn : Connected 2 (removeSites (bc61_boxAround 2 L (bc57_pt 0 0)) bcr_cross) u v)
    (hu : u 1 = 0 ∧ u 0 ≠ 0) : v 1 = 0 ∧ v 0 ≠ 0 := by
  obtain ⟨w⟩ := hconn
  induction w with
  | nil => exact hu
  | @cons a b c hab w' ih =>
    apply ih
    rw [openSubgraph_adj] at hab
    obtain ⟨_, hopen⟩ := hab
    
    have hcross : bcr_cross s(a, b) = true := by
      unfold removeSites at hopen
      by_cases hbox : ∃ t ∈ bc61_boxAround 2 L (bc57_pt 0 0), t ∈ s(a, b)
      · rw [if_pos hbox] at hopen; exact absurd hopen (by decide)
      · rwa [if_neg hbox] at hopen
    have hbnotbox : b ∉ bc61_boxAround 2 L (bc57_pt 0 0) := by
      unfold removeSites at hopen
      by_contra hb
      rw [if_pos ⟨b, hb, Sym2.mem_mk_right a b⟩] at hopen; exact absurd hopen (by decide)
    rcases bcr_cross_open_coord hcross with ⟨_, hb1⟩ | ⟨ha0, _⟩
    · 
      refine ⟨hb1, ?_⟩
      intro hb0
      apply hbnotbox
      have hb0' : b = bc57_pt 0 0 := by
        funext i; fin_cases i <;> simp [bc57_pt, hb0, hb1]
      rw [hb0']; exact btr_center_mem_box (bc57_pt 0 0)
    · exact absurd ha0 hu.2



theorem bcr_inv_plusy (L : ℕ) {u v : Site 2}
    (hconn : Connected 2 (removeSites (bc61_boxAround 2 L (bc57_pt 0 0)) bcr_cross) u v)
    (hu : u 0 = 0 ∧ (L : ℤ) < u 1) : v 0 = 0 ∧ (L : ℤ) < v 1 := by
  obtain ⟨w⟩ := hconn
  induction w with
  | nil => exact hu
  | @cons a b c hab w' ih =>
    obtain ⟨hua0, hua1⟩ := hu
    apply ih
    rw [openSubgraph_adj] at hab
    obtain ⟨hlat, hopen⟩ := hab
    have hcross : bcr_cross s(a, b) = true := by
      unfold removeSites at hopen
      by_cases hbox : ∃ t ∈ bc61_boxAround 2 L (bc57_pt 0 0), t ∈ s(a, b)
      · rw [if_pos hbox] at hopen; exact absurd hopen (by decide)
      · rwa [if_neg hbox] at hopen
    have hbnotbox : b ∉ bc61_boxAround 2 L (bc57_pt 0 0) := by
      unfold removeSites at hopen
      by_contra hb
      rw [if_pos ⟨b, hb, Sym2.mem_mk_right a b⟩] at hopen; exact absurd hopen (by decide)
    rcases bcr_cross_open_coord hcross with ⟨ha1, _⟩ | ⟨_, hb0⟩
    · 
      exact absurd ha1 (by omega)
    · 
      refine ⟨hb0, ?_⟩
      
      have hb1nat : L < (b 1).natAbs := by
        by_contra hcon
        push_neg at hcon
        refine hbnotbox ?_
        rw [bc61_mem_boxAround, mem_box, Fin.forall_fin_two]
        refine ⟨?_, ?_⟩
        · simp only [Pi.sub_apply, bc57_pt_fst, sub_zero, hb0]; simp
        · simpa only [Pi.sub_apply, bc57_pt_snd, sub_zero] using hcon
      
      rw [hypercubicLattice_adj, Fin.sum_univ_two] at hlat
      omega








theorem bcr_cross_genuineTrif (L : ℕ) :
    btr_IsGenuineCoarseTrif bcr_cross L (bc57_pt 0 0) := by
  classical
  refine ⟨bc57_pt ((L : ℤ) + 1) 0, bc57_pt 0 ((L : ℤ) + 1), bc57_pt 0 (-(L : ℤ) - 1),
    ⟨bc57_pt (L : ℤ) 0, ?_, ?_⟩, ⟨bc57_pt 0 (L : ℤ), ?_, ?_⟩, ⟨bc57_pt 0 (-(L : ℤ)), ?_, ?_⟩,
    ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · 
    rw [bc61_mem_boxAround, mem_box, Fin.forall_fin_two]
    simp only [Pi.sub_apply, bc57_pt_fst, bc57_pt_snd, sub_zero]; omega
  · 
    exact ⟨bc57_pt_adj (L : ℤ) 0, bcr_cross_horiz (L : ℤ)⟩
  · 
    rw [bc61_mem_boxAround, mem_box, Fin.forall_fin_two]
    simp only [Pi.sub_apply, bc57_pt_fst, bc57_pt_snd, sub_zero]; omega
  · 
    exact ⟨bcr_vert_adj (L : ℤ), bcr_cross_vert (L : ℤ)⟩
  · 
    rw [bc61_mem_boxAround, mem_box, Fin.forall_fin_two]
    simp only [Pi.sub_apply, bc57_pt_fst, bc57_pt_snd, sub_zero]; omega
  · 
    have hadj : (openSubgraph 2 bcr_cross).Adj (bc57_pt 0 (-(L : ℤ) - 1)) (bc57_pt 0 (-(L : ℤ))) := by
      have h1 := bcr_vert_adj (-(L : ℤ) - 1)
      have h2 := bcr_cross_vert (-(L : ℤ) - 1)
      rw [show (-(L : ℤ) - 1 + 1) = -(L : ℤ) by ring] at h1 h2
      exact ⟨h1, h2⟩
    exact hadj.symm
  · 
    have h := bcr_hreach 0 (L + 1)
    rwa [show (0 : ℤ) + ((L + 1 : ℕ) : ℤ) = (L : ℤ) + 1 by push_cast; ring] at h
  · 
    have h := bcr_vreach_up 0 (L + 1)
    rwa [show (0 : ℤ) + ((L + 1 : ℕ) : ℤ) = (L : ℤ) + 1 by push_cast; ring] at h
  · 
    have h := bcr_vreach_down 0 (L + 1)
    rwa [show (0 : ℤ) - ((L + 1 : ℕ) : ℤ) = -(L : ℤ) - 1 by push_cast; ring] at h
  · 
    apply Set.infinite_of_injective_forall_mem
      (f := fun j : ℕ => bc57_pt ((L : ℤ) + 1 + (j : ℤ)) 0)
    · intro i j hij
      have := congrArg (fun p => p 0) hij
      simp only [bc57_pt_fst] at this; omega
    · intro j; rw [mem_cluster]; exact bcr_cut_hreach_pos L j
  · 
    apply Set.infinite_of_injective_forall_mem
      (f := fun j : ℕ => bc57_pt 0 ((L : ℤ) + 1 + (j : ℤ)))
    · intro i j hij
      have := congrArg (fun p => p 1) hij
      simp only [bc57_pt_snd] at this; omega
    · intro j; rw [mem_cluster]; exact bcr_cut_vreach_up L j
  · 
    apply Set.infinite_of_injective_forall_mem
      (f := fun j : ℕ => bc57_pt 0 (-(L : ℤ) - 1 - (j : ℤ)))
    · intro i j hij
      have := congrArg (fun p => p 1) hij
      simp only [bc57_pt_snd] at this; omega
    · intro j; rw [mem_cluster]; exact bcr_cut_vreach_down L j
  · 
    intro hconn
    have := (bcr_inv_flat L hconn
      ⟨by simp only [bc57_pt_snd], by simp only [bc57_pt_fst]; omega⟩).1
    simp only [bc57_pt_snd] at this; omega
  · 
    intro hconn
    have := (bcr_inv_flat L hconn
      ⟨by simp only [bc57_pt_snd], by simp only [bc57_pt_fst]; omega⟩).1
    simp only [bc57_pt_snd] at this; omega
  · 
    intro hconn
    have := (bcr_inv_plusy L hconn
      ⟨by simp only [bc57_pt_fst], by simp only [bc57_pt_snd]; omega⟩).2
    simp only [bc57_pt_snd] at this; omega




theorem bcr_cross_rep_fires (L : ℕ) :
    ∃ (r : Site 2) (a₁ a₂ a₃ : Site 2), r ∈ bc61_boxAround 2 L (bc57_pt 0 0) ∧
      (openSubgraph 2 bcr_cross).Reachable r (bc57_pt 0 0) ∧
      (openSubgraph 2 bcr_cross).Reachable r a₁ ∧
      (openSubgraph 2 bcr_cross).Reachable r a₂ ∧
      (openSubgraph 2 bcr_cross).Reachable r a₃ :=
  bcr_connectedRep_of_genuineCluster bcr_cross L (bcr_cross_genuineTrif L)




































theorem bcr_status :
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (x u v : Site d)
      (p : (openSubgraph d ω).Walk u v),
      ¬ (bc67_contractedLattice ω L x).Reachable u v →
      ∃ w ∈ p.support, w ∈ bc61_boxAround d L x) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d),
      btr_IsGenuineCoarseTrif ω L y →
      ∃ (r : Site d) (a₁ a₂ a₃ : Site d), r ∈ bc61_boxAround d L y ∧
        (openSubgraph d ω).Reachable r y ∧ (openSubgraph d ω).Reachable r a₁ ∧
        (openSubgraph d ω).Reachable r a₂ ∧ (openSubgraph d ω).Reachable r a₃) ∧
    
    (∀ (L : ℕ) (y : Site 2), ¬ btr_IsGenuineCoarseTrif bc60_upperLines L y) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y arm b : Site d),
      (openSubgraph d ω).Reachable y arm →
      (bc67_contractedLattice ω L y).Reachable arm b →
      (openSubgraph d ω).Reachable y b) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ω L x u v p hcut; exact bcr_path_crosses_box ω L x p hcut
  · intro ω L y hgen; exact bcr_connectedRep_of_genuineCluster ω L hgen
  · intro L y; exact bcr_upperLines_not_genuineCluster L y
  · intro ω L y arm b hcy hab; exact bcr_center_reaches_branch_full ω L hcy hab

end StatMech.Walls
