/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/















































import Mathlib
import Code.Walls.brpreproute

open Set SimpleGraph Finset
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation



open Classical in



noncomputable def bea_ce : ConfigSpace (Sym2 (Site 2)) :=
  fun e =>
    if ((∃ k : ℤ, e = s(bc57_pt k 0, bc57_pt (k + 1) 0)) ∨
        (∃ k : ℤ, e = s(bc57_pt k 1, bc57_pt (k + 1) 1)) ∨
        (∃ k : ℤ, e = s(bc57_pt k (-1), bc57_pt (k + 1) (-1))) ∨
        (e = s(bc57_pt 0 0, bc57_pt 0 1)) ∨
        (e = s(bc57_pt 0 0, bc57_pt 0 (-1))))
      then true else false


theorem bea_ce_true_iff (e : Sym2 (Site 2)) :
    bea_ce e = true ↔
      ((∃ k : ℤ, e = s(bc57_pt k 0, bc57_pt (k + 1) 0)) ∨
       (∃ k : ℤ, e = s(bc57_pt k 1, bc57_pt (k + 1) 1)) ∨
       (∃ k : ℤ, e = s(bc57_pt k (-1), bc57_pt (k + 1) (-1))) ∨
       (e = s(bc57_pt 0 0, bc57_pt 0 1)) ∨
       (e = s(bc57_pt 0 0, bc57_pt 0 (-1)))) := by
  classical
  unfold bea_ce
  by_cases h : ((∃ k : ℤ, e = s(bc57_pt k 0, bc57_pt (k + 1) 0)) ∨
       (∃ k : ℤ, e = s(bc57_pt k 1, bc57_pt (k + 1) 1)) ∨
       (∃ k : ℤ, e = s(bc57_pt k (-1), bc57_pt (k + 1) (-1))) ∨
       (e = s(bc57_pt 0 0, bc57_pt 0 1)) ∨
       (e = s(bc57_pt 0 0, bc57_pt 0 (-1))))
  · rw [if_pos h]; exact iff_of_true rfl h
  · rw [if_neg h]; exact iff_of_false (by simp) h


theorem bea_line_open {h : ℤ} (hh : h = 0 ∨ h = 1 ∨ h = -1) (k : ℤ) :
    bea_ce s(bc57_pt k h, bc57_pt (k + 1) h) = true := by
  rcases hh with rfl | rfl | rfl
  · exact (bea_ce_true_iff _).mpr (Or.inl ⟨k, rfl⟩)
  · exact (bea_ce_true_iff _).mpr (Or.inr (Or.inl ⟨k, rfl⟩))
  · exact (bea_ce_true_iff _).mpr (Or.inr (Or.inr (Or.inl ⟨k, rfl⟩)))


theorem bea_bridgeUp_open : bea_ce s(bc57_pt 0 0, bc57_pt 0 1) = true :=
  (bea_ce_true_iff _).mpr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))


theorem bea_bridgeDown_open : bea_ce s(bc57_pt 0 0, bc57_pt 0 (-1)) = true :=
  (bea_ce_true_iff _).mpr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))


theorem bea_vert_adj (h : ℤ) : (hypercubicLattice 2).Adj (bc57_pt 0 h) (bc57_pt 0 (h + 1)) := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp [bc57_pt]




theorem bea_out_O {c h : ℤ} (hc : 1 < c.natAbs ∨ 1 < h.natAbs) :
    bc57_pt c h ∉ bc61_boxAround 2 1 (bc57_pt 0 0) := by
  rw [bc61_mem_boxAround, mem_box]
  simp only [not_forall, not_le]
  rcases hc with h1 | h1
  · exact ⟨0, by simp only [Pi.sub_apply, bc57_pt_fst, sub_zero]; exact h1⟩
  · exact ⟨1, by simp only [Pi.sub_apply, bc57_pt_snd, sub_zero]; exact h1⟩


theorem bea_pin_in {c h : ℤ} (hc : (c - 10).natAbs ≤ 1) (hh : h.natAbs ≤ 1) :
    bc57_pt c h ∈ bc61_boxAround 2 1 (bc57_pt 10 0) := by
  rw [bc61_mem_boxAround, mem_box, Fin.forall_fin_two]
  refine ⟨?_, ?_⟩
  · simp only [Pi.sub_apply, bc57_pt_fst]; exact hc
  · simp only [Pi.sub_apply, bc57_pt_snd, sub_zero]; exact hh


theorem bea_wall9 {h : ℤ} (hh : h = 0 ∨ h = 1 ∨ h = -1) :
    bc57_pt 9 h ∈ bc61_boxAround 2 1 (bc57_pt 10 0) := by
  refine bea_pin_in (by decide) ?_
  rcases hh with rfl | rfl | rfl <;> decide


theorem bea_pin_out_col0 {h : ℤ} : bc57_pt 0 h ∉ bc61_boxAround 2 1 (bc57_pt 10 0) := by
  rw [bc61_mem_boxAround, mem_box]; simp only [not_forall, not_le]
  exact ⟨0, by simp only [Pi.sub_apply, bc57_pt_fst]; omega⟩












theorem bea_pin_col_step {u v : Site 2} (hu : u 0 ≤ 8)
    (hadj : (openSubgraph 2 (removeSites (bc61_boxAround 2 1 (bc57_pt 10 0)) bea_ce)).Adj u v) :
    v 0 ≤ 8 := by
  classical
  obtain ⟨hlat, hopen⟩ := hadj
  unfold removeSites at hopen
  by_cases hc : ∃ t ∈ bc61_boxAround 2 1 (bc57_pt 10 0), t ∈ s(u, v)
  · rw [if_pos hc] at hopen; simp at hopen
  · rw [if_neg hc] at hopen
    have hvB : v ∉ bc61_boxAround 2 1 (bc57_pt 10 0) := fun he =>
      hc ⟨v, he, Sym2.mem_mk_right u v⟩
    rcases (bea_ce_true_iff _).mp hopen with ⟨k, hk⟩ | ⟨k, hk⟩ | ⟨k, hk⟩ | hk | hk
    
    · rw [Sym2.eq_iff] at hk
      rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simp only [bc57_pt_fst] at hu ⊢
        by_contra hcon
        exact hvB (by rw [show k + 1 = 9 by omega]; exact bea_wall9 (Or.inl rfl))
      · simp only [bc57_pt_fst] at hu ⊢; omega
    
    · rw [Sym2.eq_iff] at hk
      rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simp only [bc57_pt_fst] at hu ⊢
        by_contra hcon
        exact hvB (by rw [show k + 1 = 9 by omega]; exact bea_wall9 (Or.inr (Or.inl rfl)))
      · simp only [bc57_pt_fst] at hu ⊢; omega
    
    · rw [Sym2.eq_iff] at hk
      rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simp only [bc57_pt_fst] at hu ⊢
        by_contra hcon
        exact hvB (by rw [show k + 1 = 9 by omega]; exact bea_wall9 (Or.inr (Or.inr rfl)))
      · simp only [bc57_pt_fst] at hu ⊢; omega
    
    · rw [Sym2.eq_iff] at hk
      rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp only [bc57_pt_fst] at hu ⊢ <;> omega
    
    · rw [Sym2.eq_iff] at hk
      rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp only [bc57_pt_fst] at hu ⊢ <;> omega



theorem bea_pin_col_inv {u y : Site 2} (hu : u 0 ≤ 8)
    (hconn : Connected 2 (removeSites (bc61_boxAround 2 1 (bc57_pt 10 0)) bea_ce) u y) :
    y 0 ≤ 8 := by
  obtain ⟨w⟩ := hconn
  induction w with
  | nil => exact hu
  | @cons a b c hab w' ih => exact ih (bea_pin_col_step hu hab)



theorem bea_pinch :
    ¬ (bc67_contractedLattice bea_ce 1 (bc57_pt 10 0)).Reachable (bc57_pt 0 0) (bc57_pt 12 1) := by
  intro h
  have hy : (bc57_pt 12 1) 0 ≤ 8 :=
    bea_pin_col_inv (u := bc57_pt 0 0) (by simp) h
  simp only [bc57_pt_fst] at hy; omega










theorem bea_in_O {c h : ℤ} (hc : c.natAbs ≤ 1) (hh : h.natAbs ≤ 1) :
    bc57_pt c h ∈ bc61_boxAround 2 1 (bc57_pt 0 0) := by
  rw [bc61_mem_boxAround, mem_box, Fin.forall_fin_two]
  refine ⟨?_, ?_⟩
  · simp only [Pi.sub_apply, bc57_pt_fst, sub_zero]; exact hc
  · simp only [Pi.sub_apply, bc57_pt_snd, sub_zero]; exact hh


theorem bea_openAdj {a b h : ℤ} (hh : h = 0 ∨ h = 1 ∨ h = -1) (hab : b = a + 1) :
    (openSubgraph 2 bea_ce).Adj (bc57_pt a h) (bc57_pt b h) := by
  subst hab; exact ⟨bc57_pt_adj a h, bea_line_open hh a⟩




theorem bea_O_height_step {hgt : ℤ} {u v : Site 2} (hu : u 1 = hgt)
    (hadj : (openSubgraph 2 (removeSites (bc61_boxAround 2 1 (bc57_pt 0 0)) bea_ce)).Adj u v) :
    v 1 = hgt := by
  classical
  obtain ⟨hlat, hopen⟩ := hadj
  unfold removeSites at hopen
  by_cases hc : ∃ t ∈ bc61_boxAround 2 1 (bc57_pt 0 0), t ∈ s(u, v)
  · rw [if_pos hc] at hopen; simp at hopen
  · rw [if_neg hc] at hopen
    have hu0 : u ≠ bc57_pt 0 0 := fun he =>
      hc ⟨u, by rw [he]; exact bea_in_O (by decide) (by decide), Sym2.mem_mk_left u v⟩
    have hv0 : v ≠ bc57_pt 0 0 := fun he =>
      hc ⟨v, by rw [he]; exact bea_in_O (by decide) (by decide), Sym2.mem_mk_right u v⟩
    rcases (bea_ce_true_iff _).mp hopen with ⟨k, hk⟩ | ⟨k, hk⟩ | ⟨k, hk⟩ | hk | hk
    · rw [Sym2.eq_iff] at hk
      rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> · simp only [bc57_pt_snd] at hu ⊢; omega
    · rw [Sym2.eq_iff] at hk
      rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> · simp only [bc57_pt_snd] at hu ⊢; omega
    · rw [Sym2.eq_iff] at hk
      rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> · simp only [bc57_pt_snd] at hu ⊢; omega
    · rw [Sym2.eq_iff] at hk
      rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact absurd rfl hu0
      · exact absurd rfl hv0
    · rw [Sym2.eq_iff] at hk
      rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact absurd rfl hu0
      · exact absurd rfl hv0


theorem bea_O_height_inv {hgt : ℤ} {u y : Site 2} (hu : u 1 = hgt)
    (hconn : Connected 2 (removeSites (bc61_boxAround 2 1 (bc57_pt 0 0)) bea_ce) u y) :
    y 1 = hgt := by
  obtain ⟨w⟩ := hconn
  induction w with
  | nil => exact hu
  | @cons a b c hab w' ih => exact ih (bea_O_height_step hu hab)



theorem bea_arm_reach {h : ℤ} (hh : h = 0 ∨ h = 1 ∨ h = -1) (j : ℕ) :
    Connected 2 (removeSites (bc61_boxAround 2 1 (bc57_pt 0 0)) bea_ce)
      (bc57_pt 2 h) (bc57_pt (2 + (j : ℤ)) h) := by
  induction j with
  | zero => simpa using connected_refl _ (bc57_pt 2 h)
  | succ i ih =>
    have hstep : Connected 2 (removeSites (bc61_boxAround 2 1 (bc57_pt 0 0)) bea_ce)
        (bc57_pt (2 + (i : ℤ)) h) (bc57_pt (2 + (i : ℤ) + 1) h) :=
      bc61_cut_adj_connected (bc57_pt_adj _ h) (bea_line_open hh _)
        (bea_out_O (Or.inl (by omega))) (bea_out_O (Or.inl (by omega)))
    have hcast : 2 + ((i + 1 : ℕ) : ℤ) = 2 + (i : ℤ) + 1 := by push_cast; ring
    rw [hcast]; exact ih.trans hstep


theorem bea_arm_infinite {h : ℤ} (hh : h = 0 ∨ h = 1 ∨ h = -1) :
    (cluster 2 (removeSites (bc61_boxAround 2 1 (bc57_pt 0 0)) bea_ce) (bc57_pt 2 h)).Infinite := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun j : ℕ => bc57_pt (2 + (j : ℤ)) h) ?_ ?_
  · intro a b hab
    have h2 := congrArg (fun p : Site 2 => p 0) hab
    simp only [bc57_pt_fst] at h2
    have : (a : ℤ) = (b : ℤ) := by omega
    exact_mod_cast this
  · intro j; exact mem_cluster.mpr (bea_arm_reach hh j)


theorem bea_arm_disc {h h' : ℤ} (hne : h ≠ h') :
    ¬ Connected 2 (removeSites (bc61_boxAround 2 1 (bc57_pt 0 0)) bea_ce)
      (bc57_pt 2 h) (bc57_pt 2 h') := by
  intro hconn
  have hy := bea_O_height_inv (u := bc57_pt 2 h) (by rw [bc57_pt_snd]) hconn
  rw [bc57_pt_snd] at hy
  exact hne hy.symm


theorem bea_horiz_from0 {h : ℤ} (hh : h = 0 ∨ h = 1 ∨ h = -1) (n : ℤ) :
    Connected 2 bea_ce (bc57_pt 0 h) (bc57_pt n h) := by
  induction n using Int.induction_on with
  | zero => exact connected_refl _ _
  | succ i ih =>
    have step : Connected 2 bea_ce (bc57_pt (i : ℤ) h) (bc57_pt ((i : ℤ) + 1) h) :=
      IsOpenEdge.connected ⟨bc57_pt_adj (i : ℤ) h, bea_line_open hh (i : ℤ)⟩
    exact ih.trans step
  | pred i ih =>
    have step : Connected 2 bea_ce (bc57_pt (-(i : ℤ) - 1) h) (bc57_pt (-(i : ℤ)) h) := by
      have hstep := IsOpenEdge.connected
        (d := 2) (ω := bea_ce) ⟨bc57_pt_adj (-(i : ℤ) - 1) h, bea_line_open hh (-(i : ℤ) - 1)⟩
      rwa [show (-(i : ℤ) - 1) + 1 = -(i : ℤ) by ring] at hstep
    exact ih.trans step.symm


theorem bea_O_to_arm {h : ℤ} (hh : h = 0 ∨ h = 1 ∨ h = -1) :
    Connected 2 bea_ce (bc57_pt 0 0) (bc57_pt 2 h) := by
  rcases hh with rfl | rfl | rfl
  · exact bea_horiz_from0 (Or.inl rfl) 2
  · have hbr : Connected 2 bea_ce (bc57_pt 0 0) (bc57_pt 0 1) := by
      have hadj : (hypercubicLattice 2).Adj (bc57_pt 0 0) (bc57_pt 0 1) := by
        rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp [bc57_pt]
      exact IsOpenEdge.connected ⟨hadj, bea_bridgeUp_open⟩
    exact hbr.trans (bea_horiz_from0 (Or.inr (Or.inl rfl)) 2)
  · have hbr : Connected 2 bea_ce (bc57_pt 0 0) (bc57_pt 0 (-1)) := by
      have hadj : (hypercubicLattice 2).Adj (bc57_pt 0 0) (bc57_pt 0 (-1)) := by
        rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp [bc57_pt]
      exact IsOpenEdge.connected ⟨hadj, bea_bridgeDown_open⟩
    exact hbr.trans (bea_horiz_from0 (Or.inr (Or.inr rfl)) 2)





theorem bea_genuineTrif : btr_IsGenuineCoarseTrif bea_ce 1 (bc57_pt 0 0) := by
  refine ⟨bc57_pt 2 1, bc57_pt 2 0, bc57_pt 2 (-1),
    ⟨bc57_pt 1 1, bea_in_O (by decide) (by decide), bea_openAdj (Or.inr (Or.inl rfl)) (by norm_num)⟩,
    ⟨bc57_pt 1 0, bea_in_O (by decide) (by decide), bea_openAdj (Or.inl rfl) (by norm_num)⟩,
    ⟨bc57_pt 1 (-1), bea_in_O (by decide) (by decide), bea_openAdj (Or.inr (Or.inr rfl)) (by norm_num)⟩,
    ⟨bea_O_to_arm (Or.inr (Or.inl rfl)), bea_O_to_arm (Or.inl rfl), bea_O_to_arm (Or.inr (Or.inr rfl))⟩,
    ⟨bea_arm_infinite (Or.inr (Or.inl rfl)), bea_arm_infinite (Or.inl rfl),
      bea_arm_infinite (Or.inr (Or.inr rfl))⟩,
    bea_arm_disc (by decide), bea_arm_disc (by decide), bea_arm_disc (by decide)⟩



theorem bea_gnTrif : bc67_IsGnTrifurcation bea_ce 1 (bc57_pt 0 0) :=
  bc67_gnTrif_of_coarseTrif bea_ce 1 (bc57_pt 0 0) (btr_genuine_imp_bc61 bea_genuineTrif)





noncomputable def bea_arm (i : Fin 3) : Site 2 :=
  if i = 0 then bc57_pt 12 1 else if i = 1 then bc57_pt 10 0 else bc57_pt 2 (-1)

@[simp] theorem bea_arm_zero : bea_arm 0 = bc57_pt 12 1 := rfl
@[simp] theorem bea_arm_one : bea_arm 1 = bc57_pt 10 0 := rfl




theorem bea_repRoute_false :
    ¬ bcr_RepRoute bea_ce 1 (bc57_pt 0 0) bea_arm := by
  intro h
  have hreach := h 0 1 (by decide)
  rw [bea_arm_one, bea_arm_zero] at hreach
  exact bea_pinch hreach









theorem bea_genuineTrif_entry_false :
    btr_IsGenuineCoarseTrif bea_ce 1 (bc57_pt 0 0) ∧
      ¬ (bc67_contractedLattice bea_ce 1 (bea_arm 1)).Reachable (bc57_pt 0 0) (bea_arm 0) ∧
      ¬ bcr_RepRoute bea_ce 1 (bc57_pt 0 0) bea_arm := by
  refine ⟨bea_genuineTrif, ?_, bea_repRoute_false⟩
  rw [bea_arm_one, bea_arm_zero]
  exact bea_pinch

#check @bea_genuineTrif_entry_false

end StatMech.Walls
