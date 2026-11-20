/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

















































































































































import Mathlib
import Code.Walls.bc83genuinetrif
import Code.Walls.bc78mergedichotomy
import Code.Percolation.BKSpanningTreeClose
import Code.Percolation.TrifurcationCount
import Code.Percolation.TrifurcationConstruction

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}



















theorem bc88_genuine_count_le_boundary_of_openForest (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : bst_BoxOpenForest ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  bst_Tcount_le_boundary_of_boxOpenForest ω n h







theorem bc88_branch_le_leaf_unconditional {W : Type*} [Fintype W] [Nonempty W] (G : SimpleGraph W)
    [DecidableRel G.Adj] (hacyc : G.IsAcyclic) (hmin : ∀ v, 1 ≤ G.degree v) :
    (Finset.univ.filter (fun v => 3 ≤ G.degree v)).card
      ≤ (Finset.univ.filter (fun v => G.degree v = 1)).card :=
  flc2_forest_internal_le_leaves G hacyc hmin




























theorem bc88_left_ray_step {a b : Site 2}
    (hab : (openSubgraph 2 (removeSite (bc57_pt 0 1) bc60_upperLines)).Adj a b)
    (ha : a 1 = 1 ∧ a 0 ≤ -1) : b 1 = 1 ∧ b 0 ≤ -1 := by
  obtain ⟨hlat, hopen⟩ := hab
  
  have h0 : (bc57_pt 0 1) ∉ s(a, b) := by
    intro hmem; rw [removeSite_apply_of_mem hmem] at hopen; exact absurd hopen (by decide)
  rw [removeSite_apply_of_notMem h0] at hopen
  
  obtain ⟨_, _, hab1⟩ := bc60_open_edge_heights hopen
  refine ⟨by rw [← hab1]; exact ha.1, ?_⟩
  
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hlat
  have hheight : a 1 = b 1 := hab1
  have hcol : (a 0 - b 0).natAbs = 1 := by omega
  
  rcases (Int.natAbs_eq_iff).mp hcol with h | h
  · 
    omega
  · 
    have hb0 : b 0 = a 0 + 1 := by omega
    by_contra hbc
    
    have hb0z : b 0 = 0 := by omega
    have hb1z : b 1 = 1 := by rw [← hab1]; exact ha.1
    have hbeq : b = bc57_pt 0 1 := by
      funext i; fin_cases i
      · simpa [bc57_pt] using hb0z
      · simpa [bc57_pt] using hb1z
    exact h0 (by rw [hbeq]; exact Sym2.mem_mk_right _ _)




theorem bc88_left_ray_invariant {y : Site 2}
    (hconn : Connected 2 (removeSite (bc57_pt 0 1) bc60_upperLines) (bc57_pt (-1) 1) y) :
    y 1 = 1 ∧ y 0 ≤ -1 := by
  obtain ⟨walk⟩ := hconn
  
  suffices h : ∀ (p q : Site 2)
      (w : (openSubgraph 2 (removeSite (bc57_pt 0 1) bc60_upperLines)).Walk p q),
      (p 1 = 1 ∧ p 0 ≤ -1) → (q 1 = 1 ∧ q 0 ≤ -1) by
    exact h _ _ walk (by simp [bc57_pt])
  intro p q w
  induction w with
  | nil => exact fun hp => hp
  | @cons a b c hab w' ih =>
    intro ha
    exact ih (bc88_left_ray_step hab ha)



theorem bc88_right_ray_step {a b : Site 2}
    (hab : (openSubgraph 2 (removeSite (bc57_pt 0 1) bc60_upperLines)).Adj a b)
    (ha : a 1 = 1 ∧ 1 ≤ a 0) : b 1 = 1 ∧ 1 ≤ b 0 := by
  obtain ⟨hlat, hopen⟩ := hab
  have h0 : (bc57_pt 0 1) ∉ s(a, b) := by
    intro hmem; rw [removeSite_apply_of_mem hmem] at hopen; exact absurd hopen (by decide)
  rw [removeSite_apply_of_notMem h0] at hopen
  obtain ⟨_, _, hab1⟩ := bc60_open_edge_heights hopen
  refine ⟨by rw [← hab1]; exact ha.1, ?_⟩
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hlat
  have hheight : a 1 = b 1 := hab1
  have hcol : (a 0 - b 0).natAbs = 1 := by omega
  rcases (Int.natAbs_eq_iff).mp hcol with h | h
  · 
    have hb0 : b 0 = a 0 - 1 := by omega
    by_contra hbc
    have hb0z : b 0 = 0 := by omega
    have hb1z : b 1 = 1 := by rw [← hab1]; exact ha.1
    have hbeq : b = bc57_pt 0 1 := by
      funext i; fin_cases i
      · simpa [bc57_pt] using hb0z
      · simpa [bc57_pt] using hb1z
    exact h0 (by rw [hbeq]; exact Sym2.mem_mk_right _ _)
  · 
    omega



theorem bc88_right_ray_invariant {y : Site 2}
    (hconn : Connected 2 (removeSite (bc57_pt 0 1) bc60_upperLines) (bc57_pt 1 1) y) :
    y 1 = 1 ∧ 1 ≤ y 0 := by
  obtain ⟨walk⟩ := hconn
  suffices h : ∀ (p q : Site 2)
      (w : (openSubgraph 2 (removeSite (bc57_pt 0 1) bc60_upperLines)).Walk p q),
      (p 1 = 1 ∧ 1 ≤ p 0) → (q 1 = 1 ∧ 1 ≤ q 0) by
    exact h _ _ walk (by simp [bc57_pt])
  intro p q w
  induction w with
  | nil => exact fun hp => hp
  | @cons a b c hab w' ih =>
    intro ha
    exact ih (bc88_right_ray_step hab ha)






theorem bc88_left_right_disconnected :
    ¬ Connected 2 (removeSite (bc57_pt 0 1) bc60_upperLines) (bc57_pt (-1) 1) (bc57_pt 1 1) := by
  intro hconn
  have := (bc88_left_ray_invariant hconn).2
  rw [bc57_pt_fst] at this
  omega




theorem bc88_center_left_disconnected :
    ¬ Connected 2 (removeSite (bc57_pt 0 1) bc60_upperLines) (bc57_pt 0 1) (bc57_pt (-1) 1) := by
  intro hconn
  have := (bc88_left_ray_invariant hconn.symm).2
  rw [bc57_pt_fst] at this
  omega



theorem bc88_center_right_disconnected :
    ¬ Connected 2 (removeSite (bc57_pt 0 1) bc60_upperLines) (bc57_pt 0 1) (bc57_pt 1 1) := by
  intro hconn
  have := (bc88_right_ray_invariant hconn.symm).2
  rw [bc57_pt_fst] at this
  omega





theorem bc88_line_pts_infinite (m : ℤ) :
    (cluster 2 bc60_upperLines (bc57_pt m 1)).Infinite := by
  
  have hconn : Connected 2 bc60_upperLines (bc57_pt m 1) (bc57_pt 0 1) :=
    connected_mono (removeSite_le 0 bc60_upperLines) (bc60_line1_connected_zero m)
  rw [cluster_eq_of_connected hconn]
  exact bc60_cluster_infinite (le_refl 1)








theorem bc88_upperLines_isTrifurcation :
    IsTrifurcation 2 bc60_upperLines (bc57_pt 0 1) := by
  refine ⟨bc57_pt 0 1, bc57_pt (-1) 1, bc57_pt 1 1, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩,
    ?_, ?_, ?_⟩
  
  · intro h; have := congrArg (fun f => f 0) h; simp only [bc57_pt_fst] at this; omega
  · intro h; have := congrArg (fun f => f 0) h; simp only [bc57_pt_fst] at this; omega
  · intro h; have := congrArg (fun f => f 0) h; simp only [bc57_pt_fst] at this; omega
  
  · exact connected_refl _ _
  · exact connected_mono (removeSite_le 0 bc60_upperLines) (bc60_line1_all_connected 0 (-1))
  · exact connected_mono (removeSite_le 0 bc60_upperLines) (bc60_line1_all_connected 0 1)
  
  · exact bc88_line_pts_infinite 0
  · exact bc88_line_pts_infinite (-1)
  · exact bc88_line_pts_infinite 1
  
  · exact bc88_center_left_disconnected
  · exact bc88_center_right_disconnected
  · exact bc88_left_right_disconnected










theorem bc88_left_ray_step_gen {c : ℤ} {a b : Site 2}
    (hab : (openSubgraph 2 (removeSite (bc57_pt c 1) bc60_upperLines)).Adj a b)
    (ha : a 1 = 1 ∧ a 0 ≤ c - 1) : b 1 = 1 ∧ b 0 ≤ c - 1 := by
  obtain ⟨hlat, hopen⟩ := hab
  have h0 : (bc57_pt c 1) ∉ s(a, b) := by
    intro hmem; rw [removeSite_apply_of_mem hmem] at hopen; exact absurd hopen (by decide)
  rw [removeSite_apply_of_notMem h0] at hopen
  obtain ⟨_, _, hab1⟩ := bc60_open_edge_heights hopen
  refine ⟨by rw [← hab1]; exact ha.1, ?_⟩
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hlat
  have hheight : a 1 = b 1 := hab1
  have hcol : (a 0 - b 0).natAbs = 1 := by omega
  rcases (Int.natAbs_eq_iff).mp hcol with h | h
  · omega
  · have hb0 : b 0 = a 0 + 1 := by omega
    by_contra hbc
    have hb0z : b 0 = c := by omega
    have hb1z : b 1 = 1 := by rw [← hab1]; exact ha.1
    have hbeq : b = bc57_pt c 1 := by
      funext i; fin_cases i
      · simpa [bc57_pt] using hb0z
      · simpa [bc57_pt] using hb1z
    exact h0 (by rw [hbeq]; exact Sym2.mem_mk_right _ _)

theorem bc88_right_ray_step_gen {c : ℤ} {a b : Site 2}
    (hab : (openSubgraph 2 (removeSite (bc57_pt c 1) bc60_upperLines)).Adj a b)
    (ha : a 1 = 1 ∧ c + 1 ≤ a 0) : b 1 = 1 ∧ c + 1 ≤ b 0 := by
  obtain ⟨hlat, hopen⟩ := hab
  have h0 : (bc57_pt c 1) ∉ s(a, b) := by
    intro hmem; rw [removeSite_apply_of_mem hmem] at hopen; exact absurd hopen (by decide)
  rw [removeSite_apply_of_notMem h0] at hopen
  obtain ⟨_, _, hab1⟩ := bc60_open_edge_heights hopen
  refine ⟨by rw [← hab1]; exact ha.1, ?_⟩
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hlat
  have hheight : a 1 = b 1 := hab1
  have hcol : (a 0 - b 0).natAbs = 1 := by omega
  rcases (Int.natAbs_eq_iff).mp hcol with h | h
  · have hb0 : b 0 = a 0 - 1 := by omega
    by_contra hbc
    have hb0z : b 0 = c := by omega
    have hb1z : b 1 = 1 := by rw [← hab1]; exact ha.1
    have hbeq : b = bc57_pt c 1 := by
      funext i; fin_cases i
      · simpa [bc57_pt] using hb0z
      · simpa [bc57_pt] using hb1z
    exact h0 (by rw [hbeq]; exact Sym2.mem_mk_right _ _)
  · omega


theorem bc88_left_ray_invariant_gen {c : ℤ} {y : Site 2}
    (hconn : Connected 2 (removeSite (bc57_pt c 1) bc60_upperLines) (bc57_pt (c - 1) 1) y) :
    y 1 = 1 ∧ y 0 ≤ c - 1 := by
  obtain ⟨walk⟩ := hconn
  suffices h : ∀ (p q : Site 2)
      (w : (openSubgraph 2 (removeSite (bc57_pt c 1) bc60_upperLines)).Walk p q),
      (p 1 = 1 ∧ p 0 ≤ c - 1) → (q 1 = 1 ∧ q 0 ≤ c - 1) by
    exact h _ _ walk (by simp [bc57_pt])
  intro p q w
  induction w with
  | nil => exact fun hp => hp
  | @cons a b c' hab w' ih => intro ha; exact ih (bc88_left_ray_step_gen hab ha)

theorem bc88_right_ray_invariant_gen {c : ℤ} {y : Site 2}
    (hconn : Connected 2 (removeSite (bc57_pt c 1) bc60_upperLines) (bc57_pt (c + 1) 1) y) :
    y 1 = 1 ∧ c + 1 ≤ y 0 := by
  obtain ⟨walk⟩ := hconn
  suffices h : ∀ (p q : Site 2)
      (w : (openSubgraph 2 (removeSite (bc57_pt c 1) bc60_upperLines)).Walk p q),
      (p 1 = 1 ∧ c + 1 ≤ p 0) → (q 1 = 1 ∧ c + 1 ≤ q 0) by
    exact h _ _ walk (by simp [bc57_pt])
  intro p q w
  induction w with
  | nil => exact fun hp => hp
  | @cons a b c' hab w' ih => intro ha; exact ih (bc88_right_ray_step_gen hab ha)






theorem bc88_upperLines_isTrifurcation_general (k : ℤ) :
    IsTrifurcation 2 bc60_upperLines (bc57_pt k 1) := by
  refine ⟨bc57_pt k 1, bc57_pt (k - 1) 1, bc57_pt (k + 1) 1, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro h; have := congrArg (fun f => f 0) h; simp only [bc57_pt_fst] at this; omega
  · intro h; have := congrArg (fun f => f 0) h; simp only [bc57_pt_fst] at this; omega
  · intro h; have := congrArg (fun f => f 0) h; simp only [bc57_pt_fst] at this; omega
  · exact connected_refl _ _
  · exact connected_mono (removeSite_le 0 bc60_upperLines) (bc60_line1_all_connected k (k - 1))
  · exact connected_mono (removeSite_le 0 bc60_upperLines) (bc60_line1_all_connected k (k + 1))
  · exact bc88_line_pts_infinite k
  · exact bc88_line_pts_infinite (k - 1)
  · exact bc88_line_pts_infinite (k + 1)
  · 
    intro hconn
    have := (bc88_left_ray_invariant_gen hconn.symm).2
    rw [bc57_pt_fst] at this; omega
  · intro hconn
    have := (bc88_right_ray_invariant_gen hconn.symm).2
    rw [bc57_pt_fst] at this; omega
  · intro hconn
    have := (bc88_left_ray_invariant_gen hconn).2
    rw [bc57_pt_fst] at this; omega














theorem bc88_open_nbr_of_center {v : Site 2}
    (hadj : (openSubgraph 2 bc60_upperLines).Adj (bc57_pt 0 1) v) :
    v = bc57_pt 1 1 ∨ v = bc57_pt (-1) 1 := by
  obtain ⟨hlat, hopen⟩ := hadj
  obtain ⟨_, _, hh⟩ := bc60_open_edge_heights hopen
  rw [bc57_pt_snd] at hh
  
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hlat
  rw [bc57_pt_fst, bc57_pt_snd] at hlat
  have hv1 : v 1 = 1 := hh.symm
  have hcol : (v 0 - 0).natAbs = 1 := by omega
  have : v 0 = 1 ∨ v 0 = -1 := by
    rcases (Int.natAbs_eq_iff).mp hcol with h | h <;> omega
  rcases this with h | h
  · left; funext i; fin_cases i
    · simpa [bc57_pt] using h
    · simpa [bc57_pt] using hv1
  · right; funext i; fin_cases i
    · simpa [bc57_pt] using h
    · simpa [bc57_pt] using hv1






theorem bc88_center_open_degree_le_two {Vset : Finset (Site 2)}
    (F : SimpleGraph (↑Vset : Type)) [DecidableRel F.Adj]
    (hπ : ∀ u v, F.Adj u v → (openSubgraph 2 bc60_upperLines).Adj (u : Site 2) (v : Site 2))
    (vx : (↑Vset : Type)) (hvx : (vx : Site 2) = bc57_pt 0 1) :
    F.degree vx ≤ 2 := by
  classical
  
  have hmap : ∀ w ∈ F.neighborFinset vx, (w : Site 2) ∈ ({bc57_pt 1 1, bc57_pt (-1) 1} : Finset (Site 2)) := by
    intro w hw
    rw [F.mem_neighborFinset] at hw
    have hadj : (openSubgraph 2 bc60_upperLines).Adj (vx : Site 2) (w : Site 2) := hπ _ _ hw
    rw [hvx] at hadj
    rcases bc88_open_nbr_of_center hadj with h | h <;> simp [h]
  have hcard : (F.neighborFinset vx).card ≤ ({bc57_pt 1 1, bc57_pt (-1) 1} : Finset (Site 2)).card := by
    refine Finset.card_le_card_of_injOn (fun w => (w : Site 2)) hmap ?_
    intro u _ v _ huv; exact Subtype.val_injective huv
  have htwo : ({bc57_pt 1 1, bc57_pt (-1) 1} : Finset (Site 2)).card ≤ 2 := by
    refine le_trans (Finset.card_insert_le _ _) ?_
    simp
  rw [← F.card_neighborFinset_eq_degree]
  exact le_trans hcard htwo






theorem bc88_upperLines_open_degree_two {Vset : Finset (Site 2)}
    (F : SimpleGraph (↑Vset : Type)) [DecidableRel F.Adj]
    (hπ : ∀ u v, F.Adj u v → (openSubgraph 2 bc60_upperLines).Adj (u : Site 2) (v : Site 2))
    (vx : (↑Vset : Type)) (hvx : (vx : Site 2) = bc57_pt 0 1) :
    F.degree vx ≤ 2 :=
  bc88_center_open_degree_le_two F hπ vx hvx








theorem bc88_upperLines_boxOpenForest_fails {n : ℕ} (hn : 1 ≤ n) :
    ¬ bst_BoxOpenForest bc60_upperLines n := by
  classical
  rintro ⟨Vset, hVne, F, hF, vx, b, hπ, hacyc, hmin, htriData, hleaf⟩
  
  have hxbox : bc57_pt 0 1 ∈ box 2 n := bc60_pt_zero_mem_box (by simpa using hn)
  
  have htri : IsTrifurcation 2 bc60_upperLines (bc57_pt 0 1) := bc88_upperLines_isTrifurcation
  
  obtain ⟨hvx, hreach, hcut⟩ := htriData (bc57_pt 0 1) hxbox htri
  have hdeg3 : 3 ≤ F.degree (vx (bc57_pt 0 1)) :=
    bst_deg_ge_three_of_boxOpenForest hπ hxbox htri hvx hreach hcut
  
  have hdeg2 : F.degree (vx (bc57_pt 0 1)) ≤ 2 :=
    bc88_center_open_degree_le_two F hπ (vx (bc57_pt 0 1)) hvx
  omega








theorem bc88_coarse_fires_upperLines {L : ℕ} (hL : 3 ≤ L) :
    bc61_IsCoarseTrifurcation bc60_upperLines L (0 : Site 2) :=
  bc61_wholeBox_severs_upperLines hL

































theorem bc88_status :
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (n : ℕ),
      bst_BoxOpenForest ω n → Tcount 2 ω n ≤ boxSV_boundaryCard 2 n) ∧
    
    (∀ k : ℤ, IsTrifurcation 2 bc60_upperLines (bc57_pt k 1)) ∧
    
    (∀ n : ℕ, 1 ≤ n → ¬ bst_BoxOpenForest bc60_upperLines n) ∧
    
    (∀ L : ℕ, 3 ≤ L → bc61_IsCoarseTrifurcation bc60_upperLines L (0 : Site 2)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ω n h; exact bc88_genuine_count_le_boundary_of_openForest ω n h
  · intro k; exact bc88_upperLines_isTrifurcation_general k
  · intro n hn; exact bc88_upperLines_boxOpenForest_fails hn
  · intro L hL; exact bc88_coarse_fires_upperLines hL

end StatMech.Walls
