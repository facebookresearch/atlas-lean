/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

























































import Mathlib
import Code.Walls.bc58wholebox
import Code.Walls.bc49finiteenergy

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}




















def bc59_DisjointCorridors (ω : ConfigSpace (Sym2 (Site d))) : Prop :=
  ∃ (G : Finset (Sym2 (Site d))) (a₁ a₂ a₃ : Site d),
    (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧
    (s((0 : Site d), a₁) ∈ G ∧ s((0 : Site d), a₂) ∈ G ∧ s((0 : Site d), a₃) ∈ G) ∧
    ((hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
      (hypercubicLattice d).Adj 0 a₃) ∧
    ((cluster d (removeSite 0 (forceOpenFinset G ω)) a₁).Infinite ∧
      (cluster d (removeSite 0 (forceOpenFinset G ω)) a₂).Infinite ∧
      (cluster d (removeSite 0 (forceOpenFinset G ω)) a₃).Infinite) ∧
    (¬ Connected d (removeSite 0 (forceOpenFinset G ω)) a₁ a₂ ∧
     ¬ Connected d (removeSite 0 (forceOpenFinset G ω)) a₁ a₃ ∧
     ¬ Connected d (removeSite 0 (forceOpenFinset G ω)) a₂ a₃)





theorem bc59_corridors_give_trifurcation (ω : ConfigSpace (Sym2 (Site d)))
    (h : bc59_DisjointCorridors ω) :
    ∃ G : Finset (Sym2 (Site d)), bc47_IsClassicalTrifurcation (forceOpenFinset G ω) 0 := by
  obtain ⟨G, a₁, a₂, a₃, hne, ⟨hG1, hG2, hG3⟩, ⟨hadj1, hadj2, hadj3⟩,
    ⟨hi1, hi2, hi3⟩, ⟨hs12, hs13, hs23⟩⟩ := h
  refine ⟨G, a₁, a₂, a₃, hne, ⟨?_, ?_, ?_⟩, ⟨hi1, hi2, hi3⟩, ⟨hs12, hs13, hs23⟩⟩
  · exact ⟨hadj1, forceOpenFinset_of_mem hG1 ω⟩
  · exact ⟨hadj2, forceOpenFinset_of_mem hG2 ω⟩
  · exact ⟨hadj3, forceOpenFinset_of_mem hG3 ω⟩









def bc59_HasDisjointCorridors (d n : ℕ) : Prop :=
  ∀ ω ∈ threeMeetBox d n, bc59_DisjointCorridors ω



theorem bc59_originTrifModification_of_hasCorridors {n : ℕ}
    (h : bc59_HasDisjointCorridors d n) : bc58_OriginTrifModification d n := by
  intro ω hω
  exact bc59_corridors_give_trifurcation ω (h ω hω)






theorem bc59_burton_keane_bernoulli_of_hasCorridors (hd : 1 ≤ d)
    (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (h : ∀ n : ℕ, bc59_HasDisjointCorridors d n) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 0} = 1 ∨
      bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  bc58_burton_keane_bernoulli_of_originTrifModification hd p hp1 hp0
    (fun n => bc59_originTrifModification_of_hasCorridors (h n))



















def bc59_a1 : Site 2 := bc57_pt 1 0
def bc59_a2 : Site 2 := bc57_pt (-1) 0
def bc59_a3 : Site 2 := bc57_pt 0 1



noncomputable def bc59_G : Finset (Sym2 (Site 2)) :=
  {s((0 : Site 2), bc59_a1), s((0 : Site 2), bc59_a2), s((0 : Site 2), bc59_a3),
   s(bc57_pt 0 1, bc57_pt 0 2)}


noncomputable def bc59_omega' : ConfigSpace (Sym2 (Site 2)) :=
  forceOpenFinset bc59_G bc57_evenLines








theorem bc59_origin_eq : (0 : Site 2) = bc57_pt 0 0 := by
  funext i; fin_cases i <;> simp [bc57_pt]


theorem bc59_pt_eq_origin_iff {a b : ℤ} : bc57_pt a b = (0 : Site 2) ↔ a = 0 ∧ b = 0 := by
  rw [bc59_origin_eq]
  constructor
  · intro h
    have h0 := congrArg (fun f => f 0) h
    have h1 := congrArg (fun f => f 1) h
    simp only [bc57_pt_fst, bc57_pt_snd] at h0 h1
    exact ⟨h0, h1⟩
  · rintro ⟨ha, hb⟩; rw [ha, hb]


theorem bc59_corridor_open :
    (removeSite 0 bc59_omega') s(bc57_pt 0 1, bc57_pt 0 2) = true := by
  have h0 : (0 : Site 2) ∉ s(bc57_pt 0 1, bc57_pt 0 2) := by
    rw [Sym2.mem_iff]
    rintro (h | h) <;>
      exact absurd (bc59_pt_eq_origin_iff.mp h.symm) (by decide)
  rw [removeSite_apply_of_notMem h0]
  exact forceOpenFinset_of_mem (by simp [bc59_G]) bc57_evenLines




theorem bc59_open_edge_dichotomy {u v : Site 2}
    (hopen : (removeSite 0 bc59_omega') s(u, v) = true) :
    ((0 : Site 2) ∉ s(u, v)) ∧
      ((∃ k m : ℤ, s(u, v) = s(bc57_pt k (2 * m), bc57_pt (k + 1) (2 * m))) ∨
        s(u, v) = s(bc57_pt 0 1, bc57_pt 0 2)) := by
  classical
  
  have h0 : (0 : Site 2) ∉ s(u, v) := by
    intro hmem
    rw [removeSite_apply_of_mem hmem] at hopen
    exact absurd hopen (by decide)
  refine ⟨h0, ?_⟩
  rw [removeSite_apply_of_notMem h0, bc59_omega', forceOpenFinset] at hopen
  by_cases hG : s(u, v) ∈ bc59_G
  · 
    simp only [bc59_G, Finset.mem_insert, Finset.mem_singleton] at hG
    rcases hG with h | h | h | h
    · exact absurd (h ▸ Sym2.mem_mk_left _ _) h0
    · exact absurd (h ▸ Sym2.mem_mk_left _ _) h0
    · exact absurd (h ▸ Sym2.mem_mk_left _ _) h0
    · exact Or.inr h
  · 
    rw [if_neg hG, bc57_evenLines] at hopen
    by_cases hk : ∃ k m : ℤ, s(u, v) = s(bc57_pt k (2 * m), bc57_pt (k + 1) (2 * m))
    · exact Or.inl hk
    · rw [if_neg hk] at hopen; exact absurd hopen (by decide)














theorem bc59_R_step {u v : Site 2} (hu0 : u 1 = 0) (hu1 : 1 ≤ u 0)
    (hadj : (openSubgraph 2 (removeSite 0 bc59_omega')).Adj u v) : v 1 = 0 ∧ 1 ≤ v 0 := by
  obtain ⟨_, hopen⟩ := hadj
  obtain ⟨h0, hcases⟩ := bc59_open_edge_dichotomy hopen
  
  rw [Sym2.mem_iff] at h0; push Not at h0
  obtain ⟨hune, hvne⟩ := h0
  rcases hcases with ⟨k, m, hkm⟩ | hc
  · 
    rw [Sym2.eq_iff] at hkm
    rcases hkm with ⟨hu', hv'⟩ | ⟨hu', hv'⟩
    · 
      have hu0' : (2 * m : ℤ) = 0 := by rw [hu', bc57_pt_snd] at hu0; exact hu0
      have huc : (k : ℤ) = u 0 := by rw [hu', bc57_pt_fst]
      have hvne0 : ¬ (k + 1 = 0 ∧ 2 * m = 0) := by
        rw [hv'] at hvne; exact fun h => hvne (by rw [bc59_origin_eq, h.1, h.2])
      rw [hv', bc57_pt_snd, bc57_pt_fst]
      exact ⟨hu0', by omega⟩
    · 
      have hu0' : (2 * m : ℤ) = 0 := by rw [hu', bc57_pt_snd] at hu0; exact hu0
      have huc : (k + 1 : ℤ) = u 0 := by rw [hu', bc57_pt_fst]
      have hvne0 : ¬ (k = 0 ∧ 2 * m = 0) := by
        rw [hv'] at hvne; exact fun h => hvne (by rw [bc59_origin_eq, h.1, h.2])
      rw [hv', bc57_pt_snd, bc57_pt_fst]
      exact ⟨hu0', by omega⟩
  · 
    rw [Sym2.eq_iff] at hc
    rcases hc with ⟨hu', _⟩ | ⟨hu', _⟩ <;>
      · rw [hu', bc57_pt_snd] at hu0; exact absurd hu0 (by decide)



theorem bc59_L_step {u v : Site 2} (hu0 : u 1 = 0) (hu1 : u 0 ≤ -1)
    (hadj : (openSubgraph 2 (removeSite 0 bc59_omega')).Adj u v) : v 1 = 0 ∧ v 0 ≤ -1 := by
  obtain ⟨_, hopen⟩ := hadj
  obtain ⟨h0, hcases⟩ := bc59_open_edge_dichotomy hopen
  rw [Sym2.mem_iff] at h0; push Not at h0
  obtain ⟨hune, hvne⟩ := h0
  rcases hcases with ⟨k, m, hkm⟩ | hc
  · rw [Sym2.eq_iff] at hkm
    rcases hkm with ⟨hu', hv'⟩ | ⟨hu', hv'⟩
    · have hu0' : (2 * m : ℤ) = 0 := by rw [hu', bc57_pt_snd] at hu0; exact hu0
      have huc : (k : ℤ) = u 0 := by rw [hu', bc57_pt_fst]
      have hvne0 : ¬ (k + 1 = 0 ∧ 2 * m = 0) := by
        rw [hv'] at hvne; exact fun h => hvne (by rw [bc59_origin_eq, h.1, h.2])
      rw [hv', bc57_pt_snd, bc57_pt_fst]
      exact ⟨hu0', by omega⟩
    · have hu0' : (2 * m : ℤ) = 0 := by rw [hu', bc57_pt_snd] at hu0; exact hu0
      have huc : (k + 1 : ℤ) = u 0 := by rw [hu', bc57_pt_fst]
      have hvne0 : ¬ (k = 0 ∧ 2 * m = 0) := by
        rw [hv'] at hvne; exact fun h => hvne (by rw [bc59_origin_eq, h.1, h.2])
      rw [hv', bc57_pt_snd, bc57_pt_fst]
      exact ⟨hu0', by omega⟩
  · rw [Sym2.eq_iff] at hc
    rcases hc with ⟨hu', _⟩ | ⟨hu', _⟩ <;>
      · rw [hu', bc57_pt_snd] at hu0; exact absurd hu0 (by decide)




theorem bc59_T_step {u v : Site 2} (hu1 : 1 ≤ u 1)
    (hadj : (openSubgraph 2 (removeSite 0 bc59_omega')).Adj u v) : 1 ≤ v 1 := by
  obtain ⟨_, hopen⟩ := hadj
  obtain ⟨_, hcases⟩ := bc59_open_edge_dichotomy hopen
  rcases hcases with ⟨k, m, hkm⟩ | hc
  · rw [Sym2.eq_iff] at hkm
    rcases hkm with ⟨hu', hv'⟩ | ⟨hu', hv'⟩
    · have : (2 * m : ℤ) = u 1 := by rw [hu', bc57_pt_snd]
      rw [hv', bc57_pt_snd]; omega
    · have : (2 * m : ℤ) = u 1 := by rw [hu', bc57_pt_snd]
      rw [hv', bc57_pt_snd]; omega
  · rw [Sym2.eq_iff] at hc
    rcases hc with ⟨_, hv'⟩ | ⟨_, hv'⟩
    · have : v 1 = 2 := by rw [hv', bc57_pt_snd]
      omega
    · have : v 1 = 1 := by rw [hv', bc57_pt_snd]
      omega








theorem bc59_R_invariant {u y : Site 2} (hu0 : u 1 = 0) (hu1 : 1 ≤ u 0)
    (hconn : Connected 2 (removeSite 0 bc59_omega') u y) : y 1 = 0 ∧ 1 ≤ y 0 := by
  obtain ⟨w⟩ := hconn
  induction w with
  | nil => exact ⟨hu0, hu1⟩
  | @cons a b c hab w' ih =>
    obtain ⟨hb0, hb1⟩ := bc59_R_step hu0 hu1 hab
    exact ih hb0 hb1


theorem bc59_L_invariant {u y : Site 2} (hu0 : u 1 = 0) (hu1 : u 0 ≤ -1)
    (hconn : Connected 2 (removeSite 0 bc59_omega') u y) : y 1 = 0 ∧ y 0 ≤ -1 := by
  obtain ⟨w⟩ := hconn
  induction w with
  | nil => exact ⟨hu0, hu1⟩
  | @cons a b c hab w' ih =>
    obtain ⟨hb0, hb1⟩ := bc59_L_step hu0 hu1 hab
    exact ih hb0 hb1



theorem bc59_T_invariant {u y : Site 2} (hu1 : 1 ≤ u 1)
    (hconn : Connected 2 (removeSite 0 bc59_omega') u y) : 1 ≤ y 1 := by
  obtain ⟨w⟩ := hconn
  induction w with
  | nil => exact hu1
  | @cons a b c hab w' ih => exact ih (bc59_T_step hu1 hab)








theorem bc59_line0_edge_open {k : ℤ} (h0 : (0 : Site 2) ∉ s(bc57_pt k 0, bc57_pt (k + 1) 0)) :
    (removeSite 0 bc59_omega') s(bc57_pt k 0, bc57_pt (k + 1) 0) = true := by
  rw [removeSite_apply_of_notMem h0, bc59_omega']
  have : bc57_evenLines s(bc57_pt k (2 * 0), bc57_pt (k + 1) (2 * 0)) = true :=
    bc57_evenLines_open k 0
  simp only [mul_zero] at this
  rw [forceOpenFinset]
  by_cases hG : s(bc57_pt k 0, bc57_pt (k + 1) 0) ∈ bc59_G
  · rw [if_pos hG]
  · rw [if_neg hG]; exact this



theorem bc59_line2_edge_open (k : ℤ) :
    (removeSite 0 bc59_omega') s(bc57_pt k 2, bc57_pt (k + 1) 2) = true := by
  have h0 : (0 : Site 2) ∉ s(bc57_pt k 2, bc57_pt (k + 1) 2) := by
    rw [Sym2.mem_iff]
    rintro (h | h) <;> exact absurd (bc59_pt_eq_origin_iff.mp h.symm).2 (by decide)
  rw [removeSite_apply_of_notMem h0, bc59_omega']
  have : bc57_evenLines s(bc57_pt k (2 * 1), bc57_pt (k + 1) (2 * 1)) = true :=
    bc57_evenLines_open k 1
  simp only [mul_one] at this
  rw [forceOpenFinset]
  by_cases hG : s(bc57_pt k 2, bc57_pt (k + 1) 2) ∈ bc59_G
  · rw [if_pos hG]
  · rw [if_neg hG]; exact this



theorem bc59_R_reach (j : ℕ) :
    Connected 2 (removeSite 0 bc59_omega') (bc57_pt 1 0) (bc57_pt ((j : ℤ) + 1) 0) := by
  induction j with
  | zero => simpa using connected_refl _ (bc57_pt 1 0)
  | succ i ih =>
    have step : Connected 2 (removeSite 0 bc59_omega') (bc57_pt ((i : ℤ) + 1) 0)
        (bc57_pt ((i : ℤ) + 1 + 1) 0) := by
      have h0 : (0 : Site 2) ∉ s(bc57_pt ((i : ℤ) + 1) 0, bc57_pt ((i : ℤ) + 1 + 1) 0) := by
        rw [Sym2.mem_iff]
        rintro (h | h) <;> exact absurd (bc59_pt_eq_origin_iff.mp h.symm).1 (by omega)
      exact IsOpenEdge.connected ⟨bc57_pt_adj ((i : ℤ) + 1) 0, bc59_line0_edge_open h0⟩
    have hcast : ((i + 1 : ℕ) : ℤ) + 1 = (i : ℤ) + 1 + 1 := by push_cast; ring
    rw [hcast]; exact ih.trans step


theorem bc59_L_reach (j : ℕ) :
    Connected 2 (removeSite 0 bc59_omega') (bc57_pt (-1) 0) (bc57_pt (-((j : ℤ) + 1)) 0) := by
  induction j with
  | zero => simpa using connected_refl _ (bc57_pt (-1) 0)
  | succ i ih =>
    
    have hadj : (hypercubicLattice 2).Adj (bc57_pt (-((i : ℤ) + 1) - 1) 0)
        (bc57_pt (-((i : ℤ) + 1) - 1 + 1) 0) := bc57_pt_adj _ 0
    have heq : (-((i : ℤ) + 1) - 1 + 1) = -((i : ℤ) + 1) := by ring
    have h0 : (0 : Site 2) ∉ s(bc57_pt (-((i : ℤ) + 1) - 1) 0, bc57_pt (-((i : ℤ) + 1) - 1 + 1) 0) := by
      rw [Sym2.mem_iff]
      rintro (h | h) <;> exact absurd (bc59_pt_eq_origin_iff.mp h.symm).1 (by omega)
    have step0 := IsOpenEdge.connected ⟨hadj, bc59_line0_edge_open h0⟩
    rw [heq] at step0
    have step : Connected 2 (removeSite 0 bc59_omega') (bc57_pt (-((i : ℤ) + 1)) 0)
        (bc57_pt (-((i : ℤ) + 1) - 1) 0) := step0.symm
    have hcast : -(((i + 1 : ℕ) : ℤ) + 1) = -((i : ℤ) + 1) - 1 := by push_cast; ring
    rw [hcast]; exact ih.trans step



theorem bc59_T_reach_line2 (j : ℕ) :
    Connected 2 (removeSite 0 bc59_omega') (bc57_pt 0 2) (bc57_pt (j : ℤ) 2) := by
  induction j with
  | zero => simpa using connected_refl _ (bc57_pt 0 2)
  | succ i ih =>
    have step : Connected 2 (removeSite 0 bc59_omega') (bc57_pt (i : ℤ) 2)
        (bc57_pt ((i : ℤ) + 1) 2) :=
      IsOpenEdge.connected ⟨bc57_pt_adj (i : ℤ) 2, bc59_line2_edge_open (i : ℤ)⟩
    have hcast : ((i + 1 : ℕ) : ℤ) = (i : ℤ) + 1 := by push_cast; ring
    rw [hcast]; exact ih.trans step


theorem bc59_T_reach_corridor :
    Connected 2 (removeSite 0 bc59_omega') (bc57_pt 0 1) (bc57_pt 0 2) := by
  have hadj : (hypercubicLattice 2).Adj (bc57_pt 0 1) (bc57_pt 0 2) := by
    rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp [bc57_pt]
  exact IsOpenEdge.connected ⟨hadj, bc59_corridor_open⟩


theorem bc59_pt_outside_box_fst {n : ℕ} {a b : ℤ} (ha : n < a.natAbs) :
    bc57_pt a b ∉ box 2 n := by
  rw [mem_box]; simp only [not_forall, not_le]; exact ⟨0, by rw [bc57_pt_fst]; exact ha⟩


theorem bc59_R_infinite : (cluster 2 (removeSite 0 bc59_omega') (bc57_pt 1 0)).Infinite := by
  rw [cluster_infinite_iff]
  intro n
  refine ⟨bc57_pt ((n : ℤ) + 1) 0, bc59_pt_outside_box_fst (by omega), bc59_R_reach n⟩


theorem bc59_L_infinite : (cluster 2 (removeSite 0 bc59_omega') (bc57_pt (-1) 0)).Infinite := by
  rw [cluster_infinite_iff]
  intro n
  refine ⟨bc57_pt (-((n : ℤ) + 1)) 0, bc59_pt_outside_box_fst (by omega), bc59_L_reach n⟩



theorem bc59_T_infinite : (cluster 2 (removeSite 0 bc59_omega') (bc57_pt 0 1)).Infinite := by
  rw [cluster_infinite_iff]
  intro n
  refine ⟨bc57_pt ((n : ℤ) + 1) 2, bc59_pt_outside_box_fst (by omega), ?_⟩
  have h2 : Connected 2 (removeSite 0 bc59_omega') (bc57_pt 0 2) (bc57_pt ((n : ℤ) + 1) 2) := by
    have := bc59_T_reach_line2 (n + 1)
    have hcast : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
    rwa [hcast] at this
  exact bc59_T_reach_corridor.trans h2









theorem bc59_sep_RL : ¬ Connected 2 (removeSite 0 bc59_omega') (bc57_pt 1 0) (bc57_pt (-1) 0) := by
  intro hconn
  obtain ⟨_, hc⟩ := bc59_R_invariant (by simp) (by simp) hconn
  rw [bc57_pt_fst] at hc; omega



theorem bc59_sep_RT : ¬ Connected 2 (removeSite 0 bc59_omega') (bc57_pt 1 0) (bc57_pt 0 1) := by
  intro hconn
  obtain ⟨hh, _⟩ := bc59_R_invariant (by simp) (by simp) hconn
  rw [bc57_pt_snd] at hh; omega


theorem bc59_sep_LT : ¬ Connected 2 (removeSite 0 bc59_omega') (bc57_pt (-1) 0) (bc57_pt 0 1) := by
  intro hconn
  obtain ⟨hh, _⟩ := bc59_L_invariant (by simp) (by simp) hconn
  rw [bc57_pt_snd] at hh; omega




theorem bc59_arms_distinct : bc59_a1 ≠ bc59_a2 ∧ bc59_a1 ≠ bc59_a3 ∧ bc59_a2 ≠ bc59_a3 := by
  unfold bc59_a1 bc59_a2 bc59_a3
  refine ⟨?_, ?_, ?_⟩ <;> intro h
  · have := congrArg (fun f => f 0) h; simp [bc57_pt] at this
  · have := congrArg (fun f => f 1) h; simp [bc57_pt] at this
  · have := congrArg (fun f => f 0) h; simp [bc57_pt] at this


theorem bc59_arms_adj :
    (hypercubicLattice 2).Adj 0 bc59_a1 ∧ (hypercubicLattice 2).Adj 0 bc59_a2 ∧
      (hypercubicLattice 2).Adj 0 bc59_a3 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    (rw [bc59_origin_eq, hypercubicLattice_adj, Fin.sum_univ_two])
  · unfold bc59_a1; simp [bc57_pt]
  · unfold bc59_a2; simp [bc57_pt]
  · unfold bc59_a3; simp [bc57_pt]












theorem bc59_evenLines_hasDisjointCorridors : bc59_DisjointCorridors bc57_evenLines := by
  refine ⟨bc59_G, bc59_a1, bc59_a2, bc59_a3, bc59_arms_distinct, ⟨?_, ?_, ?_⟩, bc59_arms_adj,
    ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  
  · simp [bc59_G]
  · simp [bc59_G]
  · simp [bc59_G]
  
  · change (cluster 2 (removeSite 0 bc59_omega') bc59_a1).Infinite; exact bc59_R_infinite
  · change (cluster 2 (removeSite 0 bc59_omega') bc59_a2).Infinite; exact bc59_L_infinite
  · change (cluster 2 (removeSite 0 bc59_omega') bc59_a3).Infinite; exact bc59_T_infinite
  
  · change ¬ Connected 2 (removeSite 0 bc59_omega') bc59_a1 bc59_a2; exact bc59_sep_RL
  · change ¬ Connected 2 (removeSite 0 bc59_omega') bc59_a1 bc59_a3; exact bc59_sep_RT
  · change ¬ Connected 2 (removeSite 0 bc59_omega') bc59_a2 bc59_a3; exact bc59_sep_LT




theorem bc59_evenLines_originTrif :
    ∃ G : Finset (Sym2 (Site 2)), bc47_IsClassicalTrifurcation (forceOpenFinset G bc57_evenLines) 0 :=
  bc59_corridors_give_trifurcation bc57_evenLines bc59_evenLines_hasDisjointCorridors






















theorem bc59_status (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p) :
    
    ((∀ n : ℕ, bc59_HasDisjointCorridors d n) →
      (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω = 0} = 1 ∨
        bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω = 1} = 1)
        ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0
        ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
            {ω | numInfiniteClusters d ω ≤ 1} = 1) ∧
    
    (∀ ω : ConfigSpace (Sym2 (Site d)), bc59_DisjointCorridors ω →
      ∃ G : Finset (Sym2 (Site d)), bc47_IsClassicalTrifurcation (forceOpenFinset G ω) 0) ∧
    
    bc59_DisjointCorridors bc57_evenLines ∧
    (∃ G : Finset (Sym2 (Site 2)),
      bc47_IsClassicalTrifurcation (forceOpenFinset G bc57_evenLines) 0) :=
  ⟨fun h => bc59_burton_keane_bernoulli_of_hasCorridors hd p hp1 hp0 h,
   fun ω hω => bc59_corridors_give_trifurcation ω hω,
   bc59_evenLines_hasDisjointCorridors,
   bc59_evenLines_originTrif⟩

end StatMech.Walls
