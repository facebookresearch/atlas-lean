/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





































































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.BoxSurfaceVolume
import Code.Lattice.Clusters
import Code.Percolation.BurtonKeane
import Code.Percolation.BurtonKeaneUniqueness
import Code.Percolation.TrifurcationCount
import Code.Percolation.BurtonKeaneClose2
import Code.Percolation.ArmReachComponentClose
import Code.Percolation.SpanForestArmsClose
import Code.Percolation.DisjointArmEndsClose

open Set SimpleGraph Finset
open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}








def IsCanonicalTrifurcation (d : ℕ) (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) : Prop :=
  ∃ a₁ a₂ a₃ : Site d,
    (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧
    ((openSubgraph d ω).Adj x a₁ ∧ (openSubgraph d ω).Adj x a₂ ∧ (openSubgraph d ω).Adj x a₃) ∧
    ((cluster d (removeSite x ω) a₁).Infinite ∧ (cluster d (removeSite x ω) a₂).Infinite ∧
      (cluster d (removeSite x ω) a₃).Infinite) ∧
    (¬ Connected d (removeSite x ω) a₁ a₂ ∧
      ¬ Connected d (removeSite x ω) a₁ a₃ ∧
      ¬ Connected d (removeSite x ω) a₂ a₃)











theorem ctc2_cluster_removeSite_subset (x a : Site d) (ω : ConfigSpace (Sym2 (Site d))) :
    cluster d (removeSite x ω) a ⊆ cluster d ω a := by
  intro y hy
  rw [mem_cluster] at hy ⊢
  obtain ⟨w⟩ := hy
  
  have hle : openSubgraph d (removeSite x ω) ≤ openSubgraph d ω := by
    intro p q hpq
    obtain ⟨hadj, hopen⟩ := hpq
    refine ⟨hadj, ?_⟩
    by_cases hx : x ∈ s(p, q)
    · rw [removeSite_apply_of_mem hx] at hopen; exact absurd hopen (by simp)
    · rwa [removeSite_apply_of_notMem hx] at hopen
  set f : openSubgraph d (removeSite x ω) →g openSubgraph d ω :=
    { toFun := id, map_rel' := fun {p q} hpq => hle hpq } with hf
  exact ⟨w.map f⟩




theorem ctc2_isTrifurcation_of_canonical {ω : ConfigSpace (Sym2 (Site d))} {x : Site d}
    (h : IsCanonicalTrifurcation d ω x) : IsTrifurcation d ω x := by
  obtain ⟨a₁, a₂, a₃, hne, hadj, hinf, hsep⟩ := h
  refine ⟨a₁, a₂, a₃, hne, ⟨hadj.1.reachable, hadj.2.1.reachable, hadj.2.2.reachable⟩, ?_, hsep⟩
  refine ⟨?_, ?_, ?_⟩
  · exact hinf.1.mono (ctc2_cluster_removeSite_subset x a₁ ω)
  · exact hinf.2.1.mono (ctc2_cluster_removeSite_subset x a₂ ω)
  · exact hinf.2.2.mono (ctc2_cluster_removeSite_subset x a₃ ω)










theorem ctc2_arm_in_box_succ {ω : ConfigSpace (Sym2 (Site d))} {x a : Site d} {n : ℕ}
    (hx : x ∈ box d n) (hadj : (openSubgraph d ω).Adj x a) : a ∈ box d (n + 1) :=
  arc_neighbour_in_box_succ hx hadj.1








theorem ctc2_canonical_three_disjoint_boundary (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x : Site d} (hxbox : x ∈ box d n) (htri : IsCanonicalTrifurcation d ω x) :
    ∃ a₁ a₂ a₃ z₁ z₂ z₃ : Site d,
      ((openSubgraph d ω).Adj x a₁ ∧ (openSubgraph d ω).Adj x a₂ ∧ (openSubgraph d ω).Adj x a₃) ∧
      (z₁ ∈ vertexBoundary d (n + 1) ∧ z₂ ∈ vertexBoundary d (n + 1) ∧
        z₃ ∈ vertexBoundary d (n + 1)) ∧
      (Connected d (removeSite x ω) a₁ z₁ ∧ Connected d (removeSite x ω) a₂ z₂ ∧
        Connected d (removeSite x ω) a₃ z₃) ∧
      (¬ Connected d (removeSite x ω) z₁ z₂ ∧ ¬ Connected d (removeSite x ω) z₁ z₃ ∧
        ¬ Connected d (removeSite x ω) z₂ z₃) ∧
      (z₁ ≠ z₂ ∧ z₁ ≠ z₃ ∧ z₂ ≠ z₃) := by
  obtain ⟨a₁, a₂, a₃, _, hadj, hinf, hsep⟩ := htri
  obtain ⟨z₁, z₂, z₃, hzb, hzc, hzd, hzne⟩ :=
    bk2_trif_three_disjoint_boundary ω (n + 1) (by omega)
      (ctc2_arm_in_box_succ hxbox hadj.1) (ctc2_arm_in_box_succ hxbox hadj.2.1)
      (ctc2_arm_in_box_succ hxbox hadj.2.2)
      hinf.1 hinf.2.1 hinf.2.2 hsep.1 hsep.2.1 hsep.2.2
  exact ⟨a₁, a₂, a₃, z₁, z₂, z₃, hadj, hzb, hzc, hzd, hzne⟩
















theorem ctc2_armsRemoveSiteInfinite_of_canonical (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hcanon : ∀ x, x ∈ box d n → IsTrifurcation d ω x → IsCanonicalTrifurcation d ω x) :
    arc_TrifArmsRemoveSiteInfinite ω n := by
  intro x hxbox htri
  obtain ⟨a₁, a₂, a₃, hne, hadj, hinf, hsep⟩ := hcanon x hxbox htri
  
  refine ⟨![a₁, a₂, a₃], ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact hadj.1
    · exact hadj.2.1
    · exact hadj.2.2
  · intro i
    fin_cases i
    · exact ((openSubgraph d ω).ne_of_adj hadj.1).symm
    · exact ((openSubgraph d ω).ne_of_adj hadj.2.1).symm
    · exact ((openSubgraph d ω).ne_of_adj hadj.2.2).symm
  · exact ⟨hsep.1, hsep.2.1, hsep.2.2⟩
  · intro i
    fin_cases i
    · exact hinf.1
    · exact hinf.2.1
    · exact hinf.2.2























theorem ctc2_count_of_armForestReaching (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : sfa_ArmForestReaching ω n) : Tcount d ω n ≤ boxSV_boundaryCard d n :=
  sfa_Tcount_le_boundary_of_armForestReaching ω n h










theorem ctc2_count_single_boundary (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x : Site d} (hxbox : x ∈ box d n) (htri : IsTrifurcation d ω x)
    (hsingle : ∀ y, y ∈ box d n → IsTrifurcation d ω y → y = x)
    (c : Fin 3 → Site d)
    (hadj : ∀ i, (openSubgraph d ω).Adj x (c i))
    (hne : ∀ i, c i ≠ x)
    (hcut : ¬ Connected d (removeSite x ω) (c 0) (c 1) ∧
            ¬ Connected d (removeSite x ω) (c 0) (c 2) ∧
            ¬ Connected d (removeSite x ω) (c 1) (c 2))
    (hbdry : ∀ i, c i ∈ vertexBoundary d n)
    (hinj : Function.Injective c) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  arc_Tcount_le_boundary_of_residue_single_boundary ω n hxbox htri hsingle c hadj hne hcut
    hbdry hinj










theorem ctc2_count_of_disjointArmEnds (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (hn : 1 ≤ n)
    (hdisj : bk2_DisjointArmEnds ω n) : Tcount d ω n ≤ boxSV_boundaryCard d n :=
  bk2_Tcount_le_boundary_of_disjointArmEnds ω n hn hdisj






theorem ctc2_count_of_subsingleton (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (hn : 1 ≤ n)
    (hsub : ∀ x y, x ∈ box d n → IsTrifurcation d ω x → y ∈ box d n →
      IsTrifurcation d ω y → x = y) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  ctc2_count_of_disjointArmEnds ω n hn (bk2_disjointArmEnds_of_subsingleton ω n hsub)
















theorem ctc2_count_of_forestLeafInjection (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : daec_ForestLeafInjection ω n) : Tcount d ω n ≤ boxSV_boundaryCard d n :=
  daec_Tcount_le_boundary_of_forestLeafInjection ω n h








open Classical in


noncomputable def ctc2_canonTcount (d : ℕ) (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : ℕ :=
  ((boxFinsetBK d n).filter (fun x => IsCanonicalTrifurcation d ω x)).card




theorem ctc2_canonTcount_le_Tcount (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    ctc2_canonTcount d ω n ≤ Tcount d ω n := by
  classical
  unfold ctc2_canonTcount Tcount
  apply Finset.card_le_card
  intro x hx
  rw [Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, ctc2_isTrifurcation_of_canonical hx.2⟩





theorem ctc2_canonTcount_le_boundary_of_forestLeafInjection (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (h : daec_ForestLeafInjection ω n) :
    ctc2_canonTcount d ω n ≤ boxSV_boundaryCard d n :=
  le_trans (ctc2_canonTcount_le_Tcount ω n) (ctc2_count_of_forestLeafInjection ω n h)






theorem ctc2_canonTcount_le_boundary_of_subsingleton (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (hn : 1 ≤ n)
    (hsub : ∀ x y, x ∈ box d n → IsTrifurcation d ω x → y ∈ box d n →
      IsTrifurcation d ω y → x = y) :
    ctc2_canonTcount d ω n ≤ boxSV_boundaryCard d n :=
  le_trans (ctc2_canonTcount_le_Tcount ω n) (ctc2_count_of_subsingleton ω n hn hsub)












namespace CtcWitness


def px (k : ℤ) : Site 2 := ![k, 0]

def py (k : ℤ) : Site 2 := ![0, k]

theorem px_inj : Function.Injective px := by
  intro a b h
  have h0 : (px a) 0 = (px b) 0 := by rw [h]
  simpa [px] using h0

theorem py_inj : Function.Injective py := by
  intro a b h
  have h1 : (py a) 1 = (py b) 1 := by rw [h]
  simpa [py] using h1

theorem px_adj (k : ℤ) : (hypercubicLattice 2).Adj (px k) (px (k + 1)) := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp [px]

theorem py_adj (k : ℤ) : (hypercubicLattice 2).Adj (py k) (py (k + 1)) := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp [py]

open Classical in




noncomputable def threeRayConfig : ConfigSpace (Sym2 (Site 2)) :=
  fun e =>
    if (∃ k : ℤ, e = s(px k, px (k + 1))) then true
    else if (∃ k : ℤ, 0 ≤ k ∧ e = s(py k, py (k + 1))) then true
    else false

theorem px_ray_open (k : ℤ) : threeRayConfig s(px k, px (k + 1)) = true := by
  classical
  rw [threeRayConfig, if_pos]; exact ⟨k, rfl⟩


theorem px_zero_eq_py_zero : px 0 = py 0 := by funext i; fin_cases i <;> simp [px, py]

theorem py_ray_open (k : ℤ) (hk : 0 ≤ k) : threeRayConfig s(py k, py (k + 1)) = true := by
  classical
  rw [threeRayConfig]
  by_cases h : (∃ j : ℤ, s(py k, py (k + 1)) = s(px j, px (j + 1)))
  · 
    
    exfalso
    obtain ⟨j, hj⟩ := h
    rw [Sym2.eq_iff] at hj
    rcases hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have e1 : (0 : ℤ) = j := by have := congrFun h1 0; simpa [py, px] using this
      have e2 : (0 : ℤ) = j + 1 := by have := congrFun h2 0; simpa [py, px] using this
      omega
    · have e1 : (0 : ℤ) = j + 1 := by have := congrFun h1 0; simpa [py, px] using this
      have e2 : (0 : ℤ) = j := by have := congrFun h2 0; simpa [py, px] using this
      omega
  · rw [if_neg h, if_pos]; exact ⟨k, hk, rfl⟩






theorem cut_px_pos_open (k : ℤ) (hk : 1 ≤ k) :
    (removeSite (px 0) threeRayConfig) s(px k, px (k + 1)) = true := by
  have hx : px 0 ∉ s(px k, px (k + 1)) := by
    rw [Sym2.mem_iff]; simp only [not_or]
    constructor
    · intro h; have : (0 : ℤ) = k := px_inj h; omega
    · intro h; have : (0 : ℤ) = k + 1 := px_inj h; omega
  rw [removeSite_apply_of_notMem hx]; exact px_ray_open k


theorem cut_px_neg_open (k : ℤ) (hk : k ≤ -2) :
    (removeSite (px 0) threeRayConfig) s(px k, px (k + 1)) = true := by
  have hx : px 0 ∉ s(px k, px (k + 1)) := by
    rw [Sym2.mem_iff]; simp only [not_or]
    constructor
    · intro h; have : (0 : ℤ) = k := px_inj h; omega
    · intro h; have : (0 : ℤ) = k + 1 := px_inj h; omega
  rw [removeSite_apply_of_notMem hx]; exact px_ray_open k


theorem cut_py_pos_open (k : ℤ) (hk : 1 ≤ k) :
    (removeSite (px 0) threeRayConfig) s(py k, py (k + 1)) = true := by
  have hx : px 0 ∉ s(py k, py (k + 1)) := by
    rw [px_zero_eq_py_zero, Sym2.mem_iff]; simp only [not_or]
    constructor
    · intro h; have : (0 : ℤ) = k := py_inj h; omega
    · intro h; have : (0 : ℤ) = k + 1 := py_inj h; omega
  rw [removeSite_apply_of_notMem hx]; exact py_ray_open k (by omega)


theorem cut_connected_px_pos (m : ℤ) (hm : 1 ≤ m) :
    Connected 2 (removeSite (px 0) threeRayConfig) (px 1) (px m) := by
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, m = 1 + j := ⟨(m - 1).toNat, by omega⟩
  clear hm
  induction j with
  | zero => simpa using connected_refl _ (px 1)
  | succ i ih =>
    have hi : (1 : ℤ) ≤ 1 + i := by omega
    have step : Connected 2 (removeSite (px 0) threeRayConfig) (px (1 + i)) (px (1 + (i : ℤ) + 1)) :=
      IsOpenEdge.connected ⟨px_adj (1 + i), cut_px_pos_open (1 + i) hi⟩
    have hcast : (1 : ℤ) + (i + 1 : ℕ) = (1 + (i : ℤ)) + 1 := by push_cast; ring
    rw [hcast]; exact ih.trans step


theorem cut_connected_px_neg (m : ℤ) (hm : 1 ≤ m) :
    Connected 2 (removeSite (px 0) threeRayConfig) (px (-1)) (px (-m)) := by
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, m = 1 + j := ⟨(m - 1).toNat, by omega⟩
  clear hm
  induction j with
  | zero => simpa using connected_refl _ (px (-1))
  | succ i ih =>
    have hi : (-(1 + (i : ℤ)) - 1) ≤ -2 := by omega
    
    have step : Connected 2 (removeSite (px 0) threeRayConfig)
        (px (-(1 + (i : ℤ)) - 1)) (px (-(1 + (i : ℤ)))) := by
      have hadj := px_adj (-(1 + (i : ℤ)) - 1)
      rw [show (-(1 + (i : ℤ)) - 1) + 1 = -(1 + (i : ℤ)) by ring] at hadj
      exact IsOpenEdge.connected ⟨hadj, by
        have := cut_px_neg_open (-(1 + (i : ℤ)) - 1) hi
        rwa [show (-(1 + (i : ℤ)) - 1) + 1 = -(1 + (i : ℤ)) by ring] at this⟩
    rw [show -((1 : ℤ) + (i + 1 : ℕ)) = -(1 + (i : ℤ)) - 1 by push_cast; ring]
    refine ih.trans ?_
    rw [show -((1 : ℤ) + (i : ℕ)) = -(1 + (i : ℤ)) by ring]
    exact step.symm


theorem cut_connected_py_pos (m : ℤ) (hm : 1 ≤ m) :
    Connected 2 (removeSite (px 0) threeRayConfig) (py 1) (py m) := by
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, m = 1 + j := ⟨(m - 1).toNat, by omega⟩
  clear hm
  induction j with
  | zero => simpa using connected_refl _ (py 1)
  | succ i ih =>
    have hi : (1 : ℤ) ≤ 1 + i := by omega
    have step : Connected 2 (removeSite (px 0) threeRayConfig) (py (1 + i)) (py (1 + (i : ℤ) + 1)) :=
      IsOpenEdge.connected ⟨py_adj (1 + i), cut_py_pos_open (1 + i) hi⟩
    have hcast : (1 : ℤ) + (i + 1 : ℕ) = (1 + (i : ℤ)) + 1 := by push_cast; ring
    rw [hcast]; exact ih.trans step

theorem px_pos_outside_box (n : ℕ) : px (n + 1) ∉ box 2 n := by
  rw [mem_box]; simp only [not_forall, not_le]; refine ⟨0, ?_⟩
  simp only [px, Matrix.cons_val_zero]
  have : ((n : ℤ) + 1).natAbs = (n + 1 : ℕ) := by omega
  omega

theorem px_neg_outside_box (n : ℕ) : px (-(n + 1 : ℤ)) ∉ box 2 n := by
  rw [mem_box]; simp only [not_forall, not_le]; refine ⟨0, ?_⟩
  simp only [px, Matrix.cons_val_zero]
  have : (-(n + 1 : ℤ)).natAbs = (n + 1 : ℕ) := by omega
  omega

theorem py_pos_outside_box (n : ℕ) : py (n + 1) ∉ box 2 n := by
  rw [mem_box]; simp only [not_forall, not_le]; refine ⟨1, ?_⟩
  have hval : (py ((n : ℤ) + 1)) 1 = (n : ℤ) + 1 := by simp [py]
  rw [hval]
  have : ((n : ℤ) + 1).natAbs = (n + 1 : ℕ) := by omega
  omega


theorem cut_px_pos_infinite : (cluster 2 (removeSite (px 0) threeRayConfig) (px 1)).Infinite := by
  rw [cluster_infinite_iff]; intro n
  exact ⟨px (n + 1), px_pos_outside_box n, cut_connected_px_pos (n + 1) (by omega)⟩

theorem cut_px_neg_infinite :
    (cluster 2 (removeSite (px 0) threeRayConfig) (px (-1))).Infinite := by
  rw [cluster_infinite_iff]; intro n
  refine ⟨px (-((n : ℤ) + 1)), px_neg_outside_box n, ?_⟩
  exact cut_connected_px_neg ((n : ℤ) + 1) (by omega)

theorem cut_py_pos_infinite : (cluster 2 (removeSite (px 0) threeRayConfig) (py 1)).Infinite := by
  rw [cluster_infinite_iff]; intro n
  exact ⟨py (n + 1), py_pos_outside_box n, cut_connected_py_pos (n + 1) (by omega)⟩










theorem cut_edge_classify {a b : Site 2}
    (hopen : (removeSite (px 0) threeRayConfig) s(a, b) = true) :
    (∃ k : ℤ, 1 ≤ k ∧ s(a, b) = s(px k, px (k + 1))) ∨
    (∃ k : ℤ, k ≤ -2 ∧ s(a, b) = s(px k, px (k + 1))) ∨
    (∃ k : ℤ, 1 ≤ k ∧ s(a, b) = s(py k, py (k + 1))) := by
  classical
  
  have hx0 : px 0 ∉ s(a, b) := by
    intro hmem; rw [removeSite_apply_of_mem hmem] at hopen; exact absurd hopen (by simp)
  rw [removeSite_apply_of_notMem hx0, threeRayConfig] at hopen
  split at hopen
  · 
    rename_i hex; obtain ⟨k, hk⟩ := hex
    
    have hkne0 : k ≠ 0 := by
      rintro rfl; apply hx0; rw [hk, Sym2.mem_iff]; left; rfl
    have hkne_neg1 : k ≠ -1 := by
      rintro rfl; apply hx0; rw [hk, Sym2.mem_iff]; right
      rw [show (-1 : ℤ) + 1 = 0 by ring]
    rcases lt_or_ge k 0 with hneg | hpos
    · exact Or.inr (Or.inl ⟨k, by omega, hk⟩)
    · exact Or.inl ⟨k, by omega, hk⟩
  · 
    split at hopen
    · rename_i hey; obtain ⟨k, hk0, hk⟩ := hey
      have hkne0 : k ≠ 0 := by
        rintro rfl; apply hx0
        rw [px_zero_eq_py_zero, hk, Sym2.mem_iff]; left; rfl
      exact Or.inr (Or.inr ⟨k, by omega, hk⟩)
    · exact absurd hopen (by simp)



theorem px_edge_coords {u v : Site 2} {k : ℤ}
    (he : (u = px k ∧ v = px (k + 1)) ∨ (u = px (k + 1) ∧ v = px k)) :
    (u 0 = k ∧ v 0 = k + 1 ∨ u 0 = k + 1 ∧ v 0 = k) ∧ u 1 = 0 ∧ v 1 = 0 := by
  rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    refine ⟨?_, by simp [px], by simp [px]⟩
  · left; constructor <;> simp [px]
  · right; constructor <;> simp [px]


theorem py_edge_coords {u v : Site 2} {k : ℤ}
    (he : (u = py k ∧ v = py (k + 1)) ∨ (u = py (k + 1) ∧ v = py k)) :
    u 0 = 0 ∧ v 0 = 0 ∧ (u 1 = k ∧ v 1 = k + 1 ∨ u 1 = k + 1 ∧ v 1 = k) := by
  rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    refine ⟨by simp [py], by simp [py], ?_⟩
  · left; constructor <;> simp [py]
  · right; constructor <;> simp [py]



theorem cut_px_pos_step {u v : Site 2} (hu : 1 ≤ u 0 ∧ u 1 = 0)
    (hadj : (openSubgraph 2 (removeSite (px 0) threeRayConfig)).Adj u v) :
    1 ≤ v 0 ∧ v 1 = 0 := by
  obtain ⟨_, hopen⟩ := hadj
  rcases cut_edge_classify hopen with ⟨k, hk, he⟩ | ⟨k, hk, he⟩ | ⟨k, hk, he⟩ <;>
    rw [Sym2.eq_iff] at he
  · obtain ⟨h0, _, hv1⟩ := px_edge_coords he; omega
  · obtain ⟨h0, _, _⟩ := px_edge_coords he; omega
  · obtain ⟨hu0, _, _⟩ := py_edge_coords he; omega



theorem cut_px_pos_invariant {u y : Site 2} (hu : 1 ≤ u 0 ∧ u 1 = 0)
    (h : Connected 2 (removeSite (px 0) threeRayConfig) u y) :
    1 ≤ y 0 ∧ y 1 = 0 := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact hu
  | @cons a b c hab w' ih => exact ih (cut_px_pos_step hu hab)


theorem cut_px_neg_step {u v : Site 2} (hu : u 0 ≤ -1 ∧ u 1 = 0)
    (hadj : (openSubgraph 2 (removeSite (px 0) threeRayConfig)).Adj u v) :
    v 0 ≤ -1 ∧ v 1 = 0 := by
  obtain ⟨_, hopen⟩ := hadj
  rcases cut_edge_classify hopen with ⟨k, hk, he⟩ | ⟨k, hk, he⟩ | ⟨k, hk, he⟩ <;>
    rw [Sym2.eq_iff] at he
  · obtain ⟨h0, _, _⟩ := px_edge_coords he; omega
  · obtain ⟨h0, _, hv1⟩ := px_edge_coords he; omega
  · obtain ⟨hu0, _, _⟩ := py_edge_coords he; omega

theorem cut_px_neg_invariant {u y : Site 2} (hu : u 0 ≤ -1 ∧ u 1 = 0)
    (h : Connected 2 (removeSite (px 0) threeRayConfig) u y) :
    y 0 ≤ -1 ∧ y 1 = 0 := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact hu
  | @cons a b c hab w' ih => exact ih (cut_px_neg_step hu hab)


theorem cut_py_pos_step {u v : Site 2} (hu : u 0 = 0 ∧ 1 ≤ u 1)
    (hadj : (openSubgraph 2 (removeSite (px 0) threeRayConfig)).Adj u v) :
    v 0 = 0 ∧ 1 ≤ v 1 := by
  obtain ⟨_, hopen⟩ := hadj
  rcases cut_edge_classify hopen with ⟨k, hk, he⟩ | ⟨k, hk, he⟩ | ⟨k, hk, he⟩ <;>
    rw [Sym2.eq_iff] at he
  · obtain ⟨h0, _, _⟩ := px_edge_coords he; omega
  · obtain ⟨h0, _, _⟩ := px_edge_coords he; omega
  · obtain ⟨hu0, hv0, h1⟩ := py_edge_coords he; omega

theorem cut_py_pos_invariant {u y : Site 2} (hu : u 0 = 0 ∧ 1 ≤ u 1)
    (h : Connected 2 (removeSite (px 0) threeRayConfig) u y) :
    y 0 = 0 ∧ 1 ≤ y 1 := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact hu
  | @cons a b c hab w' ih => exact ih (cut_py_pos_step hu hab)



theorem cut_disconnect_pos_neg :
    ¬ Connected 2 (removeSite (px 0) threeRayConfig) (px 1) (px (-1)) := by
  intro h
  have := cut_px_pos_invariant (by simp [px]) h
  simp only [px, Matrix.cons_val_zero] at this; omega

theorem cut_disconnect_pos_py :
    ¬ Connected 2 (removeSite (px 0) threeRayConfig) (px 1) (py 1) := by
  intro h
  have := cut_px_pos_invariant (by simp [px]) h
  simp only [py, Matrix.cons_val_zero] at this; omega

theorem cut_disconnect_neg_py :
    ¬ Connected 2 (removeSite (px 0) threeRayConfig) (px (-1)) (py 1) := by
  intro h
  have := cut_px_neg_invariant (by simp [px]) h
  simp only [py, Matrix.cons_val_zero] at this; omega

end CtcWitness

open CtcWitness in





theorem ctc2_isCanonicalTrifurcation_threeRay :
    ∃ (ω : ConfigSpace (Sym2 (Site 2))) (x : Site 2), IsCanonicalTrifurcation 2 ω x := by
  classical
  refine ⟨threeRayConfig, px 0, px 1, py 1, px (-1), ?_, ?_, ?_, ?_⟩
  · 
    refine ⟨?_, ?_, ?_⟩
    · intro h
      have hc : (px 1) 1 = (py 1) 1 := by rw [h]
      simp [px, py] at hc
    · intro h; have h0 : (1 : ℤ) = -1 := px_inj h; omega
    · intro h
      have hc : (py 1) 0 = (px (-1)) 0 := by rw [h]
      simp [px, py] at hc
  · 
    refine ⟨?_, ?_, ?_⟩
    · refine ⟨px_adj 0, ?_⟩
      have := px_ray_open 0; simpa [px] using this
    · refine ⟨py_adj 0, ?_⟩
      have := py_ray_open 0 (le_refl 0); simpa [py] using this
    · refine ⟨?_, ?_⟩
      · rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp [px]
      · have := px_ray_open (-1)
        rw [show ((-1 : ℤ) + 1) = 0 by ring] at this
        rw [Sym2.eq_swap]; simpa [px] using this
  · 
    exact ⟨cut_px_pos_infinite, cut_py_pos_infinite, cut_px_neg_infinite⟩
  · 
    exact ⟨cut_disconnect_pos_py, cut_disconnect_pos_neg, fun h =>
      cut_disconnect_neg_py h.symm⟩

end Percolation

end StatMech
