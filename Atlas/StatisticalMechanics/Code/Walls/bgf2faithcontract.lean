/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




































import Mathlib
import Code.Walls.baoallopen
import Code.Walls.bcvcutvertex
import Code.Percolation.GridBoxConnected

open Set SimpleGraph Finset
open StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation











def bgf2_inBox (L : ℕ) (c x : Site 2) : Prop := ∀ i, (x i - c i).natAbs ≤ L


theorem bgf2_update_inBox {L : ℕ} {c x : Site 2} (hx : bgf2_inBox L c x) (j : Fin 2) {v : ℤ}
    (hv : (v - c j).natAbs ≤ L) : bgf2_inBox L c (Function.update x j v) := by
  intro i
  by_cases hij : i = j
  · subst hij; rw [Function.update_self]; exact hv
  · rw [Function.update_of_ne hij]; exact hx i


theorem bgf2_mix_inBox {L : ℕ} {c x y : Site 2} (hx : bgf2_inBox L c x) (hy : bgf2_inBox L c y)
    (k : ℕ) : bgf2_inBox L c (mixSite x y k) := by
  intro i
  simp only [mixSite]
  by_cases h : (i : ℕ) < k
  · rw [if_pos h]; exact hy i
  · rw [if_neg h]; exact hx i



def bgf2_AllOpenAt (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ) (c : Site 2) : Prop :=
  ∀ x y : Site 2, bgf2_inBox L c x → bgf2_inBox L c y → (hypercubicLattice 2).Adj x y →
    ω s(x, y) = true



theorem bgf2_ascend {L : ℕ} {c : Site 2} {ω : ConfigSpace (Sym2 (Site 2))}
    (hopen : bgf2_AllOpenAt ω L c) {x : Site 2} (hx : bgf2_inBox L c x) (j : Fin 2) :
    ∀ (k : ℕ) (a : ℤ), (a - c j).natAbs ≤ L → (a + (k : ℤ) - c j).natAbs ≤ L →
      Connected 2 ω (Function.update x j a) (Function.update x j (a + (k : ℤ))) := by
  intro k
  induction k with
  | zero => intro a _ _; simpa using connected_rfl
  | succ m ih =>
    intro a ha hak
    have hint : (a + (m : ℤ) - c j).natAbs ≤ L := by push_cast at hak ⊢; omega
    have hstep : Connected 2 ω (Function.update x j (a + (m : ℤ)))
        (Function.update x j (a + (m : ℤ) + 1)) := by
      have hin1 : bgf2_inBox L c (Function.update x j (a + (m : ℤ))) :=
        bgf2_update_inBox hx j hint
      have hin2 : bgf2_inBox L c (Function.update x j (a + (m : ℤ) + 1)) := by
        refine bgf2_update_inBox hx j ?_
        have : a + ((m : ℤ) + 1) - c j = a + (m : ℤ) + 1 - c j := by ring
        push_cast at hak ⊢; omega
      have hadj := adj_update_succ x j (a + (m : ℤ))
      exact SimpleGraph.Adj.reachable (G := openSubgraph 2 ω)
        (by rw [openSubgraph_adj]; exact ⟨hadj, hopen _ _ hin1 hin2 hadj⟩)
    have hrec := (ih a ha hint).trans hstep
    have he : a + (m : ℤ) + 1 = a + ((m + 1 : ℕ) : ℤ) := by push_cast; ring
    rwa [he] at hrec


theorem bgf2_update_conn {L : ℕ} {c : Site 2} {ω : ConfigSpace (Sym2 (Site 2))}
    (hopen : bgf2_AllOpenAt ω L c) {x : Site 2} (hx : bgf2_inBox L c x) (j : Fin 2) {a : ℤ}
    (ha : (a - c j).natAbs ≤ L) : Connected 2 ω x (Function.update x j a) := by
  have hxj : (x j - c j).natAbs ≤ L := hx j
  have hxupd : Function.update x j (x j) = x := Function.update_eq_self j x
  rcases le_total (x j) a with hle | hle
  · obtain ⟨k, hk⟩ := Int.le.dest hle
    have h := bgf2_ascend hopen hx j k (x j) hxj (by rw [hk]; exact ha)
    rwa [hxupd, hk] at h
  · obtain ⟨k, hk⟩ := Int.le.dest hle
    have h := bgf2_ascend hopen hx j k a ha (by rw [hk]; exact hxj)
    rw [hk, hxupd] at h
    exact h.symm


theorem bgf2_mix_conn {L : ℕ} {c : Site 2} {ω : ConfigSpace (Sym2 (Site 2))}
    (hopen : bgf2_AllOpenAt ω L c) {x y : Site 2} (hx : bgf2_inBox L c x) (hy : bgf2_inBox L c y) :
    ∀ k, k ≤ 2 → Connected 2 ω x (mixSite x y k) := by
  intro k
  induction k with
  | zero => intro _; rw [mixSite_zero]
  | succ m ih =>
    intro hsucc
    have hm : m < 2 := by omega
    have h1 := ih (by omega)
    have hstep : Connected 2 ω (mixSite x y m) (mixSite x y (m + 1)) := by
      rw [mixSite_succ hm]
      exact bgf2_update_conn hopen (bgf2_mix_inBox hx hy m) ⟨m, hm⟩ (hy ⟨m, hm⟩)
    exact h1.trans hstep





theorem bgf2_boxCentre_connected {L : ℕ} {c : Site 2} {ω : ConfigSpace (Sym2 (Site 2))}
    (hopen : bgf2_AllOpenAt ω L c) {a b : Site 2} (ha : bgf2_inBox L c a) (hb : bgf2_inBox L c b) :
    Connected 2 ω a b := by
  have h := bgf2_mix_conn hopen ha hb 2 le_rfl
  rwa [mixSite_full] at h

#check @bgf2_boxCentre_connected








def bgf2_centre (L : ℕ) (j : Site 2) : Site 2 := fun i => (2 * (L : ℤ) + 1) * j i



theorem bgf2_idx_iff_inBox {L : ℕ} {j x : Site 2} :
    bgn_idx L x = j ↔ bgf2_inBox L (bgf2_centre L j) x := by
  constructor
  · intro h i
    have hxi : (x i + (L : ℤ)) / (2 * (L : ℤ) + 1) = j i := by rw [← h]; rfl
    have h2 := (bsc_ediv_eq_iff).mp hxi
    simpa [bgf2_centre] using h2
  · intro h; funext i
    show (x i + (L : ℤ)) / (2 * (L : ℤ) + 1) = j i
    refine (bsc_ediv_eq_iff).mpr ?_
    have := h i
    simpa [bgf2_centre] using this


theorem bgf2_idx_centre (L : ℕ) (j : Site 2) : bgn_idx L (bgf2_centre L j) = j :=
  bgf2_idx_iff_inBox.mpr (by intro i; simp [bgf2_centre])


theorem bgf2_centre_inj {L : ℕ} {j k : Site 2} (h : bgf2_centre L j = bgf2_centre L k) : j = k := by
  funext i
  have := congrFun h i
  simp only [bgf2_centre] at this
  have hb : (2 * (L : ℤ) + 1) ≠ 0 := by positivity
  exact mul_left_cancel₀ hb this



def bgf2_IndexAllOpen (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ) (j : Site 2) : Prop :=
  ∀ x y : Site 2, bgn_idx L x = j → bgn_idx L y = j → (hypercubicLattice 2).Adj x y →
    ω s(x, y) = true




theorem bgf2_indexAllOpen_connected {L : ℕ} {ω : ConfigSpace (Sym2 (Site 2))} {j : Site 2}
    (h : bgf2_IndexAllOpen ω L j) {a b : Site 2} (ha : bgn_idx L a = j) (hb : bgn_idx L b = j) :
    Connected 2 ω a b := by
  refine bgf2_boxCentre_connected (L := L) (c := bgf2_centre L j) ?_ ?_ ?_
  · intro x y hx hy hadj
    exact h x y (bgf2_idx_iff_inBox.mpr hx) (bgf2_idx_iff_inBox.mpr hy) hadj
  · exact bgf2_idx_iff_inBox.mp ha
  · exact bgf2_idx_iff_inBox.mp hb

#check @bgf2_indexAllOpen_connected







open Classical in

noncomputable def bgf2_q (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ) (x : Site 2) : Site 2 :=
  if bgf2_IndexAllOpen ω L (bgn_idx L x) then bgf2_centre L (bgn_idx L x) else x




def bgf2_Gf (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ) : SimpleGraph (Site 2) where
  Adj u v := u ≠ v ∧ ∃ a b : Site 2, bgf2_q ω L a = u ∧ bgf2_q ω L b = v ∧ (openSubgraph 2 ω).Adj a b
  symm := by
    rintro u v ⟨huv, a, b, ha, hb, hab⟩
    exact ⟨huv.symm, b, a, hb, ha, hab.symm⟩

@[simp] theorem bgf2_Gf_adj (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ) (u v : Site 2) :
    (bgf2_Gf ω L).Adj u v ↔
      u ≠ v ∧ ∃ a b : Site 2, bgf2_q ω L a = u ∧ bgf2_q ω L b = v ∧ (openSubgraph 2 ω).Adj a b :=
  Iff.rfl

#check @bgf2_Gf










theorem bgf2_q_eq_connected {ω : ConfigSpace (Sym2 (Site 2))} {L : ℕ} {a b : Site 2}
    (h : bgf2_q ω L a = bgf2_q ω L b) : Connected 2 ω a b := by
  unfold bgf2_q at h
  by_cases hPa : bgf2_IndexAllOpen ω L (bgn_idx L a)
  · rw [if_pos hPa] at h
    by_cases hPb : bgf2_IndexAllOpen ω L (bgn_idx L b)
    · rw [if_pos hPb] at h
      have hidx := bgf2_centre_inj h
      exact bgf2_indexAllOpen_connected hPa rfl hidx.symm
    · rw [if_neg hPb] at h
      exfalso; apply hPb
      have hbi : bgn_idx L b = bgn_idx L a := by rw [← h, bgf2_idx_centre]
      rw [hbi]; exact hPa
  · rw [if_neg hPa] at h
    by_cases hPb : bgf2_IndexAllOpen ω L (bgn_idx L b)
    · rw [if_pos hPb] at h
      exfalso; apply hPa
      have hai : bgn_idx L a = bgn_idx L b := by rw [h, bgf2_idx_centre]
      rw [hai]; exact hPb
    · rw [if_neg hPb] at h
      rw [h]



theorem bgf2_reach_of_connected {ω : ConfigSpace (Sym2 (Site 2))} {L : ℕ} {a b : Site 2}
    (h : Connected 2 ω a b) :
    (bgf2_Gf ω L).Reachable (bgf2_q ω L a) (bgf2_q ω L b) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact Reachable.refl _
  | @cons x z b hadj q ih =>
    refine Reachable.trans ?_ ih
    by_cases hqxz : bgf2_q ω L x = bgf2_q ω L z
    · rw [hqxz]
    · exact SimpleGraph.Adj.reachable ⟨hqxz, x, z, rfl, rfl, hadj⟩





theorem bgf2_connected_of_reach_aux {ω : ConfigSpace (Sym2 (Site 2))} {L : ℕ} :
    ∀ {u v : Site 2}, (bgf2_Gf ω L).Reachable u v →
      ∀ a b, bgf2_q ω L a = u → bgf2_q ω L b = v → Connected 2 ω a b := by
  intro u v h
  obtain ⟨p⟩ := h
  induction p with
  | nil =>
    intro a b ha hb
    exact bgf2_q_eq_connected (ha.trans hb.symm)
  | @cons u z v hadj q ih =>
    intro a b ha hb
    obtain ⟨huz, a', b', ha', hb', hab'⟩ := hadj
    have h1 : Connected 2 ω a a' := bgf2_q_eq_connected (ha.trans ha'.symm)
    have h2 : Connected 2 ω a' b' := SimpleGraph.Adj.reachable hab'
    have h3 : Connected 2 ω b' b := ih b' b hb' hb
    exact (h1.trans h2).trans h3





theorem bgf2_faithful (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ) (a b : Site 2) :
    (bgf2_Gf ω L).Reachable (bgf2_q ω L a) (bgf2_q ω L b) ↔ Connected 2 ω a b := by
  constructor
  · intro h; exact bgf2_connected_of_reach_aux h a b rfl rfl
  · exact bgf2_reach_of_connected

#check @bgf2_faithful










theorem bgf2_centre_zero (L : ℕ) : bgf2_centre L 0 = 0 := by
  funext i; simp [bgf2_centre]


theorem bgf2_mem_box0_iff {L : ℕ} {x : Site 2} :
    x ∈ bc61_boxAround 2 L 0 ↔ bgn_idx L x = 0 := by
  rw [bsc_boxCentre_zero 2 L x, bao_bgn_idx_zero]



theorem bgf2_indexAllOpen_zero_of_bff {ω : ConfigSpace (Sym2 (Site 2))} {L : ℕ}
    (h : bff_BoxAllOpen ω L) : bgf2_IndexAllOpen ω L 0 := by
  intro x y hx hy hadj
  have hxbox : x ∈ box 2 L := by
    have hmem : x ∈ bc61_boxAround 2 L 0 := bgf2_mem_box0_iff.mpr hx
    rwa [bc61_mem_boxAround_zero] at hmem
  have hybox : y ∈ box 2 L := by
    have hmem : y ∈ bc61_boxAround 2 L 0 := bgf2_mem_box0_iff.mpr hy
    rwa [bc61_mem_boxAround_zero] at hmem
  exact h _ (mk_mem_boxEdges hxbox hybox hadj)



theorem bgf2_q_eq_zero_iff {ω : ConfigSpace (Sym2 (Site 2))} {L : ℕ}
    (h0 : bgf2_IndexAllOpen ω L 0) {x : Site 2} : bgf2_q ω L x = 0 ↔ bgn_idx L x = 0 := by
  unfold bgf2_q
  by_cases hP : bgf2_IndexAllOpen ω L (bgn_idx L x)
  · rw [if_pos hP]
    constructor
    · intro hc
      have hce : bgf2_centre L (bgn_idx L x) = bgf2_centre L 0 := by rw [hc, bgf2_centre_zero]
      exact bgf2_centre_inj hce
    · intro hc; rw [hc, bgf2_centre_zero]
  · rw [if_neg hP]
    constructor
    · intro hc; rw [hc]; exact bao_bgn_idx_zero L
    · intro hc; exfalso; apply hP; rw [hc]; exact h0


theorem bgf2_q_eq_zero_iff_mem {ω : ConfigSpace (Sym2 (Site 2))} {L : ℕ}
    (h0 : bgf2_IndexAllOpen ω L 0) {x : Site 2} :
    bgf2_q ω L x = 0 ↔ x ∈ bc61_boxAround 2 L 0 := by
  rw [bgf2_q_eq_zero_iff h0, bgf2_mem_box0_iff]




theorem bgf2_indexAllOpen_cut {ω : ConfigSpace (Sym2 (Site 2))} {L : ℕ} {j : Site 2}
    (h : bgf2_IndexAllOpen ω L j) (hj : j ≠ 0) :
    bgf2_IndexAllOpen (removeSites (bc61_boxAround 2 L 0) ω) L j := by
  intro x y hx hy hadj
  have hxout : x ∉ bc61_boxAround 2 L 0 := by
    intro hin; exact hj (by rw [← hx]; exact bgf2_mem_box0_iff.mp hin)
  have hyout : y ∉ bc61_boxAround 2 L 0 := by
    intro hin; exact hj (by rw [← hy]; exact bgf2_mem_box0_iff.mp hin)
  rw [bc61_removeBox_apply_of_notMem hxout hyout]
  exact h x y hx hy hadj





theorem bgf2_cut_q_eq_connected {ω : ConfigSpace (Sym2 (Site 2))} {L : ℕ}
    (h0 : bgf2_IndexAllOpen ω L 0) {a b : Site 2}
    (h : bgf2_q ω L a = bgf2_q ω L b) (hne : bgf2_q ω L a ≠ 0) :
    Connected 2 (removeSites (bc61_boxAround 2 L 0) ω) a b := by
  have hja : bgn_idx L a ≠ 0 := fun hj => hne ((bgf2_q_eq_zero_iff h0).mpr hj)
  unfold bgf2_q at h
  by_cases hPa : bgf2_IndexAllOpen ω L (bgn_idx L a)
  · rw [if_pos hPa] at h
    by_cases hPb : bgf2_IndexAllOpen ω L (bgn_idx L b)
    · rw [if_pos hPb] at h
      have hidx := bgf2_centre_inj h
      exact bgf2_indexAllOpen_connected (bgf2_indexAllOpen_cut hPa hja) rfl hidx.symm
    · rw [if_neg hPb] at h
      exfalso; apply hPb
      have hbi : bgn_idx L b = bgn_idx L a := by rw [← h, bgf2_idx_centre]
      rw [hbi]; exact hPa
  · rw [if_neg hPa] at h
    by_cases hPb : bgf2_IndexAllOpen ω L (bgn_idx L b)
    · rw [if_pos hPb] at h
      exfalso; apply hPa
      have hai : bgn_idx L a = bgn_idx L b := by rw [h, bgf2_idx_centre]
      rw [hai]; exact hPb
    · rw [if_neg hPb] at h
      rw [h]






theorem bgf2_cut_connected_of_reach_aux {ω : ConfigSpace (Sym2 (Site 2))} {L : ℕ}
    (h0 : bgf2_IndexAllOpen ω L 0) :
    ∀ {u v : Site 2}, (bkg_deleteVertex (bgf2_Gf ω L) 0).Reachable u v →
      ∀ a b, bgf2_q ω L a = u → bgf2_q ω L b = v → u ≠ 0 → v ≠ 0 →
        Connected 2 (removeSites (bc61_boxAround 2 L 0) ω) a b := by
  intro u v h
  obtain ⟨p⟩ := h
  induction p with
  | nil =>
    intro a b ha hb hu hv
    exact bgf2_cut_q_eq_connected h0 (ha.trans hb.symm) (by rw [ha]; exact hu)
  | @cons u z v hadj q ih =>
    intro a b ha hb hu hv
    obtain ⟨⟨huz, a', b', ha', hb', hab'⟩, hune, hzne⟩ := hadj
    have h1 : Connected 2 (removeSites (bc61_boxAround 2 L 0) ω) a a' :=
      bgf2_cut_q_eq_connected h0 (ha.trans ha'.symm) (by rw [ha]; exact hu)
    have ha'out : a' ∉ bc61_boxAround 2 L 0 := by
      rw [← bgf2_q_eq_zero_iff_mem h0]; rw [ha']; exact hune
    have hb'out : b' ∉ bc61_boxAround 2 L 0 := by
      rw [← bgf2_q_eq_zero_iff_mem h0]; rw [hb']; exact hzne
    have h2 : Connected 2 (removeSites (bc61_boxAround 2 L 0) ω) a' b' :=
      bc61_cut_adj_connected hab'.1 hab'.2 ha'out hb'out
    have h3 : Connected 2 (removeSites (bc61_boxAround 2 L 0) ω) b' b := ih b' b hb' hb hzne hv
    exact (h1.trans h2).trans h3

#check @bgf2_cut_connected_of_reach_aux













theorem bgf2_trif_separation {ω : ConfigSpace (Sym2 (Site 2))} {L : ℕ} (h : bao_AllOpenTrif ω L) :
    ∃ w₁ w₂ w₃ : Site 2,
      w₁ ≠ (0 : Site 2) ∧ w₂ ≠ (0 : Site 2) ∧ w₃ ≠ (0 : Site 2) ∧
      ¬ (bkg_deleteVertex (bgf2_Gf ω L) 0).Reachable w₁ w₂ ∧
      ¬ (bkg_deleteVertex (bgf2_Gf ω L) 0).Reachable w₁ w₃ ∧
      ¬ (bkg_deleteVertex (bgf2_Gf ω L) 0).Reachable w₂ w₃ := by
  obtain ⟨htri, hbox⟩ := h
  have h0 : bgf2_IndexAllOpen ω L 0 := bgf2_indexAllOpen_zero_of_bff hbox
  obtain ⟨a₁, a₂, a₃, _hinc, ⟨hinf₁, hinf₂, hinf₃⟩, hcut₁₂, hcut₁₃, hcut₂₃⟩ := htri
  have hout₁ : a₁ ∉ bc61_boxAround 2 L 0 := bsc_notMem_box_of_infinite hinf₁
  have hout₂ : a₂ ∉ bc61_boxAround 2 L 0 := bsc_notMem_box_of_infinite hinf₂
  have hout₃ : a₃ ∉ bc61_boxAround 2 L 0 := bsc_notMem_box_of_infinite hinf₃
  have hne₁ : bgf2_q ω L a₁ ≠ 0 := fun hz => hout₁ ((bgf2_q_eq_zero_iff_mem h0).mp hz)
  have hne₂ : bgf2_q ω L a₂ ≠ 0 := fun hz => hout₂ ((bgf2_q_eq_zero_iff_mem h0).mp hz)
  have hne₃ : bgf2_q ω L a₃ ≠ 0 := fun hz => hout₃ ((bgf2_q_eq_zero_iff_mem h0).mp hz)
  refine ⟨bgf2_q ω L a₁, bgf2_q ω L a₂, bgf2_q ω L a₃, hne₁, hne₂, hne₃, ?_, ?_, ?_⟩
  · intro hr
    exact hcut₁₂ ((bc67_Gn_deletion_eq_removeSites ω L 0 a₁ a₂).mpr
      (bgf2_cut_connected_of_reach_aux h0 hr a₁ a₂ rfl rfl hne₁ hne₂))
  · intro hr
    exact hcut₁₃ ((bc67_Gn_deletion_eq_removeSites ω L 0 a₁ a₃).mpr
      (bgf2_cut_connected_of_reach_aux h0 hr a₁ a₃ rfl rfl hne₁ hne₃))
  · intro hr
    exact hcut₂₃ ((bc67_Gn_deletion_eq_removeSites ω L 0 a₂ a₃).mpr
      (bgf2_cut_connected_of_reach_aux h0 hr a₂ a₃ rfl rfl hne₂ hne₃))

#check @bgf2_trif_separation






theorem bgf2_trif_deg3 {V : Type*} [Fintype V] {H T : SimpleGraph V} [DecidableRel T.Adj]
    (hTH : T ≤ H) (hTconn : T.Connected) {hub w₁ w₂ w₃ : V}
    (hne₁ : w₁ ≠ hub) (hne₂ : w₂ ≠ hub) (hne₃ : w₃ ≠ hub)
    (hs₁₂ : ¬ (bkg_deleteVertex H hub).Reachable w₁ w₂)
    (hs₁₃ : ¬ (bkg_deleteVertex H hub).Reachable w₁ w₃)
    (hs₂₃ : ¬ (bkg_deleteVertex H hub).Reachable w₂ w₃) :
    3 ≤ T.degree hub :=
  bcv_trif_degree_ge_three hTH hTconn hne₁ hne₂ hne₃ hs₁₂ hs₁₃ hs₂₃

#check @bgf2_trif_deg3










theorem bgf2_onlyBox0_hub_merged {L : ℕ} : bgf2_IndexAllOpen (bao_onlyBox0 L) L 0 :=
  bgf2_indexAllOpen_zero_of_bff (bao_onlyBox0_allOpen L)




theorem bgf2_onlyBox0_not_merged {L : ℕ} (hL : 1 ≤ L) :
    ¬ bgf2_IndexAllOpen (bao_onlyBox0 L) L (bc57_pt 1 0) := by
  intro H
  have hi0 : bgn_idx L (bc57_pt (2 * (L : ℤ) + 1) 0) = bc57_pt 1 0 :=
    bao_bgn_idx_box10 hL 0 (le_refl 0) (by positivity)
  have hi1 : bgn_idx L (bc57_pt (2 * (L : ℤ) + 1) 1) = bc57_pt 1 0 :=
    bao_bgn_idx_box10 hL 1 (by norm_num) (by exact_mod_cast hL)
  have hadj : (hypercubicLattice 2).Adj (bc57_pt (2 * (L : ℤ) + 1) 0) (bc57_pt (2 * (L : ℤ) + 1) 1) := by
    rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp only [bc57_pt_fst, bc57_pt_snd]; omega
  have hopen := H _ _ hi0 hi1 hadj
  have hclosed : bao_onlyBox0 L s(bc57_pt (2 * (L : ℤ) + 1) 0, bc57_pt (2 * (L : ℤ) + 1) 1) = false := by
    unfold bao_onlyBox0
    rw [if_neg]
    intro hmem
    have hbox := bao_boxEdges_fst hmem
    have hn := (Lattice.mem_box).mp hbox 0
    rw [bc57_pt_fst] at hn
    omega
  rw [hclosed] at hopen
  exact absurd hopen (by decide)





theorem bgf2_onlyBox0_not_identified {L : ℕ} (hL : 1 ≤ L) :
    bgf2_q (bao_onlyBox0 L) L (bc57_pt (2 * (L : ℤ) + 1) 0)
      ≠ bgf2_q (bao_onlyBox0 L) L (bc57_pt (2 * (L : ℤ) + 1) 1) := by
  have hnm : ¬ bgf2_IndexAllOpen (bao_onlyBox0 L) L (bc57_pt 1 0) := bgf2_onlyBox0_not_merged hL
  have hi0 : bgn_idx L (bc57_pt (2 * (L : ℤ) + 1) 0) = bc57_pt 1 0 :=
    bao_bgn_idx_box10 hL 0 (le_refl 0) (by positivity)
  have hi1 : bgn_idx L (bc57_pt (2 * (L : ℤ) + 1) 1) = bc57_pt 1 0 :=
    bao_bgn_idx_box10 hL 1 (by norm_num) (by exact_mod_cast hL)
  have hq0 : bgf2_q (bao_onlyBox0 L) L (bc57_pt (2 * (L : ℤ) + 1) 0)
      = bc57_pt (2 * (L : ℤ) + 1) 0 := by unfold bgf2_q; rw [hi0, if_neg hnm]
  have hq1 : bgf2_q (bao_onlyBox0 L) L (bc57_pt (2 * (L : ℤ) + 1) 1)
      = bc57_pt (2 * (L : ℤ) + 1) 1 := by unfold bgf2_q; rw [hi1, if_neg hnm]
  rw [hq0, hq1]
  intro hc
  have := congrFun hc 1
  rw [bc57_pt_snd, bc57_pt_snd] at this
  omega




theorem bgf2_onlyBox0_box_connected {L : ℕ} {a b : Site 2}
    (ha : bgn_idx L a = 0) (hb : bgn_idx L b = 0) :
    Connected 2 (bao_onlyBox0 L) a b :=
  bgf2_indexAllOpen_connected bgf2_onlyBox0_hub_merged ha hb

#check @bgf2_onlyBox0_not_merged
#check @bgf2_onlyBox0_not_identified
#check @bgf2_onlyBox0_box_connected









































theorem bgf2_status :
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ) (a b : Site 2),
      (bgf2_Gf ω L).Reachable (bgf2_q ω L a) (bgf2_q ω L b) ↔ Connected 2 ω a b) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ), bao_AllOpenTrif ω L →
      ∃ w₁ w₂ w₃ : Site 2, w₁ ≠ 0 ∧ w₂ ≠ 0 ∧ w₃ ≠ 0 ∧
        ¬ (bkg_deleteVertex (bgf2_Gf ω L) 0).Reachable w₁ w₂ ∧
        ¬ (bkg_deleteVertex (bgf2_Gf ω L) 0).Reachable w₁ w₃ ∧
        ¬ (bkg_deleteVertex (bgf2_Gf ω L) 0).Reachable w₂ w₃) ∧
    
    (∀ (L : ℕ), 1 ≤ L → ¬ bgf2_IndexAllOpen (bao_onlyBox0 L) L (bc57_pt 1 0)) :=
  ⟨fun ω L a b => bgf2_faithful ω L a b,
   fun ω L h => bgf2_trif_separation h,
   fun L hL => bgf2_onlyBox0_not_merged hL⟩

#check @bgf2_status

end StatMech.Walls


#print axioms StatMech.Walls.bgf2_boxCentre_connected
#print axioms StatMech.Walls.bgf2_faithful
#print axioms StatMech.Walls.bgf2_cut_connected_of_reach_aux
#print axioms StatMech.Walls.bgf2_trif_separation
#print axioms StatMech.Walls.bgf2_trif_deg3
#print axioms StatMech.Walls.bgf2_onlyBox0_not_merged
#print axioms StatMech.Walls.bgf2_onlyBox0_not_identified
