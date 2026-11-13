/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.FrontierA.AllOpenBoxGeneral

open Set SimpleGraph Finset

namespace StatMech.FrontierA

open StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation
open StatMech.Walls

variable {d : ℕ}

noncomputable local instance bgfdPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p



noncomputable def bgfdQ (omega : ConfigSpace (Sym2 (Site d)))
    (L : ℕ) (x : Site d) : Site d :=
  if BgfdIndexAllOpen omega L (bgn_idx L x) then
    bgfdCentre L (bgn_idx L x)
  else x


def bgfdGraph (omega : ConfigSpace (Sym2 (Site d)))
    (L : ℕ) : SimpleGraph (Site d) where
  Adj u v := u ≠ v ∧ ∃ a b : Site d,
    bgfdQ omega L a = u ∧ bgfdQ omega L b = v ∧
      (openSubgraph d omega).Adj a b
  symm := by
    rintro u v ⟨huv, a, b, ha, hb, hab⟩
    exact ⟨huv.symm, b, a, hb, ha, hab.symm⟩

@[simp] theorem bgfdGraph_adj
    (omega : ConfigSpace (Sym2 (Site d))) (L : ℕ) (u v : Site d) :
    (bgfdGraph omega L).Adj u v ↔
      u ≠ v ∧ ∃ a b : Site d,
        bgfdQ omega L a = u ∧ bgfdQ omega L b = v ∧
          (openSubgraph d omega).Adj a b :=
  Iff.rfl


theorem bgfd_q_eq_connected
    {omega : ConfigSpace (Sym2 (Site d))} {L : ℕ} {a b : Site d}
    (h : bgfdQ omega L a = bgfdQ omega L b) :
    Connected d omega a b := by
  unfold bgfdQ at h
  by_cases hPa : BgfdIndexAllOpen omega L (bgn_idx L a)
  · rw [if_pos hPa] at h
    by_cases hPb : BgfdIndexAllOpen omega L (bgn_idx L b)
    · rw [if_pos hPb] at h
      have hidx := bgfd_centre_injective L h
      exact bgfd_indexAllOpen_connected hPa rfl hidx.symm
    · rw [if_neg hPb] at h
      exfalso
      apply hPb
      have hbi : bgn_idx L b = bgn_idx L a := by
        rw [← h, bgfd_idx_centre]
      rw [hbi]
      exact hPa
  · rw [if_neg hPa] at h
    by_cases hPb : BgfdIndexAllOpen omega L (bgn_idx L b)
    · rw [if_pos hPb] at h
      exfalso
      apply hPa
      have hai : bgn_idx L a = bgn_idx L b := by
        rw [h, bgfd_idx_centre]
      rw [hai]
      exact hPb
    · rw [if_neg hPb] at h
      rw [h]


theorem bgfd_reach_of_connected
    {omega : ConfigSpace (Sym2 (Site d))} {L : ℕ} {a b : Site d}
    (h : Connected d omega a b) :
    (bgfdGraph omega L).Reachable (bgfdQ omega L a) (bgfdQ omega L b) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact Reachable.refl _
  | @cons x z b hadj q ih =>
      refine Reachable.trans ?_ ih
      by_cases hqxz : bgfdQ omega L x = bgfdQ omega L z
      · rw [hqxz]
      · exact SimpleGraph.Adj.reachable ⟨hqxz, x, z, rfl, rfl, hadj⟩


theorem bgfd_connected_of_reach_aux
    {omega : ConfigSpace (Sym2 (Site d))} {L : ℕ} :
    ∀ {u v : Site d}, (bgfdGraph omega L).Reachable u v →
      ∀ a b, bgfdQ omega L a = u → bgfdQ omega L b = v →
        Connected d omega a b := by
  intro u v h
  obtain ⟨p⟩ := h
  induction p with
  | nil =>
      intro a b ha hb
      exact bgfd_q_eq_connected (ha.trans hb.symm)
  | @cons u z v hadj q ih =>
      intro a b ha hb
      obtain ⟨huz, a', b', ha', hb', hab'⟩ := hadj
      have h1 : Connected d omega a a' :=
        bgfd_q_eq_connected (ha.trans ha'.symm)
      have h2 : Connected d omega a' b' :=
        SimpleGraph.Adj.reachable hab'
      have h3 : Connected d omega b' b := ih b' b hb' hb
      exact (h1.trans h2).trans h3


theorem bgfd_faithful
    (omega : ConfigSpace (Sym2 (Site d))) (L : ℕ) (a b : Site d) :
    (bgfdGraph omega L).Reachable (bgfdQ omega L a) (bgfdQ omega L b) ↔
      Connected d omega a b := by
  constructor
  · intro h
    exact bgfd_connected_of_reach_aux h a b rfl rfl
  · exact bgfd_reach_of_connected


theorem bgfd_mem_box0_iff {L : ℕ} {x : Site d} :
    x ∈ bc61_boxAround d L 0 ↔ bgn_idx L x = 0 := by
  rw [bc61_mem_boxAround, sub_zero]
  rw [bgfd_idx_iff_inBox]
  simp only [bgfdCentre, Pi.zero_apply, mul_zero, sub_zero, bgfdInBox]
  exact mem_box



theorem bgfd_q_eq_zero_iff
    {omega : ConfigSpace (Sym2 (Site d))} {L : ℕ}
    (h0 : BgfdIndexAllOpen omega L 0) {x : Site d} :
    bgfdQ omega L x = 0 ↔ bgn_idx L x = 0 := by
  unfold bgfdQ
  by_cases hP : BgfdIndexAllOpen omega L (bgn_idx L x)
  · rw [if_pos hP]
    constructor
    · intro hc
      have hce : bgfdCentre L (bgn_idx L x) = bgfdCentre L 0 := by
        rw [hc, bgfd_centre_zero]
      exact bgfd_centre_injective L hce
    · intro hc
      rw [hc, bgfd_centre_zero]
  · rw [if_neg hP]
    constructor
    · intro hc
      subst x
      rw [← bgfd_centre_zero (d := d) L]
      exact bgfd_idx_centre L 0
    · intro hc
      exfalso
      apply hP
      rw [hc]
      exact h0

theorem bgfd_q_eq_zero_iff_mem
    {omega : ConfigSpace (Sym2 (Site d))} {L : ℕ}
    (h0 : BgfdIndexAllOpen omega L 0) {x : Site d} :
    bgfdQ omega L x = 0 ↔ x ∈ bc61_boxAround d L 0 := by
  rw [bgfd_q_eq_zero_iff h0, bgfd_mem_box0_iff]



theorem bgfd_indexAllOpen_cut
    {omega : ConfigSpace (Sym2 (Site d))} {L : ℕ} {j : Site d}
    (h : BgfdIndexAllOpen omega L j) (hj : j ≠ 0) :
    BgfdIndexAllOpen
      (removeSites (bc61_boxAround d L 0) omega) L j := by
  intro x y hx hy hadj
  have hxout : x ∉ bc61_boxAround d L 0 := by
    intro hin
    exact hj (by rw [← hx]; exact bgfd_mem_box0_iff.mp hin)
  have hyout : y ∉ bc61_boxAround d L 0 := by
    intro hin
    exact hj (by rw [← hy]; exact bgfd_mem_box0_iff.mp hin)
  rw [bc61_removeBox_apply_of_notMem hxout hyout]
  exact h x y hx hy hadj


theorem bgfd_cut_q_eq_connected
    {omega : ConfigSpace (Sym2 (Site d))} {L : ℕ}
    (h0 : BgfdIndexAllOpen omega L 0) {a b : Site d}
    (h : bgfdQ omega L a = bgfdQ omega L b)
    (hne : bgfdQ omega L a ≠ 0) :
    Connected d (removeSites (bc61_boxAround d L 0) omega) a b := by
  have hja : bgn_idx L a ≠ 0 :=
    fun hj => hne ((bgfd_q_eq_zero_iff h0).mpr hj)
  unfold bgfdQ at h
  by_cases hPa : BgfdIndexAllOpen omega L (bgn_idx L a)
  · rw [if_pos hPa] at h
    by_cases hPb : BgfdIndexAllOpen omega L (bgn_idx L b)
    · rw [if_pos hPb] at h
      have hidx := bgfd_centre_injective L h
      exact bgfd_indexAllOpen_connected
        (bgfd_indexAllOpen_cut hPa hja) rfl hidx.symm
    · rw [if_neg hPb] at h
      exfalso
      apply hPb
      have hbi : bgn_idx L b = bgn_idx L a := by
        rw [← h, bgfd_idx_centre]
      rw [hbi]
      exact hPa
  · rw [if_neg hPa] at h
    by_cases hPb : BgfdIndexAllOpen omega L (bgn_idx L b)
    · rw [if_pos hPb] at h
      exfalso
      apply hPa
      have hai : bgn_idx L a = bgn_idx L b := by
        rw [h, bgfd_idx_centre]
      rw [hai]
      exact hPb
    · rw [if_neg hPb] at h
      rw [h]



theorem bgfd_cut_connected_of_reach_aux
    {omega : ConfigSpace (Sym2 (Site d))} {L : ℕ}
    (h0 : BgfdIndexAllOpen omega L 0) :
    ∀ {u v : Site d},
      (bkg_deleteVertex (bgfdGraph omega L) 0).Reachable u v →
      ∀ a b, bgfdQ omega L a = u → bgfdQ omega L b = v →
        u ≠ 0 → v ≠ 0 →
        Connected d (removeSites (bc61_boxAround d L 0) omega) a b := by
  intro u v h
  obtain ⟨p⟩ := h
  induction p with
  | nil =>
      intro a b ha hb hu hv
      exact bgfd_cut_q_eq_connected h0 (ha.trans hb.symm)
        (by rw [ha]; exact hu)
  | @cons u z v hadj q ih =>
      intro a b ha hb hu hv
      obtain ⟨⟨huz, a', b', ha', hb', hab'⟩, hune, hzne⟩ := hadj
      have h1 : Connected d
          (removeSites (bc61_boxAround d L 0) omega) a a' :=
        bgfd_cut_q_eq_connected h0 (ha.trans ha'.symm)
          (by rw [ha]; exact hu)
      have ha'out : a' ∉ bc61_boxAround d L 0 := by
        rw [← bgfd_q_eq_zero_iff_mem h0, ha']
        exact hune
      have hb'out : b' ∉ bc61_boxAround d L 0 := by
        rw [← bgfd_q_eq_zero_iff_mem h0, hb']
        exact hzne
      have h2 : Connected d
          (removeSites (bc61_boxAround d L 0) omega) a' b' :=
        bc61_cut_adj_connected hab'.1 hab'.2 ha'out hb'out
      have h3 : Connected d
          (removeSites (bc61_boxAround d L 0) omega) b' b :=
        ih b' b hb' hb hzne hv
      exact (h1.trans h2).trans h3



theorem bgfd_mem_box_centre_iff {L : ℕ} {j x : Site d} :
    x ∈ bc61_boxAround d L (bgfdCentre L j) ↔ bgn_idx L x = j := by
  rw [bc61_mem_boxAround, bgfd_idx_iff_inBox]
  simp only [mem_box, bgfdInBox, Pi.sub_apply]



theorem bgfd_q_eq_centre_iff
    {omega : ConfigSpace (Sym2 (Site d))} {L : ℕ} {j x : Site d}
    (hj : BgfdIndexAllOpen omega L j) :
    bgfdQ omega L x = bgfdCentre L j ↔ bgn_idx L x = j := by
  unfold bgfdQ
  by_cases hP : BgfdIndexAllOpen omega L (bgn_idx L x)
  · rw [if_pos hP]
    constructor
    · intro h
      exact bgfd_centre_injective (d := d) L h
    · intro h
      rw [h]
  · rw [if_neg hP]
    constructor
    · intro h
      exfalso
      apply hP
      have hidx : bgn_idx L x = j := by
        rw [h, bgfd_idx_centre]
      rwa [hidx]
    · intro h
      exfalso
      apply hP
      rwa [h]



theorem bgfd_indexAllOpen_cut_at
    {omega : ConfigSpace (Sym2 (Site d))} {L : ℕ} {j k : Site d}
    (hk : BgfdIndexAllOpen omega L k) (hkj : k ≠ j) :
    BgfdIndexAllOpen
      (removeSites (bc61_boxAround d L (bgfdCentre L j)) omega) L k := by
  intro x y hx hy hadj
  have hxout : x ∉ bc61_boxAround d L (bgfdCentre L j) := by
    intro hin
    apply hkj
    rw [← hx]
    exact bgfd_mem_box_centre_iff.mp hin
  have hyout : y ∉ bc61_boxAround d L (bgfdCentre L j) := by
    intro hin
    apply hkj
    rw [← hy]
    exact bgfd_mem_box_centre_iff.mp hin
  rw [bc61_removeBox_apply_of_notMem hxout hyout]
  exact hk x y hx hy hadj

theorem bgfd_cut_q_eq_connected_at
    {omega : ConfigSpace (Sym2 (Site d))} {L : ℕ} {j a b : Site d}
    (hj : BgfdIndexAllOpen omega L j)
    (h : bgfdQ omega L a = bgfdQ omega L b)
    (hne : bgfdQ omega L a ≠ bgfdCentre L j) :
    Connected d
      (removeSites (bc61_boxAround d L (bgfdCentre L j)) omega) a b := by
  have hja : bgn_idx L a ≠ j :=
    fun hidx => hne ((bgfd_q_eq_centre_iff hj).2 hidx)
  unfold bgfdQ at h
  by_cases hPa : BgfdIndexAllOpen omega L (bgn_idx L a)
  · rw [if_pos hPa] at h
    by_cases hPb : BgfdIndexAllOpen omega L (bgn_idx L b)
    · rw [if_pos hPb] at h
      have hidx := bgfd_centre_injective L h
      exact bgfd_indexAllOpen_connected
        (bgfd_indexAllOpen_cut_at hPa hja) rfl hidx.symm
    · rw [if_neg hPb] at h
      exfalso
      apply hPb
      have hbi : bgn_idx L b = bgn_idx L a := by
        rw [← h, bgfd_idx_centre]
      rwa [hbi]
  · rw [if_neg hPa] at h
    by_cases hPb : BgfdIndexAllOpen omega L (bgn_idx L b)
    · rw [if_pos hPb] at h
      exfalso
      apply hPa
      have hai : bgn_idx L a = bgn_idx L b := by
        rw [h, bgfd_idx_centre]
      rwa [hai]
    · rw [if_neg hPb] at h
      rw [h]


theorem bgfd_cut_connected_of_reach_at
    {omega : ConfigSpace (Sym2 (Site d))} {L : ℕ} {j : Site d}
    (hj : BgfdIndexAllOpen omega L j) :
    ∀ {u v : Site d},
      (bkg_deleteVertex (bgfdGraph omega L) (bgfdCentre L j)).Reachable u v →
      ∀ a b, bgfdQ omega L a = u → bgfdQ omega L b = v →
        u ≠ bgfdCentre L j → v ≠ bgfdCentre L j →
        Connected d
          (removeSites (bc61_boxAround d L (bgfdCentre L j)) omega) a b := by
  intro u v h
  obtain ⟨p⟩ := h
  induction p with
  | nil =>
      intro a b ha hb hu hv
      exact bgfd_cut_q_eq_connected_at hj (ha.trans hb.symm)
        (by rw [ha]; exact hu)
  | @cons u z v hadj p ih =>
      intro a b ha hb hu hv
      obtain ⟨⟨huz, a', b', ha', hb', hab'⟩, hune, hzne⟩ := hadj
      have h1 : Connected d
          (removeSites (bc61_boxAround d L (bgfdCentre L j)) omega) a a' :=
        bgfd_cut_q_eq_connected_at hj (ha.trans ha'.symm)
          (by rw [ha]; exact hu)
      have ha'out : a' ∉ bc61_boxAround d L (bgfdCentre L j) := by
        rw [bgfd_mem_box_centre_iff, ← bgfd_q_eq_centre_iff hj, ha']
        exact hune
      have hb'out : b' ∉ bc61_boxAround d L (bgfdCentre L j) := by
        rw [bgfd_mem_box_centre_iff, ← bgfd_q_eq_centre_iff hj, hb']
        exact hzne
      have h2 : Connected d
          (removeSites (bc61_boxAround d L (bgfdCentre L j)) omega) a' b' :=
        bc61_cut_adj_connected hab'.1 hab'.2 ha'out hb'out
      have h3 : Connected d
          (removeSites (bc61_boxAround d L (bgfdCentre L j)) omega) b' b :=
        ih b' b hb' hb hzne hv
      exact (h1.trans h2).trans h3



theorem bgfd_deleted_reachable_of_cut_connected
    {omega : ConfigSpace (Sym2 (Site d))} {L : ℕ} {j : Site d}
    (hj : BgfdIndexAllOpen omega L j) {a b : Site d}
    (h : Connected d
      (removeSites (bc61_boxAround d L (bgfdCentre L j)) omega) a b) :
    (bkg_deleteVertex (bgfdGraph omega L) (bgfdCentre L j)).Reachable
      (bgfdQ omega L a) (bgfdQ omega L b) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact Reachable.refl _
  | @cons x z b hadj p ih =>
      refine Reachable.trans ?_ ih
      have hxout : x ∉ bc61_boxAround d L (bgfdCentre L j) := by
        intro hx
        exact stac_removeSites_no_neighbor
          (bc61_boxAround d L (bgfdCentre L j)) omega hx hadj
      have hzout : z ∉ bc61_boxAround d L (bgfdCentre L j) := by
        intro hz
        exact stac_removeSites_no_neighbor
          (bc61_boxAround d L (bgfdCentre L j)) omega hz hadj.symm
      have hxh : bgfdQ omega L x ≠ bgfdCentre L j := by
        intro hx
        exact hxout (bgfd_mem_box_centre_iff.mpr
          ((bgfd_q_eq_centre_iff hj).mp hx))
      have hzh : bgfdQ omega L z ≠ bgfdCentre L j := by
        intro hz
        exact hzout (bgfd_mem_box_centre_iff.mpr
          ((bgfd_q_eq_centre_iff hj).mp hz))
      by_cases heq : bgfdQ omega L x = bgfdQ omega L z
      · rw [heq]
      · apply SimpleGraph.Adj.reachable
        rw [bkg_deleteVertex_adj]
        refine ⟨?_, hxh, hzh⟩
        rw [bgfdGraph_adj]
        exact ⟨heq, x, z, rfl, rfl,
          openSubgraph_mono
            (daep_removeSites_le
              (bc61_boxAround d L (bgfdCentre L j)) omega) hadj⟩

end StatMech.FrontierA
