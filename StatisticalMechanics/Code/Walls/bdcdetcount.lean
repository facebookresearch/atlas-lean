/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










































import Mathlib
import Code.Walls.bfctfinitecount
import Code.Walls.bsgspantreegn

open Set SimpleGraph Finset
open StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000

namespace StatMech.Walls









def bdc_allOpenCfg : ConfigSpace (Sym2 (Site 2)) := fun _ => true


theorem bdc_allOpen_indexAllOpen (L : ℕ) (j : Site 2) :
    bgf2_IndexAllOpen bdc_allOpenCfg L j := by
  intro x y hx hy hadj; rfl


theorem bdc_idx_ptL0 (L : ℕ) : bgn_idx L (bc57_pt (L : ℤ) 0) = 0 := by
  funext i
  fin_cases i
  · show ((bc57_pt (L : ℤ) 0) 0 + (L : ℤ)) / (2 * (L : ℤ) + 1) = (0 : Site 2) 0
    rw [bc57_pt_fst]; exact Int.ediv_eq_zero_of_lt (by positivity) (by omega)
  · show ((bc57_pt (L : ℤ) 0) 1 + (L : ℤ)) / (2 * (L : ℤ) + 1) = (0 : Site 2) 1
    rw [bc57_pt_snd]; exact Int.ediv_eq_zero_of_lt (by positivity) (by omega)


theorem bdc_idx_ptL10 (L : ℕ) : bgn_idx L (bc57_pt ((L : ℤ) + 1) 0) = bc57_pt 1 0 := by
  funext i
  fin_cases i
  · show ((bc57_pt ((L : ℤ) + 1) 0) 0 + (L : ℤ)) / (2 * (L : ℤ) + 1) = (bc57_pt 1 0) 0
    rw [bc57_pt_fst, bc57_pt_fst]
    have hb : (2 * (L : ℤ) + 1) ≠ 0 := by positivity
    have hrw : ((L : ℤ) + 1) + (L : ℤ) = (0 : ℤ) + 1 * (2 * (L : ℤ) + 1) := by ring
    rw [hrw, Int.add_mul_ediv_right _ _ hb, Int.ediv_eq_zero_of_lt (by positivity) (by omega)]
    norm_num
  · show ((bc57_pt ((L : ℤ) + 1) 0) 1 + (L : ℤ)) / (2 * (L : ℤ) + 1) = (bc57_pt 1 0) 1
    rw [bc57_pt_snd, bc57_pt_snd]
    exact Int.ediv_eq_zero_of_lt (by positivity) (by omega)


theorem bdc_q_ptL0 (L : ℕ) : bgf2_q bdc_allOpenCfg L (bc57_pt (L : ℤ) 0) = 0 := by
  unfold bgf2_q
  rw [bdc_idx_ptL0, if_pos (bdc_allOpen_indexAllOpen L 0), bgf2_centre_zero]


theorem bdc_q_ptL10 (L : ℕ) :
    bgf2_q bdc_allOpenCfg L (bc57_pt ((L : ℤ) + 1) 0) = bc57_pt (2 * (L : ℤ) + 1) 0 := by
  unfold bgf2_q
  rw [bdc_idx_ptL10, if_pos (bdc_allOpen_indexAllOpen L (bc57_pt 1 0))]
  funext i; fin_cases i
  · show bgf2_centre L (bc57_pt 1 0) 0 = (bc57_pt (2 * (L : ℤ) + 1) 0) 0
    simp [bgf2_centre, bc57_pt_fst]
  · show bgf2_centre L (bc57_pt 1 0) 1 = (bc57_pt (2 * (L : ℤ) + 1) 0) 1
    simp [bgf2_centre, bc57_pt_snd]




theorem bdc_Gf_centre_edge (L : ℕ) :
    (bgf2_Gf bdc_allOpenCfg L).Adj 0 (bc57_pt (2 * (L : ℤ) + 1) 0) := by
  refine ⟨?_, bc57_pt (L : ℤ) 0, bc57_pt ((L : ℤ) + 1) 0, bdc_q_ptL0 L, bdc_q_ptL10 L, ?_⟩
  · intro hc
    have := congrFun hc 0
    rw [bc57_pt_fst] at this; simp only [Pi.zero_apply] at this; omega
  · rw [openSubgraph_adj]
    refine ⟨?_, rfl⟩
    rw [hypercubicLattice_adj, Fin.sum_univ_two, bc57_pt_fst, bc57_pt_fst, bc57_pt_snd, bc57_pt_snd]
    omega







theorem bdc_Gf_not_le_lattice {L : ℕ} (hL : 1 ≤ L) :
    ¬ (bgf2_Gf bdc_allOpenCfg L ≤ hypercubicLattice 2) := by
  intro hle
  have hadj := hle (bdc_Gf_centre_edge L)
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
  simp only [Pi.zero_apply, bc57_pt_fst, bc57_pt_snd] at hadj
  omega













theorem bdc_datum_implies_count (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ)
    (h : bau_ArmSubforestData ω L R) :
    bc61_coarseTcount ω L R ≤ boxSV_boundaryCard 2 R :=
  bca_datum_implies_count ω L R h











def bdc_shiftCfg (c : Site 2) (ω : ConfigSpace (Sym2 (Site 2))) : ConfigSpace (Sym2 (Site 2)) :=
  fun e => ω (Sym2.map (· + c) e)


@[simp] theorem bdc_shiftCfg_edge (c : Site 2) (ω : ConfigSpace (Sym2 (Site 2))) (x y : Site 2) :
    bdc_shiftCfg c ω s(x, y) = ω s(x + c, y + c) := by
  unfold bdc_shiftCfg; rw [Sym2.map_mk]


theorem bdc_lat_shift (c x y : Site 2) :
    (hypercubicLattice 2).Adj (x + c) (y + c) ↔ (hypercubicLattice 2).Adj x y := by
  rw [hypercubicLattice_adj, hypercubicLattice_adj]
  refine Iff.of_eq (congrArg (· = 1) ?_)
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Pi.add_apply]; congr 1; ring



theorem bdc_openSub_shift (c : Site 2) (ω : ConfigSpace (Sym2 (Site 2))) (x y : Site 2) :
    (openSubgraph 2 (bdc_shiftCfg c ω)).Adj x y ↔ (openSubgraph 2 ω).Adj (x + c) (y + c) := by
  rw [openSubgraph_adj, openSubgraph_adj, bdc_shiftCfg_edge, bdc_lat_shift]




theorem bdc_bgn_idx_shift (L : ℕ) (j x : Site 2) :
    bgn_idx L (x + bgf2_centre L j) = bgn_idx L x + j := by
  funext i
  have hb : (2 * (L : ℤ) + 1) ≠ 0 := by positivity
  show ((x + bgf2_centre L j) i + (L : ℤ)) / (2 * (L : ℤ) + 1) = bgn_idx L x i + j i
  rw [Pi.add_apply]
  show (x i + bgf2_centre L j i + (L : ℤ)) / (2 * (L : ℤ) + 1)
      = (x i + (L : ℤ)) / (2 * (L : ℤ) + 1) + j i
  have hc : bgf2_centre L j i = (2 * (L : ℤ) + 1) * j i := rfl
  rw [hc]
  have hrw : x i + (2 * (L : ℤ) + 1) * j i + (L : ℤ)
      = (x i + (L : ℤ)) + j i * (2 * (L : ℤ) + 1) := by ring
  rw [hrw, Int.add_mul_ediv_right _ _ hb]



theorem bdc_centre_add (L : ℕ) (a b : Site 2) :
    bgf2_centre L (a + b) = bgf2_centre L a + bgf2_centre L b := by
  funext i
  show (2 * (L : ℤ) + 1) * (a + b) i = (2 * (L : ℤ) + 1) * a i + (2 * (L : ℤ) + 1) * b i
  rw [Pi.add_apply]; ring




theorem bdc_indexAllOpen_shift (L : ℕ) (ω : ConfigSpace (Sym2 (Site 2))) (j k : Site 2) :
    bgf2_IndexAllOpen (bdc_shiftCfg (bgf2_centre L j) ω) L k ↔ bgf2_IndexAllOpen ω L (k + j) := by
  set c := bgf2_centre L j with hc
  constructor
  · intro H x' y' hx' hy' hadj'
    have hxc : bgn_idx L (x' - c) = k := by
      have := bdc_bgn_idx_shift L j (x' - c)
      rw [sub_add_cancel] at this; rw [this] at hx'; exact add_right_cancel hx'
    have hyc : bgn_idx L (y' - c) = k := by
      have := bdc_bgn_idx_shift L j (y' - c)
      rw [sub_add_cancel] at this; rw [this] at hy'; exact add_right_cancel hy'
    have hadjc : (hypercubicLattice 2).Adj (x' - c) (y' - c) := by
      have hh := bdc_lat_shift c (x' - c) (y' - c)
      rw [sub_add_cancel, sub_add_cancel] at hh; exact hh.mp hadj'
    have := H (x' - c) (y' - c) hxc hyc hadjc
    rwa [bdc_shiftCfg_edge, sub_add_cancel, sub_add_cancel] at this
  · intro H x y hx hy hadj
    rw [bdc_shiftCfg_edge]
    refine H (x + c) (y + c) ?_ ?_ ?_
    · rw [bdc_bgn_idx_shift, hx]
    · rw [bdc_bgn_idx_shift, hy]
    · rwa [bdc_lat_shift]




theorem bdc_q_shift (L : ℕ) (ω : ConfigSpace (Sym2 (Site 2))) (j x : Site 2) :
    bgf2_q (bdc_shiftCfg (bgf2_centre L j) ω) L x = bgf2_q ω L (x + bgf2_centre L j) - bgf2_centre L j := by
  set c := bgf2_centre L j with hc
  have key : bgn_idx L (x + c) = bgn_idx L x + j := bdc_bgn_idx_shift L j x
  unfold bgf2_q
  by_cases hP : bgf2_IndexAllOpen ω L (bgn_idx L (x + c))
  · have hPs : bgf2_IndexAllOpen (bdc_shiftCfg c ω) L (bgn_idx L x) := by
      rw [bdc_indexAllOpen_shift, ← key]; exact hP
    rw [if_pos hPs, if_pos hP, key, hc, bdc_centre_add]
    abel
  · have hPs : ¬ bgf2_IndexAllOpen (bdc_shiftCfg c ω) L (bgn_idx L x) := by
      rw [bdc_indexAllOpen_shift, ← key]; exact hP
    rw [if_neg hPs, if_neg hP]; abel






theorem bdc_Gf_shift_adj (L : ℕ) (ω : ConfigSpace (Sym2 (Site 2))) (j u v : Site 2) :
    (bgf2_Gf (bdc_shiftCfg (bgf2_centre L j) ω) L).Adj u v ↔
      (bgf2_Gf ω L).Adj (u + bgf2_centre L j) (v + bgf2_centre L j) := by
  set c := bgf2_centre L j with hc
  rw [bgf2_Gf_adj, bgf2_Gf_adj]
  constructor
  · rintro ⟨huv, a, b, ha, hb, hab⟩
    refine ⟨fun h => huv (add_right_cancel h), a + c, b + c, ?_, ?_,
      (bdc_openSub_shift c ω a b).mp hab⟩
    · have := ha; rw [bdc_q_shift] at this; exact sub_eq_iff_eq_add.mp this
    · have := hb; rw [bdc_q_shift] at this; exact sub_eq_iff_eq_add.mp this
  · rintro ⟨huv, a', b', ha', hb', hab'⟩
    refine ⟨fun h => huv (by rw [h]), a' - c, b' - c, ?_, ?_, ?_⟩
    · rw [bdc_q_shift, sub_add_cancel, ha', add_sub_cancel_right]
    · rw [bdc_q_shift, sub_add_cancel, hb', add_sub_cancel_right]
    · rw [bdc_openSub_shift, sub_add_cancel, sub_add_cancel]; exact hab'




def bdc_delHom (L : ℕ) (ω : ConfigSpace (Sym2 (Site 2))) (j : Site 2) :
    bkg_deleteVertex (bgf2_Gf ω L) (bgf2_centre L j) →g
      bkg_deleteVertex (bgf2_Gf (bdc_shiftCfg (bgf2_centre L j) ω) L) 0 where
  toFun p := p - bgf2_centre L j
  map_rel' := by
    rintro p q ⟨hadj, hp, hq⟩
    refine ⟨?_, sub_ne_zero.mpr hp, sub_ne_zero.mpr hq⟩
    rw [bdc_Gf_shift_adj, sub_add_cancel, sub_add_cancel]; exact hadj




theorem bdc_cut_transport (L : ℕ) (ω : ConfigSpace (Sym2 (Site 2))) (j w₁ w₂ : Site 2)
    (h : ¬ (bkg_deleteVertex (bgf2_Gf (bdc_shiftCfg (bgf2_centre L j) ω) L) 0).Reachable w₁ w₂) :
    ¬ (bkg_deleteVertex (bgf2_Gf ω L) (bgf2_centre L j)).Reachable
        (w₁ + bgf2_centre L j) (w₂ + bgf2_centre L j) := by
  intro hr
  apply h
  have hm := hr.map (bdc_delHom L ω j)
  have e1 : (bdc_delHom L ω j) (w₁ + bgf2_centre L j) = w₁ := add_sub_cancel_right _ _
  have e2 : (bdc_delHom L ω j) (w₂ + bgf2_centre L j) = w₂ := add_sub_cancel_right _ _
  rw [e1, e2] at hm; exact hm








theorem bdc_trif_separation_at (L : ℕ) (ω : ConfigSpace (Sym2 (Site 2))) (j : Site 2)
    (h : bao_AllOpenTrif (bdc_shiftCfg (bgf2_centre L j) ω) L) :
    ∃ w₁ w₂ w₃ : Site 2,
      w₁ ≠ bgf2_centre L j ∧ w₂ ≠ bgf2_centre L j ∧ w₃ ≠ bgf2_centre L j ∧
      ¬ (bkg_deleteVertex (bgf2_Gf ω L) (bgf2_centre L j)).Reachable w₁ w₂ ∧
      ¬ (bkg_deleteVertex (bgf2_Gf ω L) (bgf2_centre L j)).Reachable w₁ w₃ ∧
      ¬ (bkg_deleteVertex (bgf2_Gf ω L) (bgf2_centre L j)).Reachable w₂ w₃ := by
  set c := bgf2_centre L j with hc
  obtain ⟨w₁, w₂, w₃, hn₁, hn₂, hn₃, hs₁₂, hs₁₃, hs₂₃⟩ := bgf2_trif_separation h
  have hne : ∀ w : Site 2, w ≠ 0 → w + c ≠ c := by
    intro w hw heq
    have : w + c = 0 + c := by rw [zero_add]; exact heq
    exact hw (add_right_cancel this)
  exact ⟨w₁ + c, w₂ + c, w₃ + c, hne _ hn₁, hne _ hn₂, hne _ hn₃,
    bdc_cut_transport L ω j w₁ w₂ hs₁₂,
    bdc_cut_transport L ω j w₁ w₃ hs₁₃,
    bdc_cut_transport L ω j w₂ w₃ hs₂₃⟩



theorem bdc_shiftCfg_zero (ω : ConfigSpace (Sym2 (Site 2))) : bdc_shiftCfg 0 ω = ω := by
  funext e
  simp only [bdc_shiftCfg, add_zero]
  congr 1
  refine e.ind ?_
  intro x y
  simp only [Sym2.map_pair_eq, add_zero]




theorem bdc_trif_separation_at_zero (L : ℕ) (ω : ConfigSpace (Sym2 (Site 2)))
    (h : bao_AllOpenTrif ω L) :
    ∃ w₁ w₂ w₃ : Site 2, w₁ ≠ 0 ∧ w₂ ≠ 0 ∧ w₃ ≠ 0 ∧
      ¬ (bkg_deleteVertex (bgf2_Gf ω L) 0).Reachable w₁ w₂ ∧
      ¬ (bkg_deleteVertex (bgf2_Gf ω L) 0).Reachable w₁ w₃ ∧
      ¬ (bkg_deleteVertex (bgf2_Gf ω L) 0).Reachable w₂ w₃ :=
  bgf2_trif_separation h












theorem bdc_hub_feed (L : ℕ) (ω : ConfigSpace (Sym2 (Site 2))) (j : Site 2)
    (h : bao_AllOpenTrif (bdc_shiftCfg (bgf2_centre L j) ω) L)
    {S : Finset (Site 2)} (hcS : bgf2_centre L j ∈ S)
    (hmem : ∀ w₁ w₂ w₃ : Site 2, w₁ ≠ bgf2_centre L j → w₂ ≠ bgf2_centre L j → w₃ ≠ bgf2_centre L j →
      w₁ ∈ S ∧ w₂ ∈ S ∧ w₃ ∈ S) :
    ∃ a₁ a₂ a₃ : {v // v ∈ S}, a₁ ≠ (⟨bgf2_centre L j, hcS⟩ : {v // v ∈ S}) ∧
      a₂ ≠ ⟨bgf2_centre L j, hcS⟩ ∧ a₃ ≠ ⟨bgf2_centre L j, hcS⟩ ∧
      ¬ (bkg_deleteVertex (bgf2_Gf ω L) (bgf2_centre L j)).Reachable (a₁ : Site 2) (a₂ : Site 2) ∧
      ¬ (bkg_deleteVertex (bgf2_Gf ω L) (bgf2_centre L j)).Reachable (a₁ : Site 2) (a₃ : Site 2) ∧
      ¬ (bkg_deleteVertex (bgf2_Gf ω L) (bgf2_centre L j)).Reachable (a₂ : Site 2) (a₃ : Site 2) := by
  obtain ⟨w₁, w₂, w₃, hne₁, hne₂, hne₃, hcut₁₂, hcut₁₃, hcut₂₃⟩ := bdc_trif_separation_at L ω j h
  obtain ⟨hm₁, hm₂, hm₃⟩ := hmem w₁ w₂ w₃ hne₁ hne₂ hne₃
  exact bfct_hub_cut_of_separation (G := bgf2_Gf ω L) ⟨bgf2_centre L j, hcS⟩ hm₁ hm₂ hm₃
    hne₁ hne₂ hne₃ hcut₁₂ hcut₁₃ hcut₂₃







































theorem bdc_status :
    
    (∀ L : ℕ, 1 ≤ L → ¬ (bgf2_Gf bdc_allOpenCfg L ≤ hypercubicLattice 2)) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ),
      bau_ArmSubforestData ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard 2 R) ∧
    
    (∀ (L : ℕ) (ω : ConfigSpace (Sym2 (Site 2))) (j : Site 2),
      bao_AllOpenTrif (bdc_shiftCfg (bgf2_centre L j) ω) L →
      ∃ w₁ w₂ w₃ : Site 2, w₁ ≠ bgf2_centre L j ∧ w₂ ≠ bgf2_centre L j ∧ w₃ ≠ bgf2_centre L j ∧
        ¬ (bkg_deleteVertex (bgf2_Gf ω L) (bgf2_centre L j)).Reachable w₁ w₂ ∧
        ¬ (bkg_deleteVertex (bgf2_Gf ω L) (bgf2_centre L j)).Reachable w₁ w₃ ∧
        ¬ (bkg_deleteVertex (bgf2_Gf ω L) (bgf2_centre L j)).Reachable w₂ w₃) := by
  refine ⟨fun L hL => bdc_Gf_not_le_lattice hL, ?_, ?_⟩
  · intro ω L R h; exact bdc_datum_implies_count ω L R h
  · intro L ω j h; exact bdc_trif_separation_at L ω j h


end StatMech.Walls


