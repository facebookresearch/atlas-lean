/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





































import Mathlib
import Code.Walls.bscsupercut
import Code.Walls.bfcfaithful
import Code.Walls.bgnglobalcontract

open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000

namespace StatMech.Walls












def bao_AllOpenTrif (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ) : Prop :=
  bc67_IsGnTrifurcation ω L (0 : Site 2) ∧ bff_BoxAllOpen ω L



theorem bao_allOpenTrif_imp_bc67 {ω : ConfigSpace (Sym2 (Site 2))} {L : ℕ}
    (h : bao_AllOpenTrif ω L) : bc67_IsGnTrifurcation ω L (0 : Site 2) :=
  h.1










theorem bao_box_internallyConnected {ω : ConfigSpace (Sym2 (Site 2))} {L : ℕ}
    (h : bao_AllOpenTrif ω L) {x y : Site 2}
    (hx : x ∈ Lattice.box 2 L) (hy : y ∈ Lattice.box 2 L) :
    Lattice.Connected 2 ω x y :=
  bff_allOpen_box_connected h.2 hx hy

#check @bao_AllOpenTrif
#check @bao_allOpenTrif_imp_bc67
#check @bao_box_internallyConnected










theorem bao_boxEdges_fst {n : ℕ} {x y : Site 2} (h : s(x, y) ∈ boxEdges 2 n) :
    x ∈ Lattice.box 2 n := by
  simp only [boxEdges, Finset.mem_image, Finset.mem_filter, Finset.mem_product,
    boxFinsetBK, Set.Finite.mem_toFinset] at h
  obtain ⟨p, ⟨⟨hp1, hp2⟩, _⟩, hpe⟩ := h
  rw [Sym2.eq_iff] at hpe
  rcases hpe with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [← h1]; exact hp1
  · rw [← h2]; exact hp2



noncomputable def bao_onlyBox0 (L : ℕ) : ConfigSpace (Sym2 (Site 2)) :=
  fun e => if e ∈ boxEdges 2 L then true else false


theorem bao_onlyBox0_allOpen (L : ℕ) : bff_BoxAllOpen (bao_onlyBox0 L) L := by
  intro e he
  unfold bao_onlyBox0
  rw [if_pos he]


theorem bao_bgn_idx_box10 {L : ℕ} (hL : 1 ≤ L) (h : ℤ) (hh0 : 0 ≤ h) (hhL : h ≤ (L : ℤ)) :
    bgn_idx L (bc57_pt (2 * (L : ℤ) + 1) h) = bc57_pt 1 0 := by
  funext i
  fin_cases i
  · show (((bc57_pt (2 * (L : ℤ) + 1) h) 0) + L) / (2 * (L : ℤ) + 1) = (bc57_pt 1 0) 0
    rw [bc57_pt_fst, bc57_pt_fst]
    have hb : (2 * (L : ℤ) + 1) ≠ 0 := by positivity
    have hrw : (2 * (L : ℤ) + 1) + L = (L : ℤ) + 1 * (2 * (L : ℤ) + 1) := by ring
    rw [hrw, Int.add_mul_ediv_right _ _ hb, Int.ediv_eq_zero_of_lt (by positivity) (by omega)]
    norm_num
  · show (((bc57_pt (2 * (L : ℤ) + 1) h) 1) + L) / (2 * (L : ℤ) + 1) = (bc57_pt 1 0) 1
    rw [bc57_pt_snd, bc57_pt_snd]
    exact Int.ediv_eq_zero_of_lt (by omega) (by omega)


theorem bao_bgn_idx_zero (L : ℕ) : bgn_idx L (0 : Site 2) = 0 := by
  funext i
  show ((0 : Site 2) i + (L : ℤ)) / (2 * (L : ℤ) + 1) = (0 : Site 2) i
  simp only [Pi.zero_apply, zero_add]
  exact Int.ediv_eq_zero_of_lt (by positivity) (by omega)



theorem bao_u_isolated {L : ℕ} (hL : 1 ≤ L) (w : Site 2) :
    ¬ (openSubgraph 2 (removeSites (bc61_boxAround 2 L 0) (bao_onlyBox0 L))).Adj
        (bc57_pt (2 * (L : ℤ) + 1) 0) w := by
  intro hadj
  have hopen : removeSites (bc61_boxAround 2 L 0) (bao_onlyBox0 L)
      s(bc57_pt (2 * (L : ℤ) + 1) 0, w) = true := hadj.2
  have hle := daep_removeSites_le (bc61_boxAround 2 L 0) (bao_onlyBox0 L)
      s(bc57_pt (2 * (L : ℤ) + 1) 0, w)
  rw [hopen] at hle
  have hcfg : bao_onlyBox0 L s(bc57_pt (2 * (L : ℤ) + 1) 0, w) = true := by
    revert hle; cases bao_onlyBox0 L s(bc57_pt (2 * (L : ℤ) + 1) 0, w) <;> simp
  unfold bao_onlyBox0 at hcfg
  by_cases hmem : s(bc57_pt (2 * (L : ℤ) + 1) 0, w) ∈ boxEdges 2 L
  · have hbox := bao_boxEdges_fst hmem
    have hn := (Lattice.mem_box).mp hbox 0
    rw [bc57_pt_fst] at hn
    omega
  · rw [if_neg hmem] at hcfg; exact absurd hcfg (by simp)


theorem bao_cut_singleton {L : ℕ} (hL : 1 ≤ L) {z : Site 2}
    (h : Connected 2 (removeSites (bc61_boxAround 2 L 0) (bao_onlyBox0 L))
      (bc57_pt (2 * (L : ℤ) + 1) 0) z) :
    z = bc57_pt (2 * (L : ℤ) + 1) 0 := by
  obtain ⟨p⟩ := h
  cases p with
  | nil => rfl
  | cons hadj _ => exact absurd hadj (bao_u_isolated hL _)







theorem bao_allOpen_not_frees_bridge {L : ℕ} (hL : 1 ≤ L) :
    bff_BoxAllOpen (bao_onlyBox0 L) L ∧
      ¬ bsc_BoxesInternallyConnected (bao_onlyBox0 L) L (0 : Site 2) := by
  refine ⟨bao_onlyBox0_allOpen L, ?_⟩
  intro H
  
  have hidx_u : bgn_idx L (bc57_pt (2 * (L : ℤ) + 1) 0) = bc57_pt 1 0 :=
    bao_bgn_idx_box10 hL 0 (le_refl 0) (by positivity)
  have hidx_v : bgn_idx L (bc57_pt (2 * (L : ℤ) + 1) 1) = bc57_pt 1 0 :=
    bao_bgn_idx_box10 hL 1 (by norm_num) (by exact_mod_cast hL)
  have hidx_eq : bgn_idx L (bc57_pt (2 * (L : ℤ) + 1) 0)
      = bgn_idx L (bc57_pt (2 * (L : ℤ) + 1) 1) := by rw [hidx_u, hidx_v]
  have hne : bgn_idx L (bc57_pt (2 * (L : ℤ) + 1) 0) ≠ bgn_idx L (0 : Site 2) := by
    rw [hidx_u, bao_bgn_idx_zero]
    intro hc
    have := congrFun hc 0
    rw [bc57_pt_fst] at this
    exact one_ne_zero this
  have hconn := H (bc57_pt (2 * (L : ℤ) + 1) 0) (bc57_pt (2 * (L : ℤ) + 1) 1) hidx_eq hne
  have heq := bao_cut_singleton hL hconn
  
  have := congrFun heq 1
  rw [bc57_pt_snd, bc57_pt_snd] at this
  exact one_ne_zero this

#check @bao_allOpen_not_frees_bridge










theorem bao_bk_of_forest (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hdata : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bkg_ClassicalForestData ω L R) :
    bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 :=
  bgn_bk_of_forest p hp1 hp0 hdata

































theorem bao_status {L : ℕ} (hL : 1 ≤ L) :
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))), bao_AllOpenTrif ω L →
      bc67_IsGnTrifurcation ω L (0 : Site 2)) ∧
    
    (bff_BoxAllOpen (bao_onlyBox0 L) L ∧
      ¬ bsc_BoxesInternallyConnected (bao_onlyBox0 L) L (0 : Site 2)) ∧
    
    (∀ (p : ℝ≥0) (hp1 : p ≤ 1), 0 < p →
      (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bkg_ClassicalForestData ω L R) →
      bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0) :=
  ⟨fun ω h => bao_allOpenTrif_imp_bc67 h,
   bao_allOpen_not_frees_bridge hL,
   fun p hp1 hp0 hdata => bao_bk_of_forest p hp1 hp0 hdata⟩

#check @bao_status

end StatMech.Walls


#print axioms StatMech.Walls.bao_allOpenTrif_imp_bc67
#print axioms StatMech.Walls.bao_box_internallyConnected
#print axioms StatMech.Walls.bao_allOpen_not_frees_bridge
#print axioms StatMech.Walls.bao_bk_of_forest
#print axioms StatMech.Walls.bao_status
