/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




































































import Mathlib
import Code.Walls.belexpleaf
import Code.Walls.bc61coarsebox
import Code.Walls.bc60upperlines

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





theorem bfk_leafClause_of_openEdgeInj {W : Type} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] (F : Finset (Sym2 (Site d)))
    (ω : ConfigSpace (Sym2 (Site d))) (edgeOf : W → Sym2 (Site d))
    (hmem : ∀ v, G.degree v = 1 → edgeOf v ∈ F)
    (hopen : ∀ v, G.degree v = 1 → ω (edgeOf v) = true)
    (hinj : Set.InjOn edgeOf {v | G.degree v = 1}) :
    (univ.filter (fun v => G.degree v = 1)).card ≤ bel_leafOpenCount F ω := by
  classical
  set Lv := univ.filter (fun v => G.degree v = 1) with hLv
  have hinjOn : Set.InjOn edgeOf Lv := by
    intro x hx y hy hxy
    rw [Finset.mem_coe, hLv, Finset.mem_filter] at hx hy
    exact hinj hx.2 hy.2 hxy
  have himg : Lv.image edgeOf ⊆ F.filter (fun e => ω e = true) := by
    intro e he
    rw [Finset.mem_image] at he
    obtain ⟨v, hv, rfl⟩ := he
    rw [hLv, Finset.mem_filter] at hv
    rw [Finset.mem_filter]
    exact ⟨hmem v hv.2, hopen v hv.2⟩
  calc Lv.card = (Lv.image edgeOf).card := (Finset.card_image_of_injOn hinjOn).symm
    _ ≤ (F.filter (fun e => ω e = true)).card := Finset.card_le_card himg
    _ = bel_leafOpenCount F ω := rfl










theorem bfk_pt_outside {L : ℕ} {m h₀ c H : ℤ} (hc : (L : ℤ) < c - m) :
    bc57_pt c H ∉ bc61_boxAround 2 L (bc57_pt m h₀) := by
  rw [bc61_mem_boxAround, mem_box]
  simp only [not_forall, not_le]
  refine ⟨0, ?_⟩
  simp only [Pi.sub_apply, bc57_pt_fst]
  omega




theorem bfk_rightArm_reach {L : ℕ} {m h₀ H : ℤ} (hH : 1 ≤ H) (j : ℕ) :
    Connected 2 (removeSites (bc61_boxAround 2 L (bc57_pt m h₀)) bc60_upperLines)
      (bc57_pt (m + (L : ℤ) + 1) H) (bc57_pt (m + (L : ℤ) + 1 + (j : ℤ)) H) := by
  induction j with
  | zero => simpa using connected_refl _ (bc57_pt (m + (L : ℤ) + 1) H)
  | succ i ih =>
    have hstep : Connected 2 (removeSites (bc61_boxAround 2 L (bc57_pt m h₀)) bc60_upperLines)
        (bc57_pt (m + (L : ℤ) + 1 + (i : ℤ)) H) (bc57_pt (m + (L : ℤ) + 1 + (i : ℤ) + 1) H) :=
      bc61_cut_adj_connected (bc57_pt_adj _ H) (bc60_open _ hH)
        (bfk_pt_outside (m := m) (h₀ := h₀) (c := m + (L : ℤ) + 1 + (i : ℤ)) (H := H)
          (by omega))
        (bfk_pt_outside (m := m) (h₀ := h₀) (c := m + (L : ℤ) + 1 + (i : ℤ) + 1) (H := H)
          (by omega))
    have hcast : (m + (L : ℤ) + 1 + ((i + 1 : ℕ) : ℤ)) = m + (L : ℤ) + 1 + (i : ℤ) + 1 := by
      push_cast; ring
    rw [hcast]; exact ih.trans hstep


theorem bfk_rightArm_infinite {L : ℕ} {m h₀ H : ℤ} (hH : 1 ≤ H) :
    (cluster 2 (removeSites (bc61_boxAround 2 L (bc57_pt m h₀)) bc60_upperLines)
      (bc57_pt (m + (L : ℤ) + 1) H)).Infinite := by
  rw [cluster_infinite_iff]
  intro n
  refine ⟨bc57_pt (m + (L : ℤ) + 1 + ((n : ℤ) + (m + (L : ℤ) + 1).natAbs + 1)) H, ?_, ?_⟩
  · rw [mem_box]; simp only [not_forall, not_le]; refine ⟨0, ?_⟩
    rw [bc57_pt_fst]; omega
  · have hstep := bfk_rightArm_reach (L := L) (m := m) (h₀ := h₀) (H := H) hH
      ((n : ℤ) + (m + (L : ℤ) + 1).natAbs + 1).toNat
    have hcast : (((n : ℤ) + (m + (L : ℤ) + 1).natAbs + 1).toNat : ℤ)
        = (n : ℤ) + (m + (L : ℤ) + 1).natAbs + 1 := by
      rw [Int.toNat_of_nonneg (by positivity)]
    rw [hcast] at hstep
    exact hstep




theorem bfk_arm_disconnected {L : ℕ} {m h₀ c H H' : ℤ} (hne : H ≠ H') :
    ¬ Connected 2 (removeSites (bc61_boxAround 2 L (bc57_pt m h₀)) bc60_upperLines)
      (bc57_pt c H) (bc57_pt c H') := by
  intro hconn
  have hω : Connected 2 bc60_upperLines (bc57_pt c H) (bc57_pt c H') :=
    bc61_connected_of_cut hconn
  have hht : (bc57_pt c H') 1 = H := bc60_height_invariant (by rw [bc57_pt_snd]) hω
  rw [bc57_pt_snd] at hht
  exact hne hht.symm




theorem bfk_arm_boxAdjacent {L : ℕ} {m h₀ H : ℤ} (hH : 1 ≤ H)
    (hHlo : h₀ - (L : ℤ) ≤ H) (hHhi : H ≤ h₀ + (L : ℤ)) :
    ∃ b ∈ bc61_boxAround 2 L (bc57_pt m h₀),
      (openSubgraph 2 bc60_upperLines).Adj b (bc57_pt (m + (L : ℤ) + 1) H) := by
  refine ⟨bc57_pt (m + (L : ℤ)) H, ?_, ?_⟩
  · rw [bc61_mem_boxAround, mem_box]
    intro i; fin_cases i
    · show ((bc57_pt (m + (L : ℤ)) H - bc57_pt m h₀) 0).natAbs ≤ L
      simp only [Pi.sub_apply, bc57_pt_fst]; omega
    · show ((bc57_pt (m + (L : ℤ)) H - bc57_pt m h₀) 1).natAbs ≤ L
      simp only [Pi.sub_apply, bc57_pt_snd]; omega
  · rw [openSubgraph_adj]
    exact ⟨bc57_pt_adj (m + (L : ℤ)) H, bc60_open (m + (L : ℤ)) hH⟩






theorem bfk_isCoarseTrif {L : ℕ} (hL : 3 ≤ L) {m h₀ : ℤ} (hh₀ : 0 ≤ h₀) :
    bc61_IsCoarseTrifurcation bc60_upperLines L (bc57_pt m h₀) := by
  refine ⟨bc57_pt (m + (L : ℤ) + 1) (h₀ + 1), bc57_pt (m + (L : ℤ) + 1) (h₀ + 2),
    bc57_pt (m + (L : ℤ) + 1) (h₀ + 3), ?_, ?_, ?_, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · exact bfk_arm_boxAdjacent (by omega) (by omega) (by omega)
  · exact bfk_arm_boxAdjacent (by omega) (by omega) (by omega)
  · exact bfk_arm_boxAdjacent (by omega) (by omega) (by omega)
  · exact bfk_rightArm_infinite (by omega)
  · exact bfk_rightArm_infinite (by omega)
  · exact bfk_rightArm_infinite (by omega)
  · exact bfk_arm_disconnected (by omega)
  · exact bfk_arm_disconnected (by omega)
  · exact bfk_arm_disconnected (by omega)









theorem bfk_coarseTcount_lower {L : ℕ} (hL : 3 ≤ L) (R : ℕ) :
    (R + 1) * (2 * R + 1) ≤ bc61_coarseTcount bc60_upperLines L R := by
  classical
  set P : Finset (ℤ × ℤ) := (Finset.Icc (-(R : ℤ)) (R : ℤ)) ×ˢ (Finset.Icc (0 : ℤ) (R : ℤ)) with hP
  set S : Finset (Site 2) := P.image (fun p => bc57_pt p.1 p.2) with hS
  have hinj : Set.InjOn (fun p : ℤ × ℤ => bc57_pt p.1 p.2) P := by
    intro p _ q _ hpq
    have h0 := congrArg (fun f => f 0) hpq
    have h1 := congrArg (fun f => f 1) hpq
    simp only [bc57_pt_fst, bc57_pt_snd] at h0 h1
    exact Prod.ext h0 h1
  have hIcc1 : (Finset.Icc (-(R : ℤ)) (R : ℤ)).card = 2 * R + 1 := by rw [Int.card_Icc]; omega
  have hIcc2 : (Finset.Icc (0 : ℤ) (R : ℤ)).card = R + 1 := by rw [Int.card_Icc]; omega
  have hcard : S.card = (2 * R + 1) * (R + 1) := by
    rw [hS, Finset.card_image_of_injOn hinj, hP, Finset.card_product, hIcc1, hIcc2]
  have hSsub : S ⊆ bc61_coarseTrifFinset bc60_upperLines L R := by
    intro x hx
    rw [hS, Finset.mem_image] at hx
    obtain ⟨⟨m, h⟩, hmh, rfl⟩ := hx
    rw [hP, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hmh
    obtain ⟨⟨hm1, hm2⟩, ⟨hh1, hh2⟩⟩ := hmh
    rw [bc61_mem_coarseTrifFinset]
    refine ⟨?_, bfk_isCoarseTrif hL hh1⟩
    rw [mem_box]; intro i; fin_cases i
    · show ((bc57_pt m h) 0).natAbs ≤ R; rw [bc57_pt_fst]; omega
    · show ((bc57_pt m h) 1).natAbs ≤ R; rw [bc57_pt_snd]; omega
  calc (R + 1) * (2 * R + 1) = S.card := by rw [hcard]; ring
    _ ≤ (bc61_coarseTrifFinset bc60_upperLines L R).card := Finset.card_le_card hSsub
    _ = bc61_coarseTcount bc60_upperLines L R := rfl



theorem bfk_boxCard_le (R : ℕ) : (boxFinsetBK 2 R).card ≤ (2 * R + 1) * (2 * R + 1) := by
  classical
  set Q : Finset (ℤ × ℤ) := (Finset.Icc (-(R : ℤ)) (R : ℤ)) ×ˢ (Finset.Icc (-(R : ℤ)) (R : ℤ))
    with hQ
  set T : Finset (Site 2) := Q.image (fun p => bc57_pt p.1 p.2) with hT
  have hsub : boxFinsetBK 2 R ⊆ T := by
    intro x hx
    rw [boxFinsetBK, Set.Finite.mem_toFinset, mem_box] at hx
    rw [hT, Finset.mem_image]
    refine ⟨(x 0, x 1), ?_, ?_⟩
    · rw [hQ, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      · have := hx 0; omega
      · have := hx 0; omega
      · have := hx 1; omega
      · have := hx 1; omega
    · funext i; fin_cases i <;> simp [bc57_pt]
  have hIcc : (Finset.Icc (-(R : ℤ)) (R : ℤ)).card = 2 * R + 1 := by rw [Int.card_Icc]; omega
  calc (boxFinsetBK 2 R).card ≤ T.card := Finset.card_le_card hsub
    _ ≤ Q.card := Finset.card_image_le
    _ = (2 * R + 1) * (2 * R + 1) := by rw [hQ, Finset.card_product, hIcc]
















theorem bfk_perConfigForest_false {L : ℕ} (hL : 3 ≤ L)
    (F : ℕ → Finset (Sym2 (Site 2)))
    (hdens : Filter.Tendsto
      (fun R => ((F R).card : ℝ) / ((boxFinsetBK 2 R).card : ℝ)) Filter.atTop (nhds 0)) :
    ¬ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (R : ℕ),
        bpe_CoarseForestNoBnd ω L R (bel_leafOpenCount (F R) ω)) := by
  intro hforest
  
  have hFlb : ∀ R, (R + 1) * (2 * R + 1) ≤ (F R).card := by
    intro R
    have h1 : bc61_coarseTcount bc60_upperLines L R ≤ bel_leafOpenCount (F R) bc60_upperLines :=
      bpe_coarseTcount_le_leafCard bc60_upperLines L R
        (bel_leafOpenCount (F R) bc60_upperLines) (hforest bc60_upperLines R)
    have h2 : bel_leafOpenCount (F R) bc60_upperLines ≤ (F R).card :=
      Finset.card_filter_le _ _
    have h3 : (R + 1) * (2 * R + 1) ≤ bc61_coarseTcount bc60_upperLines L R :=
      bfk_coarseTcount_lower hL R
    calc (R + 1) * (2 * R + 1) ≤ bc61_coarseTcount bc60_upperLines L R := h3
      _ ≤ bel_leafOpenCount (F R) bc60_upperLines := h1
      _ ≤ (F R).card := h2
  
  have hbox : ∀ R, (boxFinsetBK 2 R).card ≤ 2 * (F R).card := by
    intro R
    have hb := bfk_boxCard_le R
    have hf := hFlb R
    have hmid : (2 * R + 1) * (2 * R + 1) ≤ 2 * ((R + 1) * (2 * R + 1)) := by nlinarith
    calc (boxFinsetBK 2 R).card ≤ (2 * R + 1) * (2 * R + 1) := hb
      _ ≤ 2 * ((R + 1) * (2 * R + 1)) := hmid
      _ ≤ 2 * (F R).card := by omega
  
  have hratio : ∀ R, (1 : ℝ) / 2 ≤ ((F R).card : ℝ) / ((boxFinsetBK 2 R).card : ℝ) := by
    intro R
    have hpos : (0 : ℝ) < ((boxFinsetBK 2 R).card : ℝ) := by
      exact_mod_cast bkc_boxFinsetBK_card_pos 2 R
    rw [le_div_iff₀ hpos]
    have hcast : ((boxFinsetBK 2 R).card : ℝ) ≤ 2 * ((F R).card : ℝ) := by exact_mod_cast hbox R
    linarith
  
  have hle : (1 : ℝ) / 2 ≤ 0 := ge_of_tendsto' hdens hratio
  linarith





























theorem bfk_status {L : ℕ} (hL : 3 ≤ L) :
    
    (∀ {W : Type} [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj]
        (F : Finset (Sym2 (Site 2))) (ω : ConfigSpace (Sym2 (Site 2))) (edgeOf : W → Sym2 (Site 2)),
      (∀ v, G.degree v = 1 → edgeOf v ∈ F) → (∀ v, G.degree v = 1 → ω (edgeOf v) = true) →
      Set.InjOn edgeOf {v | G.degree v = 1} →
      (univ.filter (fun v => G.degree v = 1)).card ≤ bel_leafOpenCount F ω) ∧
    
    (∀ (m h₀ : ℤ), 0 ≤ h₀ → bc61_IsCoarseTrifurcation bc60_upperLines L (bc57_pt m h₀)) ∧
    
    (∀ R, (R + 1) * (2 * R + 1) ≤ bc61_coarseTcount bc60_upperLines L R) ∧
    
    (∀ (F : ℕ → Finset (Sym2 (Site 2))),
      Filter.Tendsto (fun R => ((F R).card : ℝ) / ((boxFinsetBK 2 R).card : ℝ))
        Filter.atTop (nhds 0) →
      ¬ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (R : ℕ),
          bpe_CoarseForestNoBnd ω L R (bel_leafOpenCount (F R) ω))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro W _ _ G _ F ω edgeOf hmem hopen hinj
    exact bfk_leafClause_of_openEdgeInj G F ω edgeOf hmem hopen hinj
  · intro m h₀ hh₀; exact bfk_isCoarseTrif hL hh₀
  · intro R; exact bfk_coarseTcount_lower hL R
  · intro F hdens; exact bfk_perConfigForest_false hL F hdens

end StatMech.Walls
