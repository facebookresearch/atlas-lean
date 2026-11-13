/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





















































































import Mathlib
import Code.RSW.Defs
import Code.RSW.SelfDuality
import Code.Lattice.CrossingParity
import Code.Lattice.PlanarDual
import Code.Lattice.JordanZ2
import Code.Lattice.JordanEnclosure
import Code.Lattice.SegmentConn
import Code.Universality.DualEventSetEquality
import Code.Universality.BoxCrossingDichotomy
import Code.Universality.BoxCrossingDichotomyClose
import Code.Universality.JordanExhaustivityClose
import Code.Universality.MatchedPlanarDualityClose
import Code.Universality.RSWBxpAssembly

open Set SimpleGraph Finset MeasureTheory
open StatMech.Lattice
open StatMech.RSW.Box

namespace StatMech

namespace Universality












theorem gec2_cut_noH (n : ℤ) (hn : 1 ≤ n) :
    ¬ HorizontalCrossing des_cutConfig 0 (n + 1) 0 n := by
  rintro ⟨x, y, hxy⟩
  have hside := des_cutConfig_connectedWithin_sameSide0 hxy
  have hx0 : (x : Site 2) 0 = 0 := x.2.2
  have hy0 : (y : Site 2) 0 = n + 1 := y.2.2
  rw [hx0, hy0] at hside
  have h0 : (0 : ℤ) ≤ 0 := le_refl 0
  have : (n + 1 : ℤ) ≤ 0 := hside.mp h0
  omega





theorem gec2_cut_no_matchedFrameDualV (n : ℤ) (hn : 1 ≤ n) :
    ¬ mpd_MatchedFrameDualV des_cutConfig n :=
  mpd_corrected_box_false n hn











theorem gec2_matchedFrameDualV_false (n : ℤ) (hn : 1 ≤ n) :
    ¬ (∀ ω : ConfigSpace (Sym2 (Site 2)),
        ¬ HorizontalCrossing ω 0 (n + 1) 0 n → mpd_MatchedFrameDualV ω n) := by
  intro h
  exact gec2_cut_no_matchedFrameDualV n hn (h des_cutConfig (gec2_cut_noH n hn))














theorem gec2_rot90_rect (n : ℤ) (x : Site 2) :
    x ∈ rect 0 (n + 1) 0 n ↔ rot90Fun x ∈ rect (-n) 0 0 (n + 1) := by
  simp only [mem_rect, rot90Fun, Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor <;> intro h <;> exact ⟨by omega, by omega, by omega, by omega⟩





theorem gec2_rot90_leftSide (n : ℤ) (x : Site 2) :
    x ∈ leftSide 0 (n + 1) 0 n ↔ rot90Fun x ∈ bottomSide (-n) 0 0 (n + 1) := by
  simp only [mem_leftSide, mem_bottomSide, mem_rect, rot90Fun,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor <;> rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩ <;>
    exact ⟨⟨by omega, by omega, by omega, by omega⟩, by omega⟩




theorem gec2_rot90_rightSide (n : ℤ) (x : Site 2) :
    x ∈ rightSide 0 (n + 1) 0 n ↔ rot90Fun x ∈ topSide (-n) 0 0 (n + 1) := by
  simp only [mem_rightSide, mem_topSide, mem_rect, rot90Fun,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor <;> rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩ <;>
    exact ⟨⟨by omega, by omega, by omega, by omega⟩, by omega⟩













theorem gec2_matchedFrameDualV_iff_closedH (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) :
    mpd_MatchedFrameDualV ω n ↔ HorizontalCrossing (des_negConfig ω) 0 (n + 1) 0 n :=
  (mpd_literal_vs_honest_boxes ω n).2



















def gec2_greenSet (n : ℤ) : Set (Sym2 (Site 2)) :=
  {e | bdEdge (rect 0 (n + 1) 0 n) e}





noncomputable def gec2_greenConfig (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) :
    ConfigSpace (Sym2 (Site 2)) := by
  classical
  exact fun e => des_negConfig ω e || decide (e ∈ gec2_greenSet n)



theorem gec2_greenConfig_ge_negConfig (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) :
    des_negConfig ω ≤ gec2_greenConfig ω n := by
  intro e
  unfold gec2_greenConfig
  cases h : des_negConfig ω e <;> simp_all






def gec2_GreenMatchedFrame (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) : Prop :=
  HorizontalCrossing (gec2_greenConfig ω n) 0 (n + 1) 0 n








theorem gec2_greenMatchedFrame_of_matchedFrameDualV (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (h : mpd_MatchedFrameDualV ω n) : gec2_GreenMatchedFrame ω n := by
  rw [gec2_matchedFrameDualV_iff_closedH] at h
  obtain ⟨x, y, hxy⟩ := h
  exact ⟨x, y, StatMech.TwoDim.connectedWithin_mono (gec2_greenConfig_ge_negConfig ω n) hxy⟩














theorem gec2_negConfig_bot (e : Sym2 (Site 2)) : des_negConfig bcc_botCfg e = true := by
  rw [des_negConfig_apply]; simp [bcc_botCfg]



def gec2_negBotHom (S : Set (Site 2)) :
    ((hypercubicLattice 2).induce S) →g (openSubgraphInduce 2 (des_negConfig bcc_botCfg) S) where
  toFun := id
  map_rel' := by
    intro x y h
    rw [openSubgraphInduce_adj, openSubgraph_adj]
    rw [SimpleGraph.induce_adj] at h
    exact ⟨h, gec2_negConfig_bot _⟩




theorem gec2_negBot_horizontalCrossing (n : ℤ) (hn : 0 ≤ n) :
    HorizontalCrossing (des_negConfig bcc_botCfg) 0 (n + 1) 0 n := by
  unfold HorizontalCrossing
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : ℤ) ≤ (n + 1) - 0)
  set R := rect 0 (n + 1) 0 0 with hR
  have hlmem : (![0, 0] : Site 2) ∈ leftSide 0 (n + 1) 0 n := by
    refine ⟨?_, by simp⟩; rw [mem_rect]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    exact ⟨le_refl 0, by omega, le_refl 0, hn⟩
  have hrmem : (![n + 1, 0] : Site 2) ∈ rightSide 0 (n + 1) 0 n := by
    refine ⟨?_, by simp⟩; rw [mem_rect]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    exact ⟨by omega, le_refl _, le_refl 0, hn⟩
  have hupd : ∀ t : ℕ, Function.update (![0, 0] : Site 2) 0 ((![0, 0] : Site 2) 0 + (t : ℤ))
      = ![(t : ℤ), 0] := by
    intro t; funext i; fin_cases i <;> simp [Function.update]
  have hseg := segment_connectedWithin (d := 2) (rect 0 (n + 1) 0 n) (0 : Fin 2)
    (![0, 0] : Site 2) k
    (fun t htle => by
      rw [hupd t, mem_rect]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      exact ⟨by positivity, by omega, le_refl 0, hn⟩)
  obtain ⟨w⟩ := hseg
  have wmap := w.map (gec2_negBotHom (rect 0 (n + 1) 0 n))
  refine ⟨⟨![0, 0], hlmem⟩, ⟨![n + 1, 0], hrmem⟩, ?_⟩
  change (openSubgraphInduce 2 (des_negConfig bcc_botCfg) (rect 0 (n + 1) 0 n)).Reachable
    ⟨![0, 0], leftSide_subset hlmem⟩ ⟨![n + 1, 0], rightSide_subset hrmem⟩
  refine (wmap.copy ?_ ?_).reachable
  · apply Subtype.ext
    change Function.update (![0, 0] : Site 2) 0 ((![0, 0] : Site 2) 0 + (0 : ℤ)) = ![0, 0]
    funext i; fin_cases i <;> simp [Function.update]
  · apply Subtype.ext
    change Function.update (![0, 0] : Site 2) 0 ((![0, 0] : Site 2) 0 + ((k : ℕ) : ℤ)) = ![n + 1, 0]
    have hck : (![0, 0] : Site 2) 0 + ((k : ℕ) : ℤ) = n + 1 := by
      simp only [Matrix.cons_val_zero]; omega
    rw [hck]; funext i; fin_cases i <;> simp [Function.update]






theorem gec2_greenMatchedFrame_nonvacuous (n : ℤ) (hn : 0 ≤ n) :
    ¬ HorizontalCrossing bcc_botCfg 0 (n + 1) 0 n ∧ gec2_GreenMatchedFrame bcc_botCfg n := by
  refine ⟨mpd_botCfg_noH n hn, ?_⟩
  obtain ⟨x, y, hxy⟩ := gec2_negBot_horizontalCrossing n hn
  exact ⟨x, y, StatMech.TwoDim.connectedWithin_mono
    (gec2_greenConfig_ge_negConfig bcc_botCfg n) hxy⟩








theorem gec2_cut_stub_bottom (n b : ℤ) (h0 : 0 ≤ b) (hbn : b ≤ n) :
    dualConfig des_cutConfig s(![-b, 0], ![-b, 1]) = true ∧
      (![-b, 0] : Site 2) ∈ bottomSide (-n) 0 0 (n + 1) := by
  refine ⟨?_, ?_⟩
  · rw [dual_isOpen_iff_isClosed]
    have hce : (crossEdge.symm s((![-b, 0] : Site 2), ![-b, 1]))
        = s(rot90Inv ![-b, 0], rot90Inv ![-b, 1]) := by
      change (sym2Congr rot90Equiv).symm s(_, _) = _
      rw [sym2Congr]; simp [Sym2.map_mk]
    rw [hce]
    have e1 : rot90Inv (![-b, 0] : Site 2) = ![0, b] := by funext i; fin_cases i <;> simp [rot90Inv]
    have e2 : rot90Inv (![-b, 1] : Site 2) = ![1, b] := by funext i; fin_cases i <;> simp [rot90Inv]
    rw [e1, e2]
    exact des_cutConfig_cut_closed b
  · refine ⟨?_, by simp⟩
    rw [mem_rect]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    exact ⟨by omega, by omega, le_refl 0, by omega⟩







theorem gec2_face_dualCircuit (ω : ConfigSpace (Sym2 (Site 2)))
    {n : ℤ} (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 (n + 1) 0 n) :
    ∃ (u : Site 2) (c : (faceBoundaryGraph (mpd_leftReach ω n)).Walk u u), c.IsCycle :=
  mpd_exists_dualCircuit ω hn hnoH











def gec2_GreenJordan (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) : Prop :=
  gec2_GreenMatchedFrame ω n






theorem gec2_dichotomy_of_greenJordan (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (_hnoH : ¬ HorizontalCrossing ω 0 (n + 1) 0 n) (h : gec2_GreenJordan ω n) :
    HorizontalCrossing ω 0 (n + 1) 0 n ∨ gec2_GreenMatchedFrame ω n :=
  Or.inr h







theorem gec2_greenJordan_of_matchedFrameDualV (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (h : mpd_MatchedFrameDualV ω n) : gec2_GreenJordan ω n :=
  gec2_greenMatchedFrame_of_matchedFrameDualV ω n h






















def gec2_GreenDichotomy (n : ℤ) : Prop :=
  (horizontalCrossingEvent 0 (n + 1) 0 n)ᶜ ⊆ dualVerticalCrossingEvent (-n) 0 0 (n + 1)















theorem gec2_matched_half_of_greenDichotomy (n : ℤ)
    (hmeasH : MeasurableSet (horizontalCrossingEvent 0 (n + 1) 0 n))
    (hmeasV : MeasurableSet (verticalCrossingEvent (-n) 0 0 (n + 1)))
    (hgreen : gec2_GreenDichotomy n)
    (hsym : rba_selfDualMeasure.real (verticalCrossingEvent (-n) 0 0 (n + 1))
              = rba_selfDualMeasure.real (horizontalCrossingEvent 0 (n + 1) 0 n)) :
    (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (horizontalCrossingEvent 0 (n + 1) 0 n) := by
  have hselfDual : rba_selfDualMeasure.real (dualVerticalCrossingEvent (-n) 0 0 (n + 1))
      = rba_selfDualMeasure.real (horizontalCrossingEvent 0 (n + 1) 0 n) := by
    rw [rba_dualVerticalCrossing_eq (-n) 0 0 (n + 1) hmeasV, hsym]
  have hcompl : rba_selfDualMeasure.real (horizontalCrossingEvent 0 (n + 1) 0 n)ᶜ
      = 1 - rba_selfDualMeasure.real (horizontalCrossingEvent 0 (n + 1) 0 n) := by
    rw [measureReal_compl hmeasH, probReal_univ]
  have hmono : rba_selfDualMeasure.real (horizontalCrossingEvent 0 (n + 1) 0 n)ᶜ
      ≤ rba_selfDualMeasure.real (dualVerticalCrossingEvent (-n) 0 0 (n + 1)) :=
    measureReal_mono hgreen
  rw [hselfDual, hcompl] at hmono
  linarith







theorem gec2_greenDichotomy_iff (n : ℤ) :
    gec2_GreenDichotomy n ↔
      ∀ ω : ConfigSpace (Sym2 (Site 2)),
        ¬ HorizontalCrossing ω 0 (n + 1) 0 n → mpd_MatchedFrameDualV ω n := by
  unfold gec2_GreenDichotomy mpd_MatchedFrameDualV
  constructor
  · intro h ω hω
    have : ω ∈ (horizontalCrossingEvent 0 (n + 1) 0 n)ᶜ := by
      simp only [Set.mem_compl_iff, mem_horizontalCrossingEvent]; exact hω
    exact (mem_dualVerticalCrossingEvent).mp (h this)
  · intro h ω hω
    simp only [Set.mem_compl_iff, mem_horizontalCrossingEvent] at hω
    exact (mem_dualVerticalCrossingEvent).mpr (h ω hω)







theorem gec2_greenDichotomy_false (n : ℤ) (hn : 1 ≤ n) : ¬ gec2_GreenDichotomy n := by
  rw [gec2_greenDichotomy_iff]
  exact gec2_matchedFrameDualV_false n hn

end Universality

end StatMech
