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
import Code.Universality.GreenEdgesClosureClose

open Set SimpleGraph Finset MeasureTheory
open StatMech.Lattice
open StatMech.RSW.Box

namespace StatMech

namespace Universality













theorem gst_greenConfig_eq_negConfig_in_box (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    {x y : Site 2} (hx : x ∈ rect 0 (n + 1) 0 n) (hy : y ∈ rect 0 (n + 1) 0 n) :
    gec2_greenConfig ω n s(x, y) = des_negConfig ω s(x, y) := by
  unfold gec2_greenConfig
  have hnot : s(x, y) ∉ gec2_greenSet n := by
    unfold gec2_greenSet
    simp only [Set.mem_setOf_eq, bdEdge_mk]
    intro h; exact (h.mp hx) hy
  simp [hnot]





def gst_greenToNegHom (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) :
    (openSubgraphInduce 2 (gec2_greenConfig ω n) (rect 0 (n + 1) 0 n)) →g
      (openSubgraphInduce 2 (des_negConfig ω) (rect 0 (n + 1) 0 n)) where
  toFun := id
  map_rel' := by
    intro x y h
    rw [openSubgraphInduce_adj, openSubgraph_adj] at h ⊢
    obtain ⟨hadj, hopen⟩ := h
    exact ⟨hadj, by rwa [gst_greenConfig_eq_negConfig_in_box ω n x.2 y.2] at hopen⟩










theorem gst_greenMatchedFrame_iff_matchedFrameDualV (ω : ConfigSpace (Sym2 (Site 2)))
    (n : ℤ) : gec2_GreenMatchedFrame ω n ↔ mpd_MatchedFrameDualV ω n := by
  rw [gec2_matchedFrameDualV_iff_closedH]
  constructor
  · rintro ⟨x, y, hxy⟩
    exact ⟨x, y, hxy.map (gst_greenToNegHom ω n)⟩
  · intro h
    exact gec2_greenMatchedFrame_of_matchedFrameDualV ω n
      ((gec2_matchedFrameDualV_iff_closedH ω n).mpr h)








theorem gst_greenJordan_false (n : ℤ) (hn : 1 ≤ n) :
    ¬ gec2_GreenJordan des_cutConfig n := by
  rw [gec2_GreenJordan, gst_greenMatchedFrame_iff_matchedFrameDualV]
  exact gec2_cut_no_matchedFrameDualV n hn














def gst_greenSet (n : ℤ) : Set (Sym2 (Site 2)) :=
  {e | ∃ x y : Site 2, e = s(x, y) ∧ x ∈ rect (-n) 0 0 (n + 1) ∧ y ∈ rect (-n) 0 0 (n + 1) ∧
    ((x 1 = 0 ∧ y 1 = 0) ∨ (x 1 = n + 1 ∧ y 1 = n + 1))}



noncomputable def gst_greenDualConfig (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) :
    ConfigSpace (Sym2 (Site 2)) := by
  classical
  exact fun e => if e ∈ gst_greenSet n then true else dualConfig ω e

theorem gst_greenDualConfig_open_iff (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (e : Sym2 (Site 2)) :
    gst_greenDualConfig ω n e = true ↔ e ∈ gst_greenSet n ∨ dualConfig ω e = true := by
  classical
  unfold gst_greenDualConfig
  by_cases h : e ∈ gst_greenSet n <;> simp [h]


theorem gst_greenDualConfig_ge (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) :
    dualConfig ω ≤ gst_greenDualConfig ω n := by
  intro e
  cases h : dualConfig ω e
  · simp
  · rw [(gst_greenDualConfig_open_iff ω n e).mpr (Or.inr h)]




def gst_GreenDualV (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) : Prop :=
  VerticalCrossing (gst_greenDualConfig ω n) (-n) 0 0 (n + 1)






theorem gst_greenDualV_of_matchedFrameDualV (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (h : mpd_MatchedFrameDualV ω n) : gst_GreenDualV ω n := by
  obtain ⟨x, y, hxy⟩ := h
  exact ⟨x, y, StatMech.TwoDim.connectedWithin_mono (gst_greenDualConfig_ge ω n) hxy⟩






theorem gst_nonvacuous (n : ℤ) (hn : 0 ≤ n) :
    ¬ HorizontalCrossing bcc_botCfg 0 (n + 1) 0 n ∧ gst_GreenDualV bcc_botCfg n := by
  refine ⟨mpd_botCfg_noH n hn, ?_⟩
  obtain ⟨x, y, hxy⟩ := mpd_botCfg_dualV_col (-n) 0 0 (n + 1) 0 ⟨by omega, le_refl 0⟩ (by omega)
  exact ⟨x, y, StatMech.TwoDim.connectedWithin_mono (gst_greenDualConfig_ge bcc_botCfg n) hxy⟩














theorem gst_cutEdge_open_invariant (n : ℤ) {u v : Site 2}
    (h : IsOpenEdge 2 (gst_greenDualConfig des_cutConfig n) u v) :
    (u 1 ≤ 1 ∧ v 1 ≤ 1) ∨ (u 1 = n + 1 ∧ v 1 = n + 1) := by
  obtain ⟨hadj, hopen⟩ := h
  rw [gst_greenDualConfig_open_iff] at hopen
  rcases hopen with hg | hd
  · obtain ⟨x, y, hexy, _, _, hcase⟩ := hg
    rw [Sym2.eq_iff] at hexy
    rcases hexy with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> subst hx <;> subst hy <;>
      rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; omega
    · right; exact ⟨h1, h2⟩
    · left; omega
    · right; exact ⟨h2, h1⟩
  · left; exact mpd_dualCut_snd_le ⟨hadj, hd⟩




theorem gst_cut_walk_le_one (n : ℤ) (hn : 1 ≤ n) {S : Set (Site 2)} {x y : S}
    (h : ConnectedWithin 2 (gst_greenDualConfig des_cutConfig n) S x y)
    (hx : (x : Site 2) 1 ≤ 1) : (y : Site 2) 1 ≤ 1 := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact hx
  | @cons a b c hab _ ih =>
    rw [openSubgraphInduce_adj, openSubgraph_adj] at hab
    apply ih
    rcases gst_cutEdge_open_invariant n hab with ⟨_, hb⟩ | ⟨ha, _⟩
    · exact hb
    · omega








theorem gst_cut_fails (n : ℤ) (hn : 1 ≤ n) : ¬ gst_GreenDualV des_cutConfig n := by
  rintro ⟨x, y, hxy⟩
  have hx1 : ((⟨(x : Site 2), bottomSide_subset x.2⟩ : rect (-n) 0 0 (n + 1)) : Site 2) 1 ≤ 1 := by
    change (x : Site 2) 1 ≤ 1; rw [x.2.2]; norm_num
  have hy1 := gst_cut_walk_le_one n hn hxy hx1
  have : (y : Site 2) 1 ≤ 1 := hy1
  rw [y.2.2] at this; omega












def gst_fullWireSet (n : ℤ) : Set (Sym2 (Site 2)) :=
  {e | ∃ x y : Site 2, e = s(x, y) ∧ x ∈ rect (-n) 0 0 (n + 1) ∧ y ∈ rect (-n) 0 0 (n + 1) ∧
    x 0 = -n ∧ y 0 = -n}



noncomputable def gst_fullWireConfig (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) :
    ConfigSpace (Sym2 (Site 2)) := by
  classical
  exact fun e => if e ∈ gst_fullWireSet n then true else dualConfig ω e

theorem gst_fullWire_open (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {e : Sym2 (Site 2)}
    (h : e ∈ gst_fullWireSet n) : gst_fullWireConfig ω n e = true := by
  classical
  unfold gst_fullWireConfig; simp [h]



theorem gst_wire_reach (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) (hn : 0 ≤ n) (k : ℕ)
    (hk : (k : ℤ) ≤ n + 1) :
    (openSubgraphInduce 2 (gst_fullWireConfig ω n) (rect (-n) 0 0 (n + 1))).Reachable
      ⟨![-n, 0], by rw [mem_rect]; simp; omega⟩
      ⟨![-n, (k : ℤ)], by rw [mem_rect]; simp; omega⟩ := by
  induction k with
  | zero => exact SimpleGraph.Reachable.refl _
  | succ m ih =>
    have hmle : (m : ℤ) ≤ n + 1 := by push_cast at hk ⊢; omega
    have step : (openSubgraphInduce 2 (gst_fullWireConfig ω n) (rect (-n) 0 0 (n + 1))).Adj
        ⟨![-n, (m : ℤ)], by rw [mem_rect]; simp; omega⟩
        ⟨![-n, ((m : ℤ) + 1)], by rw [mem_rect]; simp; omega⟩ := by
      rw [openSubgraphInduce_adj, openSubgraph_adj]
      refine ⟨by rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp, ?_⟩
      apply gst_fullWire_open
      exact ⟨![-n, (m : ℤ)], ![-n, (m : ℤ) + 1], rfl, by rw [mem_rect]; simp; omega,
        by rw [mem_rect]; simp; omega, by simp, by simp⟩
    have hcast : (((m + 1 : ℕ)) : ℤ) = (m : ℤ) + 1 := by push_cast; ring
    have hrec := (ih hmle).trans step.reachable
    rw [show (⟨![-n, ((m + 1 : ℕ) : ℤ)], by rw [mem_rect]; simp; omega⟩ :
          (rect (-n) 0 0 (n + 1) : Set (Site 2))) =
          ⟨![-n, (m : ℤ) + 1], by rw [mem_rect]; simp; omega⟩ from by
      apply Subtype.ext; simp [hcast]]
    exact hrec







theorem gst_fullWire_trivial (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) (hn : 0 ≤ n) :
    VerticalCrossing (gst_fullWireConfig ω n) (-n) 0 0 (n + 1) := by
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ (n + 1) - 0)
  have hbmem : (![-n, 0] : Site 2) ∈ bottomSide (-n) 0 0 (n + 1) := by
    refine ⟨?_, by simp⟩; rw [mem_rect]; simp; omega
  have hkeq : (k : ℤ) = n + 1 := by omega
  have hval1 : (![-n, (k : ℤ)] : Site 2) 1 = (k : ℤ) := by simp
  have hval0 : (![-n, (k : ℤ)] : Site 2) 0 = -n := by simp
  have htmem : (![-n, (k : ℤ)] : Site 2) ∈ topSide (-n) 0 0 (n + 1) := by
    refine ⟨?_, by rw [hval1]; omega⟩
    rw [mem_rect, hval0, hval1]; omega
  exact ⟨⟨![-n, 0], hbmem⟩, ⟨![-n, (k : ℤ)], htmem⟩, gst_wire_reach ω n hn k (by omega)⟩


















def gst_genuine_residue (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) : Prop :=
  jex_DualBarrierVCrossing ω n





theorem gst_dichotomy_of_genuine (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) (h : gst_genuine_residue ω n) :
    HorizontalCrossing ω 0 n 0 n ∨ DualVerticalCrossing ω 0 n 0 n :=
  jex_exhaustivity_of_barrier ω n hnoH h



theorem gst_genuine_residue_nonvacuous : gst_genuine_residue bcc_botCfg 2 :=
  jex_barrier_vcrossing_nonvacuous








theorem gst_matched_half_of_greenDichotomy (n : ℤ)
    (hmeasH : MeasurableSet (horizontalCrossingEvent 0 (n + 1) 0 n))
    (hmeasV : MeasurableSet (verticalCrossingEvent (-n) 0 0 (n + 1)))
    (hgreen : gec2_GreenDichotomy n)
    (hsym : rba_selfDualMeasure.real (verticalCrossingEvent (-n) 0 0 (n + 1))
              = rba_selfDualMeasure.real (horizontalCrossingEvent 0 (n + 1) 0 n)) :
    (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (horizontalCrossingEvent 0 (n + 1) 0 n) :=
  gec2_matched_half_of_greenDichotomy n hmeasH hmeasV hgreen hsym






theorem gst_greenDichotomy_false (n : ℤ) (hn : 1 ≤ n) : ¬ gec2_GreenDichotomy n :=
  gec2_greenDichotomy_false n hn

end Universality

end StatMech
