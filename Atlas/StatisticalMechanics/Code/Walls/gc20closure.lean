/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


























































import Mathlib
import Code.Walls.gc19switching
import Code.Walls.gc18core
import Code.Walls.gc16core
import Code.Walls.gc15core
import Code.Walls.gc7core
import Code.Walls.gc6_munonneg
import Code.Ising.HdomNativeWeight
import Code.Ising.AizenmanSignDominance
import Code.Ising.TwoReplicaWeighted
import Code.Sharpness.FluxEdgeCopyBridge

open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option maxHeartbeats 1600000

namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness
open StatMech.Sharpness.FieldGhostDict
open StatMech.Walls.Gc5EqGap StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]










theorem gc20_withGhost_loopless :
    ∀ e ∈ (withGhost G).edgeFinset, ¬ e.IsDiag := by
  intro e he
  rw [SimpleGraph.mem_edgeFinset] at he
  exact fun hdiag => (withGhost G).not_isDiag_of_mem_edgeSet he hdiag


theorem gc20_ofEdgeFun_fiber_le (m : ↥(withGhost G).edgeFinset → ℕ)
    (K₂ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e}) (e : Sym2 (Option V)) :
    ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e) e ≤ ofEdgeFun (withGhost G) m e := by
  unfold ofEdgeFun
  by_cases he : e ∈ (withGhost G).edgeFinset
  · simp only [he, dif_pos]; omega
  · simp only [he, dif_neg, not_false_iff, le_refl]





theorem gc20_fiber_disc_of_disc (m : ↥(withGhost G).edgeFinset → ℕ)
    (K₂ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e}) {u v : Option V}
    (hdisc : ¬ connP (posEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) m)) u v) :
    ¬ connP (posEdges (withGhost G).edgeFinset
        (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e))) u v := by
  intro hconn
  apply hdisc
  refine connP_mono ?_ hconn
  intro e he
  rw [posEdges, Finset.mem_filter] at he ⊢
  exact ⟨he.1, le_trans he.2 (gc20_ofEdgeFun_fiber_le G m K₂ e)⟩












theorem gc20_adjP_posEdges_iff (m : ↥G.edgeFinset → ℕ) (a b : V) :
    adjP (posEdges G.edgeFinset (ofEdgeFun G m)) a b
      ↔ (currentSubgraph G (ofEdgeFun G m)).Adj a b := by
  rw [currentSubgraph_adj]
  constructor
  · rintro ⟨e, he, ha, hb, hne⟩
    rw [posEdges, Finset.mem_filter] at he
    have hedge : e = s(a, b) := (Sym2.mem_and_mem_iff hne).mp ⟨ha, hb⟩
    have hadj : G.Adj a b := by
      have hm : e ∈ G.edgeFinset := he.1
      rw [hedge, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hm
      exact hm
    refine ⟨hadj, ?_⟩
    rw [← hedge]; exact he.2
  · rintro ⟨hadj, hpos⟩
    refine ⟨s(a, b), ?_, Sym2.mem_mk_left a b, Sym2.mem_mk_right a b, G.ne_of_adj hadj⟩
    rw [posEdges, Finset.mem_filter]
    exact ⟨SimpleGraph.mem_edgeFinset.mpr ((SimpleGraph.mem_edgeSet G).mpr hadj), hpos⟩





theorem gc20_connP_posEdges_iff_currentConnected (m : ↥G.edgeFinset → ℕ) (u v : V) :
    connP (posEdges G.edgeFinset (ofEdgeFun G m)) u v
      ↔ CurrentConnected G (ofEdgeFun G m) u v := by
  unfold connP CurrentConnected
  rw [SimpleGraph.reachable_iff_reflTransGen]
  constructor
  · intro h
    refine Relation.ReflTransGen.mono ?_ h
    intro a b hstep; exact (gc20_adjP_posEdges_iff G m a b).mp hstep
  · intro h
    refine Relation.ReflTransGen.mono ?_ h
    intro a b hstep; exact (gc20_adjP_posEdges_iff G m a b).mpr hstep







theorem gc20_disc_iff_connK_univ (m : ↥G.edgeFinset → ℕ) (u v : V) :
    ¬ connP (posEdges G.edgeFinset (ofEdgeFun G m)) u v
      ↔ ¬ RandomCurrent.connK (FluxEdgeCopy.endsM G m) univ u v := by
  rw [gc20_connP_posEdges_iff_currentConnected, FluxEdgeCopy.connK_univ_iff]












theorem gc20_fifth_vanish_of_disc (β h : ℝ) (o x y : V) (hog : (some o : Option V) ≠ none)
    (m : ↥(withGhost G).edgeFinset → ℕ)
    (hdisc : ¬ connP (posEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) m))
        (some o) none) :
    gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m {some o, none} {some x, none}
      = 0 := by
  rw [gc18_fifth_reorg G β h o x y m]
  refine Finset.sum_eq_zero (fun K₂ _ => ?_)
  rw [gc18_star_mass_vanish (withGhost G) β (ghostCoupling h β (fun _ => 1))
    (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e)) (gc20_withGhost_loopless G) hog
    (gc20_fiber_disc_of_disc G m K₂ hdisc), mul_zero]



















theorem gc20_starGap_zero_pairing1 (β : ℝ) (J : Sym2 (Option V) → ℝ)
    (m' : Ising.Current (Option V)) {o x y : V}
    (hog : (some o : Option V) ≠ none) (hoxs : (some o : Option V) ≠ some x)
    (hoys : (some o : Option V) ≠ some y)
    (Hox : connP (oddEdges (withGhost G).edgeFinset m') (some o) (some x))
    (Hg : ¬ connP (posEdges (withGhost G).edgeFinset m') (some o) none)
    (Hy : ¬ connP (posEdges (withGhost G).edgeFinset m') (some o) (some y)) :
    hnw_mass (withGhost G) β J m' ∅ - hnw_mass (withGhost G) β J m' {some o, none}
        - hnw_mass (withGhost G) β J m' {some o, some x}
        - hnw_mass (withGhost G) β J m' {some o, some y} = 0 := by
  have eg : hnw_mass (withGhost G) β J m' {some o, none} = 0 :=
    gc18_star_mass_vanish (withGhost G) β J m' (gc20_withGhost_loopless G) hog Hg
  have ey : hnw_mass (withGhost G) β J m' {some o, some y} = 0 :=
    gc18_star_mass_vanish (withGhost G) β J m' (gc20_withGhost_loopless G) hoys Hy
  have ex : hnw_mass (withGhost G) β J m' {some o, some x} = hnw_mass (withGhost G) β J m' ∅ := by
    have := hnw_switching (withGhost G) β J m' hoxs Hox ∅
    rwa [show (∅ : Finset (Option V)) ∆ {some o, some x} = {some o, some x} from by simp] at this
  rw [eg, ey, ex]; ring





theorem gc20_starGap_zero_pairing2 (β : ℝ) (J : Sym2 (Option V) → ℝ)
    (m' : Ising.Current (Option V)) {o x y : V}
    (hog : (some o : Option V) ≠ none) (hoxs : (some o : Option V) ≠ some x)
    (hoys : (some o : Option V) ≠ some y)
    (Hoy : connP (oddEdges (withGhost G).edgeFinset m') (some o) (some y))
    (Hg : ¬ connP (posEdges (withGhost G).edgeFinset m') (some o) none)
    (Hx : ¬ connP (posEdges (withGhost G).edgeFinset m') (some o) (some x)) :
    hnw_mass (withGhost G) β J m' ∅ - hnw_mass (withGhost G) β J m' {some o, none}
        - hnw_mass (withGhost G) β J m' {some o, some x}
        - hnw_mass (withGhost G) β J m' {some o, some y} = 0 := by
  have eg : hnw_mass (withGhost G) β J m' {some o, none} = 0 :=
    gc18_star_mass_vanish (withGhost G) β J m' (gc20_withGhost_loopless G) hog Hg
  have ex : hnw_mass (withGhost G) β J m' {some o, some x} = 0 :=
    gc18_star_mass_vanish (withGhost G) β J m' (gc20_withGhost_loopless G) hoxs Hx
  have ey : hnw_mass (withGhost G) β J m' {some o, some y} = hnw_mass (withGhost G) β J m' ∅ := by
    have := hnw_switching (withGhost G) β J m' hoys Hoy ∅
    rwa [show (∅ : Finset (Option V)) ∆ {some o, some y} = {some o, some y} from by simp] at this
  rw [eg, ex, ey]; ring




















theorem gc20_starGap_nonpos_of_disc_arc (β : ℝ) (J : Sym2 (Option V) → ℝ) (hβ : 0 ≤ β)
    (hJ : ∀ e, 0 ≤ J e) (m' : Ising.Current (Option V)) {o x y : V}
    (hog : (some o : Option V) ≠ none) (hoxs : (some o : Option V) ≠ some x)
    (hoys : (some o : Option V) ≠ some y)
    (Hg : ¬ connP (posEdges (withGhost G).edgeFinset m') (some o) none)
    (Harc : connP (oddEdges (withGhost G).edgeFinset m') (some o) (some x)
        ∨ connP (oddEdges (withGhost G).edgeFinset m') (some o) (some y)) :
    hnw_mass (withGhost G) β J m' ∅ - hnw_mass (withGhost G) β J m' {some o, none}
        - hnw_mass (withGhost G) β J m' {some o, some x}
        - hnw_mass (withGhost G) β J m' {some o, some y} ≤ 0 := by
  have eg : hnw_mass (withGhost G) β J m' {some o, none} = 0 :=
    gc18_star_mass_vanish (withGhost G) β J m' (gc20_withGhost_loopless G) hog Hg
  have bx : 0 ≤ hnw_mass (withGhost G) β J m' {some o, some x} :=
    hnw_mass_nonneg (withGhost G) β J hβ hJ m' _
  have by' : 0 ≤ hnw_mass (withGhost G) β J m' {some o, some y} :=
    hnw_mass_nonneg (withGhost G) β J hβ hJ m' _
  rcases Harc with Hx | Hy
  · have ex : hnw_mass (withGhost G) β J m' {some o, some x} = hnw_mass (withGhost G) β J m' ∅ := by
      have := hnw_switching (withGhost G) β J m' hoxs Hx ∅
      rwa [show (∅ : Finset (Option V)) ∆ {some o, some x} = {some o, some x} from by simp] at this
    rw [eg, ex]; linarith
  · have ey : hnw_mass (withGhost G) β J m' {some o, some y} = hnw_mass (withGhost G) β J m' ∅ := by
      have := hnw_switching (withGhost G) β J m' hoys Hy ∅
      rwa [show (∅ : Finset (Option V)) ∆ {some o, some y} = {some o, some y} from by simp] at this
    rw [eg, ey]; linarith












theorem gc20_firstFour_zero_pairing1 (β h : ℝ) (o x y : V)
    (hog : (some o : Option V) ≠ none) (hoxs : (some o : Option V) ≠ some x)
    (hoys : (some o : Option V) ≠ some y)
    (m : ↥(withGhost G).edgeFinset → ℕ)
    (hdiscG : ¬ connP (posEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) m))
        (some o) none)
    (hdiscY : ¬ connP (posEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) m))
        (some o) (some y))
    (hOx : ∀ K₂ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e},
        sources (withGhost G) (ofEdgeFun (withGhost G) K₂.1) = ∅ →
        connP (oddEdges (withGhost G).edgeFinset
            (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e))) (some o) (some x)) :
    gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ ∅
        - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, none}
        - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some x}
        - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some y} = 0 := by
  rw [gc18_firstFour_reorg G β h o x y m]
  refine Finset.sum_eq_zero (fun K₂ _ => ?_)
  by_cases hK₂ : sources (withGhost G) (ofEdgeFun (withGhost G) K₂.1) = ∅
  · rw [if_pos hK₂,
      gc20_starGap_zero_pairing1 G β (ghostCoupling h β (fun _ => 1))
        (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e)) hog hoxs hoys
        (hOx K₂ hK₂)
        (gc20_fiber_disc_of_disc G m K₂ hdiscG)
        (gc20_fiber_disc_of_disc G m K₂ hdiscY), mul_zero]
  · rw [if_neg hK₂, zero_mul]




theorem gc20_firstFour_zero_pairing2 (β h : ℝ) (o x y : V)
    (hog : (some o : Option V) ≠ none) (hoxs : (some o : Option V) ≠ some x)
    (hoys : (some o : Option V) ≠ some y)
    (m : ↥(withGhost G).edgeFinset → ℕ)
    (hdiscG : ¬ connP (posEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) m))
        (some o) none)
    (hdiscX : ¬ connP (posEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) m))
        (some o) (some x))
    (hOy : ∀ K₂ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e},
        sources (withGhost G) (ofEdgeFun (withGhost G) K₂.1) = ∅ →
        connP (oddEdges (withGhost G).edgeFinset
            (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e))) (some o) (some y)) :
    gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ ∅
        - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, none}
        - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some x}
        - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some y} = 0 := by
  rw [gc18_firstFour_reorg G β h o x y m]
  refine Finset.sum_eq_zero (fun K₂ _ => ?_)
  by_cases hK₂ : sources (withGhost G) (ofEdgeFun (withGhost G) K₂.1) = ∅
  · rw [if_pos hK₂,
      gc20_starGap_zero_pairing2 G β (ghostCoupling h β (fun _ => 1))
        (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e)) hog hoxs hoys
        (hOy K₂ hK₂)
        (gc20_fiber_disc_of_disc G m K₂ hdiscG)
        (gc20_fiber_disc_of_disc G m K₂ hdiscX), mul_zero]
  · rw [if_neg hK₂, zero_mul]












theorem gc20_firstFour_nonpos_of_disc_arc (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hog : (some o : Option V) ≠ none) (hoxs : (some o : Option V) ≠ some x)
    (hoys : (some o : Option V) ≠ some y)
    (m : ↥(withGhost G).edgeFinset → ℕ)
    (hdiscG : ¬ connP (posEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) m))
        (some o) none)
    (hArc : ∀ K₂ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e},
        sources (withGhost G) (ofEdgeFun (withGhost G) K₂.1) = ∅ →
        connP (oddEdges (withGhost G).edgeFinset
            (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e))) (some o) (some x)
          ∨ connP (oddEdges (withGhost G).edgeFinset
              (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e))) (some o) (some y)) :
    gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ ∅
        - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, none}
        - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some x}
        - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some y} ≤ 0 := by
  have hJnn : ∀ e, (0 : ℝ) ≤ ghostCoupling h β (fun _ => 1) e :=
    gc6_ghostCoupling_nonneg (V := V) β h hh
  rw [gc18_firstFour_reorg G β h o x y m]
  refine Finset.sum_nonpos (fun K₂ _ => ?_)
  by_cases hK₂ : sources (withGhost G) (ofEdgeFun (withGhost G) K₂.1) = ∅
  · rw [if_pos hK₂]
    have hw : (0 : ℝ) ≤ weight (withGhost G) β (ghostCoupling h β (fun _ => 1))
        (ofEdgeFun (withGhost G) K₂.1) :=
      asd_weight_nonneg (withGhost G) β (ghostCoupling h β (fun _ => 1)) hβ hJnn _
    have hsg : hnw_mass (withGhost G) β (ghostCoupling h β (fun _ => 1))
          (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e)) ∅
        - hnw_mass (withGhost G) β (ghostCoupling h β (fun _ => 1))
            (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e)) {some o, none}
        - hnw_mass (withGhost G) β (ghostCoupling h β (fun _ => 1))
            (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e)) {some o, some x}
        - hnw_mass (withGhost G) β (ghostCoupling h β (fun _ => 1))
            (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e)) {some o, some y} ≤ 0 :=
      gc20_starGap_nonpos_of_disc_arc G β (ghostCoupling h β (fun _ => 1)) hβ hJnn
        (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e)) hog hoxs hoys
        (gc20_fiber_disc_of_disc G m K₂ hdiscG) (hArc K₂ hK₂)
    exact mul_nonpos_of_nonneg_of_nonpos hw hsg
  · rw [if_neg hK₂, zero_mul]














theorem gc20_cert_zero_of_pairing1 (β h : ℝ) (o x y : V)
    (hog : (some o : Option V) ≠ none) (hoxs : (some o : Option V) ≠ some x)
    (hoys : (some o : Option V) ≠ some y)
    (m : ↥(withGhost G).edgeFinset → ℕ)
    (hdiscG : ¬ connP (posEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) m))
        (some o) none)
    (hdiscY : ¬ connP (posEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) m))
        (some o) (some y))
    (hOx : ∀ K₂ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e},
        sources (withGhost G) (ofEdgeFun (withGhost G) K₂.1) = ∅ →
        connP (oddEdges (withGhost G).edgeFinset
            (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e))) (some o) (some x)) :
    gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ ∅
        - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, none}
        - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some x}
        - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some y}
        + 2 * gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m
              {some o, none} {some x, none} = 0 := by
  rw [gc20_fifth_vanish_of_disc G β h o x y hog m hdiscG]
  have h4 := gc20_firstFour_zero_pairing1 G β h o x y hog hoxs hoys m hdiscG hdiscY hOx
  linarith



theorem gc20_cert_zero_of_pairing2 (β h : ℝ) (o x y : V)
    (hog : (some o : Option V) ≠ none) (hoxs : (some o : Option V) ≠ some x)
    (hoys : (some o : Option V) ≠ some y)
    (m : ↥(withGhost G).edgeFinset → ℕ)
    (hdiscG : ¬ connP (posEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) m))
        (some o) none)
    (hdiscX : ¬ connP (posEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) m))
        (some o) (some x))
    (hOy : ∀ K₂ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e},
        sources (withGhost G) (ofEdgeFun (withGhost G) K₂.1) = ∅ →
        connP (oddEdges (withGhost G).edgeFinset
            (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e))) (some o) (some y)) :
    gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ ∅
        - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, none}
        - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some x}
        - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some y}
        + 2 * gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m
              {some o, none} {some x, none} = 0 := by
  rw [gc20_fifth_vanish_of_disc G β h o x y hog m hdiscG]
  have h4 := gc20_firstFour_zero_pairing2 G β h o x y hog hoxs hoys m hdiscG hdiscX hOy
  linarith







theorem gc20_cert_nonpos_of_disc_arc (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hog : (some o : Option V) ≠ none) (hoxs : (some o : Option V) ≠ some x)
    (hoys : (some o : Option V) ≠ some y)
    (m : ↥(withGhost G).edgeFinset → ℕ)
    (hdiscG : ¬ connP (posEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) m))
        (some o) none)
    (hArc : ∀ K₂ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e},
        sources (withGhost G) (ofEdgeFun (withGhost G) K₂.1) = ∅ →
        connP (oddEdges (withGhost G).edgeFinset
            (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e))) (some o) (some x)
          ∨ connP (oddEdges (withGhost G).edgeFinset
              (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e))) (some o) (some y)) :
    gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ ∅
        - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, none}
        - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some x}
        - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some y}
        + 2 * gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m
              {some o, none} {some x, none} ≤ 0 := by
  rw [gc20_fifth_vanish_of_disc G β h o x y hog m hdiscG]
  have h4 := gc20_firstFour_nonpos_of_disc_arc G β h hβ hh o x y hog hoxs hoys m hdiscG hArc
  linarith




















def gc20_FiberConnRegime (β h : ℝ) (o x y : V) (m : ↥(withGhost G).edgeFinset → ℕ) : Prop :=
  
  ((∀ K₁ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e},
      sources (withGhost G) (ofEdgeFun (withGhost G) K₁.1) = ∅ →
      connP (oddEdges (withGhost G).edgeFinset
          (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e))) (some o) none)
    ∧ (∀ K₁ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e},
        sources (withGhost G) (ofEdgeFun (withGhost G) K₁.1) = ∅ →
        connP (oddEdges (withGhost G).edgeFinset
            (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e))) (some o) (some x))
    ∧ (∀ K₁ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e},
        sources (withGhost G) (ofEdgeFun (withGhost G) K₁.1) = ∅ →
        connP (oddEdges (withGhost G).edgeFinset
            (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e))) (some o) (some y))
    ∧ (∀ K₂ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e},
        sources (withGhost G) (ofEdgeFun (withGhost G) K₂.1) = {some x, none} →
        connP (oddEdges (withGhost G).edgeFinset
            (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e))) (some o) none)
    ∧ (∀ K₁ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e},
        sources (withGhost G) (ofEdgeFun (withGhost G) K₁.1) = ∅ →
        connP (oddEdges (withGhost G).edgeFinset
            (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e))) (some x) none))
  ∨ 
  (¬ connP (posEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) m)) (some o) none
    ∧ ¬ connP (posEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) m)) (some o) (some y)
    ∧ (∀ K₂ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e},
        sources (withGhost G) (ofEdgeFun (withGhost G) K₂.1) = ∅ →
        connP (oddEdges (withGhost G).edgeFinset
            (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e))) (some o) (some x)))
  ∨ 
  (¬ connP (posEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) m)) (some o) none
    ∧ ¬ connP (posEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) m)) (some o) (some x)
    ∧ (∀ K₂ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e},
        sources (withGhost G) (ofEdgeFun (withGhost G) K₂.1) = ∅ →
        connP (oddEdges (withGhost G).edgeFinset
            (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e))) (some o) (some y)))







theorem gc20_cert_of_trichotomy (β h : ℝ) (o x y : V) (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hreg : ∀ m : ↥(withGhost G).edgeFinset → ℕ,
      sources (withGhost G) (ofEdgeFun (withGhost G) m)
          = ({some o, some x, some y, none} : Finset (Option V)) →
      gc20_FiberConnRegime G β h o x y m) :
    gc16_PerConfigCert G β h o x y := by
  intro m hm
  have hog : (some o : Option V) ≠ none := by simp
  have hoxs : (some o : Option V) ≠ some x := by simpa using hox
  have hoys : (some o : Option V) ≠ some y := by simpa using hoy
  rcases hreg m hm with hall | hp1 | hp2
  · 
    obtain ⟨hOg, hOx, hOy, hcr1, hcr2⟩ := hall
    have hzero := gc19_cert_zero_of_allConn (withGhost G) β (ghostCoupling h β (fun _ => 1)) m
      (o := some o) (x := some x) (y := some y) (g := none)
      hog hoxs hoys (by simp) hOg hOx hOy hcr1 hcr2
    rw [hzero]
  · 
    obtain ⟨hdiscG, hdiscY, hOx⟩ := hp1
    rw [gc20_cert_zero_of_pairing1 G β h o x y hog hoxs hoys m hdiscG hdiscY hOx]
  · 
    obtain ⟨hdiscG, hdiscX, hOy⟩ := hp2
    rw [gc20_cert_zero_of_pairing2 G β h o x y hog hoxs hoys m hdiscG hdiscX hOy]








theorem gc20_ursell_nonpos_of_trichotomy (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hreg : ∀ m : ↥(withGhost G).edgeFinset → ℕ,
      sources (withGhost G) (ofEdgeFun (withGhost G) m)
          = ({some o, some x, some y, none} : Finset (Option V)) →
      gc20_FiberConnRegime G β h o x y m) :
    eg_ursell3 G β h o x y ≤ 0 :=
  gc16_cert_closes_u3 G β h o x y hox hoy hxy
    (gc20_cert_of_trichotomy G β h o x y hox hoy hxy hreg)



theorem gc20_ghs_of_trichotomy (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V)
    (hreg : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → ∀ m : ↥(withGhost G).edgeFinset → ℕ,
      sources (withGhost G) (ofEdgeFun (withGhost G) m)
          = ({some o, some x, some y, none} : Finset (Option V)) →
      gc20_FiberConnRegime G β h o x y m) :
    GHSThreePointSym G β h o :=
  gc16_ghs_of_cert G β h hβ hh o
    (fun x y hox hoy hxy => gc20_cert_of_trichotomy G β h o x y hox hoy hxy (hreg x y hox hoy hxy))




theorem gc20_aizenman_barsky_of_trichotomy (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V) (J : ℝ)
    (hreg : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → ∀ m : ↥(withGhost G).edgeFinset → ℕ,
      sources (withGhost G) (ofEdgeFun (withGhost G) m)
          = ({some o, some x, some y, none} : Finset (Option V)) →
      gc20_FiberConnRegime G β h o x y m)
    (hfactor : ∑ e ∈ G.edgeFinset, ghsBoundSym G β h o e
        = J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o) :
    bondEnergySusceptibility G β h o
      ≤ J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o :=
  gc16_aizenman_barsky_of_cert G β h hβ hh o J
    (fun x y hox hoy hxy => gc20_cert_of_trichotomy G β h o x y hox hoy hxy (hreg x y hox hoy hxy))
    hfactor

end StatMech.Walls
