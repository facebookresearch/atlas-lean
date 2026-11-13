/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






































































import Mathlib
import Code.Walls.gc22edgecopy
import Code.Walls.gc21fiberconn
import Code.Walls.gc20closure
import Code.Walls.gc19switching
import Code.Walls.gc18core
import Code.Walls.gc16core
import Code.Walls.gc15core
import Code.Walls.gc7core
import Code.Walls.gc6_munonneg
import Code.Sharpness.Switching
import Code.Sharpness.FluxEdgeCopyBridge
import Code.Ising.TwoReplicaWeighted
import Code.Ising.HdomNativeWeight
import Code.Ising.AizenmanSignDominance

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
open StatMech.Sharpness.RandomCurrent StatMech.Sharpness.FluxEdgeCopy
open StatMech.Sharpness.FieldGhostDict
open StatMech.Walls.Gc5EqGap StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]














theorem gc23_tpsum_firstSlot_switch_pos (β : ℝ) (J : Sym2 V → ℝ) (m : ↥G.edgeFinset → ℕ)
    (A B : Finset V) {u v : V} (huv : u ≠ v)
    (hconn : ∀ K₂ : {K : ↥G.edgeFinset → ℕ // ∀ e, K e ≤ m e},
        sources G (ofEdgeFun G K₂.1) = B →
        connP (posEdges G.edgeFinset (ofEdgeFun G (fun e => m e - K₂.1 e))) u v) :
    gc15_tpsum G β J m (A ∆ {u, v}) B = gc15_tpsum G β J m A B := by
  rw [gc16_tpsum_bridge G β J m (A ∆ {u, v}) B, gc16_tpsum_bridge G β J m A B]
  refine Finset.sum_congr rfl (fun K₂ _ => ?_)
  by_cases hB : sources G (ofEdgeFun G K₂.1) = B
  · rw [if_pos hB]
    congr 1
    exact gc22_splitWeightedSum_switch_pos G β J (fun e => m e - K₂.1 e) A huv (hconn K₂ hB)
  · rw [if_neg hB, zero_mul, zero_mul]




theorem gc23_tpsum_secondSlot_switch_pos (β : ℝ) (J : Sym2 V → ℝ) (m : ↥G.edgeFinset → ℕ)
    (A B : Finset V) {u v : V} (huv : u ≠ v)
    (hconn : ∀ K₁ : {K : ↥G.edgeFinset → ℕ // ∀ e, K e ≤ m e},
        sources G (ofEdgeFun G K₁.1) = A →
        connP (posEdges G.edgeFinset (ofEdgeFun G (fun e => m e - K₁.1 e))) u v) :
    gc15_tpsum G β J m A (B ∆ {u, v}) = gc15_tpsum G β J m A B := by
  rw [gc16_tpsum_symm G β J m A (B ∆ {u, v}), gc16_tpsum_symm G β J m A B]
  exact gc23_tpsum_firstSlot_switch_pos G β J m B A huv hconn




theorem gc23_tpsum_starPair_collapse_pos (β : ℝ) (J : Sym2 V → ℝ) (m : ↥G.edgeFinset → ℕ)
    {u v : V} (huv : u ≠ v)
    (hconn : ∀ K₂ : {K : ↥G.edgeFinset → ℕ // ∀ e, K e ≤ m e},
        sources G (ofEdgeFun G K₂.1) = ∅ →
        connP (posEdges G.edgeFinset (ofEdgeFun G (fun e => m e - K₂.1 e))) u v) :
    gc15_tpsum G β J m ∅ {u, v} = gc15_tpsum G β J m ∅ ∅ := by
  have h := gc23_tpsum_secondSlot_switch_pos G β J m ∅ ∅ huv ?_
  · rwa [show (∅ : Finset V) ∆ {u, v} = {u, v} from by simp] at h
  · intro K₁ hK₁; exact hconn K₁ hK₁




















theorem gc23_fibre_starGap_nonpos_uncond (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (m : ↥(withGhost G).edgeFinset → ℕ)
    (K₂ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e})
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hbdry : sources (withGhost G) (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e))
        = ({some o, some x, some y, none} : Finset (Option V))) :
    hnw_mass (withGhost G) β (ghostCoupling h β (fun _ => 1))
          (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e)) ∅
      - hnw_mass (withGhost G) β (ghostCoupling h β (fun _ => 1))
          (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e)) {some o, none}
      - hnw_mass (withGhost G) β (ghostCoupling h β (fun _ => 1))
          (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e)) {some o, some x}
      - hnw_mass (withGhost G) β (ghostCoupling h β (fun _ => 1))
          (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e)) {some o, some y} ≤ 0 := by
  have hog : (some o : Option V) ≠ none := by simp
  have hoxs : (some o : Option V) ≠ some x := by simpa using hox
  have hoys : (some o : Option V) ≠ some y := by simpa using hoy
  have hxys : (some x : Option V) ≠ some y := by simpa using hxy
  have hxgs : (some x : Option V) ≠ none := by simp
  have hygs : (some y : Option V) ≠ none := by simp
  set J' := ghostCoupling h β (fun _ : Sym2 V => (1 : ℝ)) with hJ'
  have hJnn : ∀ e, (0 : ℝ) ≤ J' e := gc6_ghostCoupling_nonneg (V := V) β h hh
  have bg : 0 ≤ hnw_mass (withGhost G) β J' (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e))
      {some o, none} :=
    hnw_mass_nonneg (withGhost G) β J' hβ hJnn _ _
  have bx : 0 ≤ hnw_mass (withGhost G) β J' (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e))
      {some o, some x} :=
    hnw_mass_nonneg (withGhost G) β J' hβ hJnn _ _
  have by' : 0 ≤ hnw_mass (withGhost G) β J' (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e))
      {some o, some y} :=
    hnw_mass_nonneg (withGhost G) β J' hβ hJnn _ _
  have htri := gc21_fibre_posTrichotomy G m K₂ (some o) (some x) (some y) none
    hoxs hoys hog hxys hxgs hygs hbdry
  rcases htri with hOg | hp1 | hp2
  · rw [gc22_hnw_mass_collapse_pos (withGhost G) β J' (fun e => m e - K₂.1 e) hog hOg]; linarith
  · rw [gc22_hnw_mass_collapse_pos (withGhost G) β J' (fun e => m e - K₂.1 e) hoxs hp1.1]; linarith
  · rw [gc22_hnw_mass_collapse_pos (withGhost G) β J' (fun e => m e - K₂.1 e) hoys hp2.1]; linarith












theorem gc23_firstFour_nonpos_uncond (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (m : ↥(withGhost G).edgeFinset → ℕ)
    (hbdry : sources (withGhost G) (ofEdgeFun (withGhost G) m)
        = ({some o, some x, some y, none} : Finset (Option V))) :
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
    have hinner : sources (withGhost G) (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e))
        = ({some o, some x, some y, none} : Finset (Option V)) := by
      have hadd := sources_ofEdgeFun_add (withGhost G) m K₂.1 K₂.2
      rw [hbdry, hK₂] at hadd
      rw [show (∅ : Finset (Option V)) ∆
            sources (withGhost G) (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e))
          = sources (withGhost G) (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e))
          from symmDiff_eq_right.mpr rfl] at hadd
      exact hadd.symm
    have hsg := gc23_fibre_starGap_nonpos_uncond G β h hβ hh o x y m K₂ hox hoy hxy hinner
    exact mul_nonpos_of_nonneg_of_nonpos hw hsg
  · rw [if_neg hK₂, zero_mul]



















theorem gc23_pair_mass_le_base_pos (β : ℝ) (J : Sym2 (Option V) → ℝ) (hβ : 0 ≤ β)
    (hJ : ∀ e, 0 ≤ J e) (p : ↥(withGhost G).edgeFinset → ℕ) {u v : V}
    (huv : (some u : Option V) ≠ some v) :
    hnw_mass (withGhost G) β J (ofEdgeFun (withGhost G) p) {some u, some v}
      ≤ hnw_mass (withGhost G) β J (ofEdgeFun (withGhost G) p) ∅ := by
  by_cases hconn : connP (posEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) p))
      (some u) (some v)
  · rw [gc22_hnw_mass_collapse_pos (withGhost G) β J p huv hconn]
  · rw [gc18_star_mass_vanish (withGhost G) β J (ofEdgeFun (withGhost G) p)
        (gc20_withGhost_loopless G) huv hconn]
    exact hnw_mass_nonneg (withGhost G) β J hβ hJ _ _










theorem gc23_fifth_le_starless (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (m : ↥(withGhost G).edgeFinset → ℕ) :
    gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m {some o, none} {some x, none}
      ≤ gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some x, none} := by
  have hJnn : ∀ e, (0 : ℝ) ≤ ghostCoupling h β (fun _ => 1) e :=
    gc6_ghostCoupling_nonneg (V := V) β h hh
  rw [gc18_fifth_reorg G β h o x y m]
  
  have hrhs : gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some x, none}
      = ∑ K₂ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e},
          (if sources (withGhost G) (ofEdgeFun (withGhost G) K₂.1) = {some x, none}
            then weight (withGhost G) β (ghostCoupling h β (fun _ => 1)) (ofEdgeFun (withGhost G) K₂.1)
            else 0)
            * hnw_mass (withGhost G) β (ghostCoupling h β (fun _ => 1))
                (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e)) ∅ := by
    unfold hnw_mass
    exact gc16_tpsum_bridge (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some x, none}
  rw [hrhs]
  refine Finset.sum_le_sum (fun K₂ _ => ?_)
  by_cases hK₂ : sources (withGhost G) (ofEdgeFun (withGhost G) K₂.1) = {some x, none}
  · rw [if_pos hK₂]
    have hw : (0 : ℝ) ≤ weight (withGhost G) β (ghostCoupling h β (fun _ => 1))
        (ofEdgeFun (withGhost G) K₂.1) :=
      asd_weight_nonneg (withGhost G) β (ghostCoupling h β (fun _ => 1)) hβ hJnn _
    have hog : (some o : Option V) ≠ none := by simp
    
    have hle : hnw_mass (withGhost G) β (ghostCoupling h β (fun _ => 1))
          (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e)) {some o, none}
        ≤ hnw_mass (withGhost G) β (ghostCoupling h β (fun _ => 1))
          (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e)) ∅ := by
      by_cases hconn : connP (posEdges (withGhost G).edgeFinset
          (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e))) (some o) none
      · rw [gc22_hnw_mass_collapse_pos (withGhost G) β (ghostCoupling h β (fun _ => 1))
          (fun e => m e - K₂.1 e) hog hconn]
      · rw [gc18_star_mass_vanish (withGhost G) β (ghostCoupling h β (fun _ => 1))
            (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e)) (gc20_withGhost_loopless G) hog hconn]
        exact hnw_mass_nonneg (withGhost G) β (ghostCoupling h β (fun _ => 1)) hβ hJnn _ _
    exact mul_le_mul_of_nonneg_left hle hw
  · rw [if_neg hK₂, zero_mul, zero_mul]






























def gc23_fifthDomination (β h : ℝ) (o x y : V) : Prop :=
  ∀ m : ↥(withGhost G).edgeFinset → ℕ,
    sources (withGhost G) (ofEdgeFun (withGhost G) m)
        = ({some o, some x, some y, none} : Finset (Option V)) →
    connP (posEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) m)) (some o) none →
      2 * gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m
            {some o, none} {some x, none}
        ≤ gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, none}
          + gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some x}
          + gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some y}
          - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ ∅






theorem gc23_allConnResidue_iff_fifthDomination (β h : ℝ) (o x y : V) :
    gc23_fifthDomination G β h o x y ↔ gc22_AllConnResidue G β h o x y := by
  constructor
  · intro hdom m hm hOg
    have h5 := hdom m hm hOg
    linarith
  · intro hres m hm hOg
    have h5 := hres m hm hOg
    linarith






theorem gc23_cert_of_fifthDomination (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hdom : gc23_fifthDomination G β h o x y) :
    gc16_PerConfigCert G β h o x y :=
  gc22_cert_of_allConnResidue G β h hβ hh o x y hox hoy hxy
    ((gc23_allConnResidue_iff_fifthDomination G β h o x y).mp hdom)




theorem gc23_ursell_nonpos_of_fifthDomination (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hdom : gc23_fifthDomination G β h o x y) :
    eg_ursell3 G β h o x y ≤ 0 :=
  gc16_cert_closes_u3 G β h o x y hox hoy hxy
    (gc23_cert_of_fifthDomination G β h hβ hh o x y hox hoy hxy hdom)



















theorem gc23_deficit_reorg (β h : ℝ) (o x y : V) (m : ↥(withGhost G).edgeFinset → ℕ) :
    gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, none}
        + gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some x}
        + gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some y}
        - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ ∅
      = ∑ K₂ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e},
          (if sources (withGhost G) (ofEdgeFun (withGhost G) K₂.1) = ∅
            then weight (withGhost G) β (ghostCoupling h β (fun _ => 1)) (ofEdgeFun (withGhost G) K₂.1)
            else 0)
            * (hnw_mass (withGhost G) β (ghostCoupling h β (fun _ => 1))
                  (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e)) {some o, none}
                + hnw_mass (withGhost G) β (ghostCoupling h β (fun _ => 1))
                    (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e)) {some o, some x}
                + hnw_mass (withGhost G) β (ghostCoupling h β (fun _ => 1))
                    (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e)) {some o, some y}
                - hnw_mass (withGhost G) β (ghostCoupling h β (fun _ => 1))
                    (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e)) ∅) := by
  have h4 := gc18_firstFour_reorg G β h o x y m
  rw [show
      gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, none}
        + gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some x}
        + gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some y}
        - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ ∅
      = -(gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ ∅
          - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, none}
          - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some x}
          - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some y})
      from by ring]
  rw [h4, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun K₂ _ => ?_)
  ring















theorem gc23_fifthDomination_of_fifthVanish (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (m : ↥(withGhost G).edgeFinset → ℕ)
    (hbdry : sources (withGhost G) (ofEdgeFun (withGhost G) m)
        = ({some o, some x, some y, none} : Finset (Option V)))
    (hT4 : gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m
        {some o, none} {some x, none} = 0) :
    2 * gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m {some o, none} {some x, none}
      ≤ gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, none}
        + gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some x}
        + gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some y}
        - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ ∅ := by
  have hdef := gc23_firstFour_nonpos_uncond G β h hβ hh o x y hox hoy hxy m hbdry
  rw [hT4]; linarith

end StatMech.Walls
