/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
















































































import Mathlib
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




















theorem gc22_splitWeightedSum_eq_edgecopy_count (β : ℝ) (J : Sym2 V → ℝ)
    (p : ↥G.edgeFinset → ℕ) (A : Finset V) :
    splitWeightedSum G β J (ofEdgeFun G p) 1 A
      = (#((univ : Finset (Finset (Copy G p))).filter
          (fun S => RandomCurrent.sources (endsM G p) S = A)) : ℝ)
        * weight G β J (ofEdgeFun G p) := by
  rw [← gc16_inner_eq_splitWeightedSum G β J p A]
  have hstep : ∀ K₁ : {K : ↥G.edgeFinset → ℕ // ∀ e, K e ≤ p e},
      (if Sharpness.sources G (ofEdgeFun G K₁.1) = A then weight G β J (ofEdgeFun G K₁.1) else 0)
        * weight G β J (ofEdgeFun G fun e => p e - K₁.1 e)
      = (∏ e : ↥G.edgeFinset, (p e).choose (K₁.1 e))
        • ((if Sharpness.sources G (ofEdgeFun G K₁.1) = A then (1 : ℝ) else 0)
            * weight G β J (ofEdgeFun G p)) := by
    intro K₁
    rw [nsmul_eq_mul, Nat.cast_prod]
    by_cases hA : Sharpness.sources G (ofEdgeFun G K₁.1) = A
    · rw [if_pos hA, if_pos hA, weight_split_eq_binom G β J p K₁.1 K₁.2]
      rw [show (∏ e ∈ G.edgeFinset, (Nat.choose ((ofEdgeFun G p) e) ((ofEdgeFun G K₁.1) e) : ℝ))
            = (∏ e : ↥G.edgeFinset, ((p e).choose (K₁.1 e) : ℝ)) from by
        rw [← Finset.prod_attach G.edgeFinset
          (fun e => (Nat.choose ((ofEdgeFun G p) e) ((ofEdgeFun G K₁.1) e) : ℝ))]
        refine Finset.prod_congr rfl (fun e _ => ?_)
        unfold ofEdgeFun; rw [dif_pos e.2, dif_pos e.2]]
      ring
    · rw [if_neg hA]; simp [hA]
  simp_rw [hstep]
  have hbridge := flux_edgecopy_bridge G p (fun k =>
    (if Sharpness.sources G (ofEdgeFun G k) = A then (1 : ℝ) else 0) * weight G β J (ofEdgeFun G p))
  rw [show (∑ K : {p_1 : ↥G.edgeFinset → ℕ // ∀ e, p_1 e ≤ p e},
        (∏ e, (p e).choose (K.1 e)) •
          ((if Sharpness.sources G (ofEdgeFun G K.1) = A then (1 : ℝ) else 0)
            * weight G β J (ofEdgeFun G p)))
      = ∑ K : {p_1 : ↥G.edgeFinset → ℕ // p_1 ≤ p},
        (∏ e, (p e).choose (K.1 e)) •
          ((if Sharpness.sources G (ofEdgeFun G K.1) = A then (1 : ℝ) else 0)
            * weight G β J (ofEdgeFun G p)) from rfl]
  rw [hbridge, Finset.card_filter]
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [← sources_eq G p S]









theorem gc22_count_collapse {ι : Type*} [DecidableEq ι] [Fintype ι] (ends : ι → Sym2 V)
    (hnd : ∀ i, ¬ (ends i).IsDiag) (A : Finset V) {u v : V} (huv : u ≠ v)
    (hconn : connK ends (univ : Finset ι) u v) :
    #((univ : Finset (Finset ι)).filter (fun K => RandomCurrent.sources ends K = A ∆ {u, v}))
      = #((univ : Finset (Finset ι)).filter (fun K => RandomCurrent.sources ends K = A)) := by
  obtain ⟨P, hPsub, hPsrc⟩ := exists_conn_set ends (univ : Finset ι) hconn huv
  have hbij := sources_shift_bijOn ends (univ : Finset ι) P (by simp) A
  rw [hPsrc] at hbij
  have hset : ((univ : Finset (Finset ι)).filter
        (fun K => RandomCurrent.sources ends K = A ∆ {u, v}))
      = ((univ : Finset (Finset ι)).filter (fun K => RandomCurrent.sources ends K = A)).image
          (fun K => K ∆ P) := by
    ext K
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hKsrc
      obtain ⟨L, hL, hLK⟩ := hbij.2.2 ⟨by simp, hKsrc⟩
      exact ⟨L, hL.2, hLK⟩
    · rintro ⟨L, hLsrc, rfl⟩
      exact (hbij.1 ⟨by simp, hLsrc⟩).2
  rw [hset, Finset.card_image_of_injOn]
  intro K₁ hK₁ K₂ hK₂ h
  simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hK₁ hK₂
  exact hbij.2.1 ⟨by simp, hK₁⟩ ⟨by simp, hK₂⟩ h












theorem gc22_splitWeightedSum_switch_pos (β : ℝ) (J : Sym2 V → ℝ) (p : ↥G.edgeFinset → ℕ)
    (A : Finset V) {u v : V} (huv : u ≠ v)
    (hpos : connP (posEdges G.edgeFinset (ofEdgeFun G p)) u v) :
    splitWeightedSum G β J (ofEdgeFun G p) 1 (A ∆ {u, v})
      = splitWeightedSum G β J (ofEdgeFun G p) 1 A := by
  rw [gc22_splitWeightedSum_eq_edgecopy_count G β J p (A ∆ {u, v}),
      gc22_splitWeightedSum_eq_edgecopy_count G β J p A]
  have hconnK : connK (endsM G p) (univ : Finset (Copy G p)) u v := by
    rw [connK_univ_iff G p u v, ← gc20_connP_posEdges_iff_currentConnected]; exact hpos
  rw [gc22_count_collapse (endsM G p) (fun i => endsM_not_isDiag G p i) A huv hconnK]






theorem gc22_hnw_mass_collapse_pos (β : ℝ) (J : Sym2 V → ℝ) (p : ↥G.edgeFinset → ℕ)
    {u v : V} (huv : u ≠ v)
    (hpos : connP (posEdges G.edgeFinset (ofEdgeFun G p)) u v) :
    hnw_mass G β J (ofEdgeFun G p) {u, v} = hnw_mass G β J (ofEdgeFun G p) ∅ := by
  unfold hnw_mass
  have h := gc22_splitWeightedSum_switch_pos G β J p ∅ huv hpos
  rwa [show (∅ : Finset V) ∆ {u, v} = {u, v} from by simp] at h

















theorem gc22_fibre_starGap_nonpos_pos (β : ℝ) (J : Sym2 (Option V) → ℝ) (hβ : 0 ≤ β)
    (hJ : ∀ e, 0 ≤ J e) (p : ↥(withGhost G).edgeFinset → ℕ) {o x y : V}
    (hog : (some o : Option V) ≠ none) (hoxs : (some o : Option V) ≠ some x)
    (hoys : (some o : Option V) ≠ some y)
    (Hg : ¬ connP (posEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) p)) (some o) none)
    (Harc : connP (posEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) p)) (some o) (some x)
        ∨ connP (posEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) p)) (some o) (some y)) :
    hnw_mass (withGhost G) β J (ofEdgeFun (withGhost G) p) ∅
        - hnw_mass (withGhost G) β J (ofEdgeFun (withGhost G) p) {some o, none}
        - hnw_mass (withGhost G) β J (ofEdgeFun (withGhost G) p) {some o, some x}
        - hnw_mass (withGhost G) β J (ofEdgeFun (withGhost G) p) {some o, some y} ≤ 0 := by
  have eg : hnw_mass (withGhost G) β J (ofEdgeFun (withGhost G) p) {some o, none} = 0 :=
    gc18_star_mass_vanish (withGhost G) β J (ofEdgeFun (withGhost G) p)
      (gc20_withGhost_loopless G) hog Hg
  have bx : 0 ≤ hnw_mass (withGhost G) β J (ofEdgeFun (withGhost G) p) {some o, some x} :=
    hnw_mass_nonneg (withGhost G) β J hβ hJ _ _
  have by' : 0 ≤ hnw_mass (withGhost G) β J (ofEdgeFun (withGhost G) p) {some o, some y} :=
    hnw_mass_nonneg (withGhost G) β J hβ hJ _ _
  rcases Harc with Hx | Hy
  · rw [eg, gc22_hnw_mass_collapse_pos (withGhost G) β J p hoxs Hx]; linarith
  · rw [eg, gc22_hnw_mass_collapse_pos (withGhost G) β J p hoys Hy]; linarith













theorem gc22_fibre_arc_of_disc (m : ↥(withGhost G).edgeFinset → ℕ)
    (K₂ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e}) {o x y : V}
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hbdry : sources (withGhost G) (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e))
        = ({some o, some x, some y, none} : Finset (Option V)))
    (Hg : ¬ connP (posEdges (withGhost G).edgeFinset
        (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e))) (some o) none) :
    connP (posEdges (withGhost G).edgeFinset
          (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e))) (some o) (some x)
      ∨ connP (posEdges (withGhost G).edgeFinset
          (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e))) (some o) (some y) := by
  have hoxs : (some o : Option V) ≠ some x := by simpa using hox
  have hoys : (some o : Option V) ≠ some y := by simpa using hoy
  have hxys : (some x : Option V) ≠ some y := by simpa using hxy
  have hog : (some o : Option V) ≠ none := by simp
  have hxgs : (some x : Option V) ≠ none := by simp
  have hygs : (some y : Option V) ≠ none := by simp
  have htri := gc21_fibre_posTrichotomy G m K₂ (some o) (some x) (some y) none
    hoxs hoys hog hxys hxgs hygs hbdry
  rcases htri with hOg | hp1 | hp2
  · exact absurd hOg Hg
  · exact Or.inl hp1.1
  · exact Or.inr hp2.1







theorem gc22_firstFour_nonpos_of_fullDisc (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (m : ↥(withGhost G).edgeFinset → ℕ)
    (hbdry : sources (withGhost G) (ofEdgeFun (withGhost G) m)
        = ({some o, some x, some y, none} : Finset (Option V)))
    (hdiscG : ¬ connP (posEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) m))
        (some o) none) :
    gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ ∅
        - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, none}
        - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some x}
        - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some y} ≤ 0 := by
  have hog : (some o : Option V) ≠ none := by simp
  have hoxs : (some o : Option V) ≠ some x := by simpa using hox
  have hoys : (some o : Option V) ≠ some y := by simpa using hoy
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
    have hfibreDisc : ¬ connP (posEdges (withGhost G).edgeFinset
        (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e))) (some o) none :=
      gc20_fiber_disc_of_disc G m K₂ hdiscG
    have hArc := gc22_fibre_arc_of_disc G m K₂ hox hoy hxy hinner hfibreDisc
    have hsg := gc22_fibre_starGap_nonpos_pos G β (ghostCoupling h β (fun _ => 1)) hβ hJnn
      (fun e => m e - K₂.1 e) hog hoxs hoys hfibreDisc hArc
    exact mul_nonpos_of_nonneg_of_nonpos hw hsg
  · rw [if_neg hK₂, zero_mul]












theorem gc22_cert_nonpos_of_fullDisc (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (m : ↥(withGhost G).edgeFinset → ℕ)
    (hbdry : sources (withGhost G) (ofEdgeFun (withGhost G) m)
        = ({some o, some x, some y, none} : Finset (Option V)))
    (hdiscG : ¬ connP (posEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) m))
        (some o) none) :
    gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ ∅
        - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, none}
        - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some x}
        - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some y}
        + 2 * gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m
              {some o, none} {some x, none} ≤ 0 := by
  have hog : (some o : Option V) ≠ none := by simp
  rw [gc20_fifth_vanish_of_disc G β h o x y hog m hdiscG]
  have h4 := gc22_firstFour_nonpos_of_fullDisc G β h hβ hh o x y hox hoy hxy m hbdry hdiscG
  linarith


























def gc22_AllConnResidue (β h : ℝ) (o x y : V) : Prop :=
  ∀ m : ↥(withGhost G).edgeFinset → ℕ,
    sources (withGhost G) (ofEdgeFun (withGhost G) m)
        = ({some o, some x, some y, none} : Finset (Option V)) →
    connP (posEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) m)) (some o) none →
      gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ ∅
        - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, none}
        - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some x}
        - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some y}
        + 2 * gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m
              {some o, none} {some x, none} ≤ 0






theorem gc22_cert_of_allConnResidue (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hres : gc22_AllConnResidue G β h o x y) :
    gc16_PerConfigCert G β h o x y := by
  intro m hm
  by_cases hOg : connP (posEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) m)) (some o) none
  · exact hres m hm hOg
  · exact gc22_cert_nonpos_of_fullDisc G β h hβ hh o x y hox hoy hxy m hm hOg







theorem gc22_ursell_nonpos_of_allConnResidue (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hres : gc22_AllConnResidue G β h o x y) :
    eg_ursell3 G β h o x y ≤ 0 :=
  gc16_cert_closes_u3 G β h o x y hox hoy hxy
    (gc22_cert_of_allConnResidue G β h hβ hh o x y hox hoy hxy hres)




theorem gc22_ghs_of_allConnResidue (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V)
    (hres : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → gc22_AllConnResidue G β h o x y) :
    GHSThreePointSym G β h o :=
  gc16_ghs_of_cert G β h hβ hh o
    (fun x y hox hoy hxy =>
      gc22_cert_of_allConnResidue G β h hβ hh o x y hox hoy hxy (hres x y hox hoy hxy))




theorem gc22_aizenman_barsky_of_allConnResidue (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V) (J : ℝ)
    (hres : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → gc22_AllConnResidue G β h o x y)
    (hfactor : ∑ e ∈ G.edgeFinset, ghsBoundSym G β h o e
        = J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o) :
    bondEnergySusceptibility G β h o
      ≤ J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o :=
  gc16_aizenman_barsky_of_cert G β h hβ hh o J
    (fun x y hox hoy hxy =>
      gc22_cert_of_allConnResidue G β h hβ hh o x y hox hoy hxy (hres x y hox hoy hxy))
    hfactor

end StatMech.Walls
