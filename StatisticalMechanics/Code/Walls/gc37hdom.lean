/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


















































































import Mathlib
import Code.Walls.gc24deltabridge
import Code.Walls.gc28ghsrigid
import Code.Walls.ghc_urselleqgap
import Code.Walls.FaithfulnessAudit
import Code.Ising.CurrentWeight

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
open StatMech.Walls.Gc5EqGap StatMech.Walls.GhcEqGap
open StatMech.Sharpness.FluxEdgeCopy
open StatMech.Sharpness.FieldGhostDict

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]



















noncomputable def gc37_U4 (β h : ℝ) (o x y : V) : ℝ :=
  isingExpectation G β h (fun s => spin s o * (spin s x * spin s y))
    - isingExpectation G β h (fun s => spin s o)
        * isingExpectation G β h (fun s => spin s x * spin s y)
    - isingExpectation G β h (fun s => spin s o * spin s x)
        * isingExpectation G β h (fun s => spin s y)
    - isingExpectation G β h (fun s => spin s o * spin s y)
        * isingExpectation G β h (fun s => spin s x)




noncomputable def gc37_triple (β h : ℝ) (o x y : V) : ℝ :=
  isingExpectation G β h (fun s => spin s o)
    * isingExpectation G β h (fun s => spin s x)
    * isingExpectation G β h (fun s => spin s y)










theorem gc37_ursell3_eq_U4_add_triple (β h : ℝ) (o x y : V) :
    eg_ursell3 G β h o x y = gc37_U4 G β h o x y + 2 * gc37_triple G β h o x y := by
  unfold eg_ursell3 gc37_U4 gc37_triple
  ring




theorem gc37_onePt_nonneg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (x : V) :
    0 ≤ isingExpectation G β h (fun s => spin s x) := by
  have hgks := gks_first G β h hβ hh {x}
  have hrw : (fun s => spin s x) = spinProd ({x} : Finset V) := by
    funext s; unfold spinProd; rw [Finset.prod_singleton]
  rw [hrw]; exact hgks





theorem gc37_triple_nonneg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V) :
    0 ≤ gc37_triple G β h o x y := by
  unfold gc37_triple
  exact mul_nonneg (mul_nonneg (gc37_onePt_nonneg G β h hβ hh o) (gc37_onePt_nonneg G β h hβ hh x))
    (gc37_onePt_nonneg G β h hβ hh y)















noncomputable def gc37_sourcePairConnSum (β : ℝ) (J : Sym2 V → ℝ) (A B : Finset V) (u v : V) : ℝ :=
  ∑' pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ),
    ((if sources G (ofEdgeFun G pq.1) = A then weight G β J (ofEdgeFun G pq.1) else 0)
        * (if sources G (ofEdgeFun G pq.2) = B then weight G β J (ofEdgeFun G pq.2) else 0))
      * (if CurrentConnected G (ofEdgeFun G (fun e => pq.1 e + pq.2 e)) u v then 1 else 0)







theorem gc37_sourcePairSum_conn_add_disconn (β : ℝ) (J : Sym2 V → ℝ) (A B : Finset V) (u v : V) :
    sourcePairSum G β J A B
      = gc37_sourcePairConnSum G β J A B u v
        + sourcePairDisconnSum G β J A B u v := by
  classical
  unfold sourcePairSum gc37_sourcePairConnSum sourcePairDisconnSum
  set f : (↥G.edgeFinset → ℕ) → ℝ :=
    fun p => if sources G (ofEdgeFun G p) = A then weight G β J (ofEdgeFun G p) else 0 with hf
  set g : (↥G.edgeFinset → ℕ) → ℝ :=
    fun q => if sources G (ofEdgeFun G q) = B then weight G β J (ofEdgeFun G q) else 0 with hg
  
  have hfg : Summable (fun z : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) => f z.1 * g z.2) :=
    summable_mul_of_summable_norm
      (summable_norm_currentSum_summand G β J A) (summable_norm_currentSum_summand G β J B)
  
  have hbound : ∀ (W : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) → ℝ),
      (∀ z, |W z| ≤ 1) →
      Summable (fun z : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) => (f z.1 * g z.2) * W z) := by
    intro W hW
    apply Summable.of_norm
    apply (hfg.norm).of_nonneg_of_le (fun _ => norm_nonneg _) (fun z => ?_)
    rw [norm_mul]
    calc ‖f z.1 * g z.2‖ * ‖W z‖ ≤ ‖f z.1 * g z.2‖ * 1 := by
            apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); rw [Real.norm_eq_abs]; exact hW z
      _ = ‖f z.1 * g z.2‖ := mul_one _
  have hconn := hbound
    (fun z => if CurrentConnected G (ofEdgeFun G (fun e => z.1 e + z.2 e)) u v then 1 else 0)
    (fun z => by
      by_cases h : CurrentConnected G (ofEdgeFun G (fun e => z.1 e + z.2 e)) u v <;> simp [h])
  have hdisc := hbound
    (fun z => if ¬ CurrentConnected G (ofEdgeFun G (fun e => z.1 e + z.2 e)) u v then 1 else 0)
    (fun z => by
      by_cases h : CurrentConnected G (ofEdgeFun G (fun e => z.1 e + z.2 e)) u v <;> simp [h])
  rw [← Summable.tsum_add hconn hdisc]
  refine tsum_congr (fun z => ?_)
  simp only [hf, hg]
  by_cases h : CurrentConnected G (ofEdgeFun G (fun e => z.1 e + z.2 e)) u v <;>
    simp only [h, not_true_eq_false, not_false_eq_true, if_true, if_false, mul_one, mul_zero,
      add_zero, zero_add]






theorem gc37_sourcePairConnSum_nonneg (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (A B : Finset V) (u v : V) : 0 ≤ gc37_sourcePairConnSum G β J A B u v := by
  unfold gc37_sourcePairConnSum
  refine tsum_nonneg (fun z => ?_)
  refine mul_nonneg (mul_nonneg ?_ ?_) ?_
  · by_cases h : sources G (ofEdgeFun G z.1) = A
    · simp only [h, if_true]; exact acw_weight_nonneg G β J hβ hJ _
    · simp [h]
  · by_cases h : sources G (ofEdgeFun G z.2) = B
    · simp only [h, if_true]; exact acw_weight_nonneg G β J hβ hJ _
    · simp [h]
  · by_cases h : CurrentConnected G (ofEdgeFun G (fun e => z.1 e + z.2 e)) u v <;> simp [h]










private noncomputable def csG (β h : ℝ) (A : Finset (Option V)) : ℝ :=
  currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) A









theorem gc37_Z0cubed_triple (β h : ℝ) (o x y : V) :
    (gc15_Z0 G β h) ^ 3 * gc37_triple G β h o x y
      = csG G β h (insert (none : Option V) (({o} : Finset V).map someEmb))
        * csG G β h (insert (none : Option V) (({x} : Finset V).map someEmb))
        * csG G β h (insert (none : Option V) (({y} : Finset V).map someEmb)) := by
  unfold gc37_triple csG
  rw [gc8_eq15_insertion_ghost G β (ghostCoupling h β (fun _ => 1))
        (insert (none : Option V) (({o} : Finset V).map someEmb)),
      gc8_eq15_insertion_ghost G β (ghostCoupling h β (fun _ => 1))
        (insert (none : Option V) (({x} : Finset V).map someEmb)),
      gc8_eq15_insertion_ghost G β (ghostCoupling h β (fun _ => 1))
        (insert (none : Option V) (({y} : Finset V).map someEmb)),
      gc10_moment_ghostSingle G β h o, gc10_moment_ghostSingle G β h x,
      gc10_moment_ghostSingle G β h y]
  unfold gc15_Z0
  ring








theorem gc37_Z0sq_U4 (β h : ℝ) (o x y : V) (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    (gc15_Z0 G β h) ^ 2 * gc37_U4 G β h o x y
      = (gc15_Z0 G β h) * csG G β h (insert (none : Option V) (({o, x, y} : Finset V).map someEmb))
        - csG G β h (insert (none : Option V) (({o} : Finset V).map someEmb))
            * csG G β h (({x, y} : Finset V).map someEmb)
        - csG G β h (({o, x} : Finset V).map someEmb)
            * csG G β h (insert (none : Option V) (({y} : Finset V).map someEmb))
        - csG G β h (({o, y} : Finset V).map someEmb)
            * csG G β h (insert (none : Option V) (({x} : Finset V).map someEmb)) := by
  have hpoly := gc15_u3_currentSum_poly G β h o x y hox hoy hxy
  have hdecomp := gc37_ursell3_eq_U4_add_triple G β h o x y
  have htriple := gc37_Z0cubed_triple G β h o x y
  have hZpos : 0 < gc15_Z0 G β h := gc15_Z0_pos G β h
  have hZne : gc15_Z0 G β h ≠ 0 := ne_of_gt hZpos
  
  rw [hdecomp] at hpoly
  unfold csG
  unfold csG at htriple
  
  
  have key : gc15_Z0 G β h * ((gc15_Z0 G β h) ^ 2 * gc37_U4 G β h o x y)
      = gc15_Z0 G β h *
        ((gc15_Z0 G β h) * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
              (insert (none : Option V) (({o, x, y} : Finset V).map someEmb))
          - currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
              (insert (none : Option V) (({o} : Finset V).map someEmb))
              * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
                  (({x, y} : Finset V).map someEmb)
          - currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
              (({o, x} : Finset V).map someEmb)
              * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
                  (insert (none : Option V) (({y} : Finset V).map someEmb))
          - currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
              (({o, y} : Finset V).map someEmb)
              * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
                  (insert (none : Option V) (({x} : Finset V).map someEmb))) := by
    linear_combination hpoly - 2 * htriple
  exact mul_left_cancel₀ hZne key


















def gc37_U4a_connRep (β h : ℝ) (o x y : V) : Prop :=
  (gc15_Z0 G β h) ^ 2 * gc37_U4 G β h o x y
    = -2 * gc37_sourcePairConnSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
        ({some o, some x} : Finset (Option V)) ({some y, none} : Finset (Option V))
        (some o) (some y)










theorem gc37_U4_nonpos_of_connRep (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hrep : gc37_U4a_connRep G β h o x y) :
    gc37_U4 G β h o x y ≤ 0 := by
  unfold gc37_U4a_connRep at hrep
  have hZpos : 0 < gc15_Z0 G β h := gc15_Z0_pos G β h
  have hZ2 : 0 < (gc15_Z0 G β h) ^ 2 := by positivity
  have hJnn : ∀ e, (0 : ℝ) ≤ ghostCoupling h β (fun _ => 1) e :=
    gc6_ghostCoupling_nonneg (V := V) β h hh
  have hconn := gc37_sourcePairConnSum_nonneg (withGhost G) β (ghostCoupling h β (fun _ => 1))
    hβ hJnn ({some o, some x} : Finset (Option V)) ({some y, none} : Finset (Option V))
    (some o) (some y)
  
  nlinarith [hrep, hconn, hZ2]




















theorem gc37_twoReplica_U4_insufficient :
    ∃ a b : ℝ, a ≤ 0 ∧ 0 ≤ b ∧ 0 < a + 2 * b := by
  exact ⟨-1, 1, by norm_num, by norm_num, by norm_num⟩










theorem gc37_ursell3_nonpos_iff_sharp (β h : ℝ) (o x y : V) :
    eg_ursell3 G β h o x y ≤ 0
      ↔ gc37_U4 G β h o x y ≤ -2 * gc37_triple G β h o x y := by
  rw [gc37_ursell3_eq_U4_add_triple]
  constructor
  · intro hle; linarith
  · intro hle; linarith






theorem gc37_ursell3_nonpos_of_sharp (β h : ℝ) (o x y : V)
    (hsharp : gc37_U4 G β h o x y ≤ -2 * gc37_triple G β h o x y) :
    eg_ursell3 G β h o x y ≤ 0 :=
  (gc37_ursell3_nonpos_iff_sharp G β h o x y).mpr hsharp














theorem gc37_U4_eq_neg_two_triple_at_zero (β : ℝ) (o x y : V) :
    gc37_U4 G β 0 o x y = -2 * gc37_triple G β 0 o x y := by
  have h0 := fa_ghs_ursell3_h0_eq_zero G β o x y
  have hdecomp := gc37_ursell3_eq_U4_add_triple G β 0 o x y
  rw [h0] at hdecomp
  linarith

end StatMech.Walls
