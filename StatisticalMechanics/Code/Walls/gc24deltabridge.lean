/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/









































































import Mathlib
import Code.Walls.gc23allconn
import Code.Walls.gc22edgecopy
import Code.Walls.gc15core
import Code.Walls.gc10deltasupport
import Code.Walls.gc10ensembleprob
import Code.Sharpness.DeltaRewriteDichotomy
import Code.Sharpness.GhostCurrentRep
import Code.Sharpness.FluxEdgeCopyBridge
import Code.Ising.CurrentWeight
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













noncomputable def gc24_fibreCount (p : ↥G.edgeFinset → ℕ) (A : Finset V) : ℕ :=
  #((univ : Finset (Finset (Copy G p))).filter
      (fun S => RandomCurrent.sources (endsM G p) S = A))








theorem gc24_splitWeightedSum_eq_fibreCount (β : ℝ) (J : Sym2 V → ℝ)
    (p : ↥G.edgeFinset → ℕ) (A : Finset V) :
    splitWeightedSum G β J (ofEdgeFun G p) 1 A
      = (gc24_fibreCount G p A : ℝ) * weight G β J (ofEdgeFun G p) :=
  gc22_splitWeightedSum_eq_edgecopy_count G β J p A












theorem gc24_tpsum_eq_fibreCount (β : ℝ) (J : Sym2 V → ℝ) (m : ↥G.edgeFinset → ℕ) (A B : Finset V) :
    gc15_tpsum G β J m A B
      = ∑ K₂ : {K : ↥G.edgeFinset → ℕ // ∀ e, K e ≤ m e},
          (if sources G (ofEdgeFun G K₂.1) = B then weight G β J (ofEdgeFun G K₂.1) else 0)
            * ((gc24_fibreCount G (fun e => m e - K₂.1 e) A : ℝ)
              * weight G β J (ofEdgeFun G (fun e => m e - K₂.1 e))) := by
  rw [gc16_tpsum_bridge G β J m A B]
  refine Finset.sum_congr rfl (fun K₂ _ => ?_)
  rw [gc24_splitWeightedSum_eq_fibreCount G β J (fun e => m e - K₂.1 e) A]






















theorem gc24_fibreCount_backbone (p : ↥G.edgeFinset → ℕ) (A : Finset V) {o x y : V}
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hm : RandomCurrent.sources (endsM G p) (univ : Finset (Copy G p)) = A) :
    ((gc24_fibreCount G p A : ℝ)
        - (gc24_fibreCount G p (A ∆ {x, y}) : ℝ)
        - (gc24_fibreCount G p (A ∆ {o, y}) : ℝ)
        - (gc24_fibreCount G p (A ∆ {o, x}) : ℝ))
      = (gc24_fibreCount G p A : ℝ)
        * (1 - (if connK (endsM G p) (univ : Finset (Copy G p)) x y then 1 else 0)
             - (if connK (endsM G p) (univ : Finset (Copy G p)) o y then 1 else 0)
             - (if connK (endsM G p) (univ : Finset (Copy G p)) o x then 1 else 0)) := by
  have h := asd_ghsSigned_eq (endsM G p) (univ : Finset (Copy G p))
    (fun i _ => endsM_not_isDiag G p i) A hm hox hoy hxy (fun _ => (1 : ℝ))
    (fun _ _ _ _ => rfl)
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h
  
  have hpow : ∀ (S : Finset V),
      #((univ : Finset (Finset (Copy G p))).filter
          (fun K => RandomCurrent.sources (endsM G p) K = S))
        = #((univ.powerset : Finset (Finset (Copy G p))).filter
            (fun K => RandomCurrent.sources (endsM G p) K = S)) := by
    intro S; rw [Finset.powerset_univ]
  unfold gc24_fibreCount
  rw [hpow A, hpow (A ∆ {x, y}), hpow (A ∆ {o, y}), hpow (A ∆ {o, x})]
  exact_mod_cast h























theorem gc24_sourcePairDisconnSum_nonneg (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (A B : Finset V) (u v : V) :
    0 ≤ sourcePairDisconnSum G β J A B u v := by
  rw [sourcePairDisconnSum_eq_edgecopy G β J A B u v]
  refine tsum_nonneg (fun m => mul_nonneg (Finset.sum_nonneg (fun S _ => ?_)) ?_)
  · refine mul_nonneg (mul_nonneg ?_ ?_) ?_ <;> positivity
  · exact acw_weight_nonneg G β J hβ hJ _













theorem gc24_switchingGap_nonneg (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (A : Finset V) {u v : V} (huv : u ≠ v) :
    currentSum G β J (A ∆ {u, v}) * currentSum G β J {u, v}
      ≤ currentSum G β J A * currentSum G β J ∅ := by
  have hid := GhostCurrentRep.gcr_currentSum_ghostRep G β J A huv
  have hnn := gc24_sourcePairDisconnSum_nonneg G β J hβ hJ A ∅ u v
  linarith [hid, hnn]























theorem gc24_three_switchingGaps_nonneg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    (currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ({some o, none} : Finset (Option V))
        * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some x, some y}
      ≤ currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
          {some o, some x, some y, none}
        * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅)
    ∧ (currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some o, some x}
        * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some y, none}
      ≤ currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
          {some o, some x, some y, none}
        * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅)
    ∧ (currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some o, some y}
        * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some x, none}
      ≤ currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
          {some o, some x, some y, none}
        * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅) := by
  have hJnn : ∀ e, (0 : ℝ) ≤ ghostCoupling h β (fun _ => 1) e :=
    gc6_ghostCoupling_nonneg (V := V) β h hh
  set J' := ghostCoupling h β (fun _ : Sym2 V => (1 : ℝ)) with hJ'
  obtain ⟨dOX, dOY, dOg, dXY, dXg, dYg⟩ := gc15_marks_distinct hox hoy hxy
  refine ⟨?_, ?_, ?_⟩
  · 
    have hg := gc24_switchingGap_nonneg (withGhost G) β J' hβ hJnn
      ({some o, some x, some y, none} : Finset (Option V)) (u := some x) (v := some y) dXY
    have hsd : ({some o, some x, some y, none} : Finset (Option V)) ∆ {some x, some y}
        = {some o, none} := by
      ext a
      simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
      by_cases h1 : a = some o <;> by_cases h2 : a = some x <;> by_cases h3 : a = some y <;>
        by_cases h4 : a = (none : Option V) <;> subst_vars <;> simp_all
    rw [hsd] at hg; exact hg
  · 
    have hg := gc24_switchingGap_nonneg (withGhost G) β J' hβ hJnn
      ({some o, some x, some y, none} : Finset (Option V)) (u := some y) (v := none) (by simp)
    have hsd : ({some o, some x, some y, none} : Finset (Option V)) ∆ {some y, none}
        = {some o, some x} := by
      ext a
      simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
      by_cases h1 : a = some o <;> by_cases h2 : a = some x <;> by_cases h3 : a = some y <;>
        by_cases h4 : a = (none : Option V) <;> subst_vars <;> simp_all
    rw [hsd] at hg; exact hg
  · 
    have hg := gc24_switchingGap_nonneg (withGhost G) β J' hβ hJnn
      ({some o, some x, some y, none} : Finset (Option V)) (u := some x) (v := none) (by simp)
    have hsd : ({some o, some x, some y, none} : Finset (Option V)) ∆ {some x, none}
        = {some o, some y} := by
      ext a
      simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
      by_cases h1 : a = some o <;> by_cases h2 : a = some x <;> by_cases h3 : a = some y <;>
        by_cases h4 : a = (none : Option V) <;> subst_vars <;> simp_all
    rw [hsd] at hg; exact hg





























def gc24_ThreeReplicaResummation (β h : ℝ) (o x y : V) : Prop :=
  ∃ (ι : Type) (_ : DecidableEq ι) (_ : Fintype ι) (ends : ι → Sym2 (Option V))
    (F : Finset ι → ℝ),
      (∀ m, 0 ≤ F m)
      ∧ (∀ i, ¬ (ends i).IsDiag)
      ∧ (∀ m : Finset ι, (¬ connK ends m (some o) none) →
            RandomCurrent.sources ends m = {some o, some x, some y, none})
      ∧ (∑' m, gc15_threeGap G β h o x y m)
          = -2 * gc10_allConnMass ends (some o) (some x) (some y) none F








theorem gc24_ursell_nonpos_of_threeReplicaResummation (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hres : gc24_ThreeReplicaResummation G β h o x y) :
    eg_ursell3 G β h o x y ≤ 0 := by
  obtain ⟨ι, _, _, ends, F, hF, hnd, hsrc, hid⟩ := hres
  have hZ : 0 < gc15_Z0 G β h := gc15_Z0_pos G β h
  have hN : 0 ≤ gc10_allConnMass ends (some o) (some x) (some y) none F :=
    gc10_allConnMass_nonneg ends (some o) (some x) (some y) none F hF
  have hsum : ∑' m, gc15_threeGap G β h o x y m ≤ 0 := by rw [hid]; nlinarith [hN]
  have hpoly : (gc15_Z0 G β h) ^ 3 * eg_ursell3 G β h o x y ≤ 0 := by
    rw [gc15_u3_eq_tsum_threeGap G β h o x y hox hoy hxy]; exact hsum
  nlinarith [pow_pos hZ 3, hpoly]






theorem gc24_ghs_of_threeReplicaResummation (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V)
    (hres : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → gc24_ThreeReplicaResummation G β h o x y) :
    GHSThreePointSym G β h o := by
  rw [ghc_ghsSym_iff_ursell_nonpos]
  intro x y he
  have hxy : x ≠ y := by rw [SimpleGraph.mem_edgeFinset] at he; exact G.ne_of_adj he
  by_cases hox : o = x
  · subst hox
    exact ghc_ursell_nonpos_degenerate G β h hβ hh o y hxy
  · by_cases hoy : o = y
    · subst hoy
      rw [ghc_ursell_swap]
      exact ghc_ursell_nonpos_degenerate G β h hβ hh o x hox
    · exact gc24_ursell_nonpos_of_threeReplicaResummation G β h o x y hox hoy hxy
        (hres x y hox hoy hxy)




theorem gc24_aizenman_barsky_of_threeReplicaResummation (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (o : V) (J : ℝ)
    (hres : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → gc24_ThreeReplicaResummation G β h o x y)
    (hfactor : ∑ e ∈ G.edgeFinset, ghsBoundSym G β h o e
        = J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o) :
    bondEnergySusceptibility G β h o
      ≤ J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o :=
  aizenman_barsky_inequality G β h o J
    (gc24_ghs_of_threeReplicaResummation G β h hβ hh o hres) hfactor















theorem gc24_backbone_not_signDefinite {ι : Type*} [DecidableEq ι] [Fintype ι]
    (ends : ι → Sym2 (Option V)) (m₁ m₂ : Finset ι) {o x y : V}
    (h₁ : connK ends m₁ (some x) (some y) ∧ connK ends m₁ (some o) (some y)
        ∧ connK ends m₁ (some o) (some x))
    (h₂ : ¬ connK ends m₂ (some x) (some y) ∧ ¬ connK ends m₂ (some o) (some y)
        ∧ ¬ connK ends m₂ (some o) (some x)) :
    asd_ghsBackboneFactor ends m₁ (some o) (some x) (some y) < 0
      ∧ 0 < asd_ghsBackboneFactor ends m₂ (some o) (some x) (some y) :=
  asd_ghsBackboneFactor_not_signDefinite ends m₁ m₂ h₁ h₂






theorem gc24_allConnMass_eq_caseA_plus_caseB {ι : Type*} [DecidableEq ι] [Fintype ι]
    (ends : ι → Sym2 (Option V)) (F : Finset ι → ℝ) {o x y : V}
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hnd : ∀ i, ¬ (ends i).IsDiag)
    (hsrcSet : ∀ m : Finset ι, (¬ connK ends m (some o) none) →
        sources ends m = {some o, some x, some y, none}) :
    gc10_allConnMass ends (some o) (some x) (some y) none F
      = drd_pairSum ends ({some o, some x, some y, none} : Finset (Option V)) F
          (fun m => gc8_caseA ends (some o) (some x) (some y) none m)
        + drd_pairSum ends ({some o, some x, some y, none} : Finset (Option V)) F
          (fun m => gc8_caseB ends (some o) (some x) (some y) none m) :=
  gc10_allConnMass_eq_caseA_plus_caseB ends F (by simpa using hox) (by simpa using hoy) (by simp)
    (by simpa using hxy) (by simp) (by simp) hnd hsrcSet

end StatMech.Walls
