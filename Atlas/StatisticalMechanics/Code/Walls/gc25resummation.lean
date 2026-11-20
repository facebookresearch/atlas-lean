/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













































































import Mathlib
import Code.Walls.gc24deltabridge
import Code.Walls.gc15core
import Code.Walls.gc10deltasupport
import Code.Walls.gc10ensembleprob
import Code.Walls.gc9core
import Code.Sharpness.DeltaRewriteDichotomy
import Code.Sharpness.GhostCurrentRep
import Code.Sharpness.FluxEdgeCopyBridge
import Code.Sharpness.SwitchingDichotomy
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

















noncomputable def gc25_nativeAllConnMass (β h : ℝ) (o x y : V) : ℝ :=
  sourcePairDisconnSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
    (insert (none : Option V) (({o, x, y} : Finset V).map someEmb)) ∅ (some o) none







theorem gc25_nativeAllConnMass_nonneg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V) :
    0 ≤ gc25_nativeAllConnMass G β h o x y := by
  unfold gc25_nativeAllConnMass
  exact gc24_sourcePairDisconnSum_nonneg (withGhost G) β (ghostCoupling h β (fun _ => 1)) hβ
    (gc6_ghostCoupling_nonneg (V := V) β h hh) _ _ _ _




















def gc25_NativeResummation (β h : ℝ) (o x y : V) : Prop :=
  (∑' m, gc15_threeGap G β h o x y m) = -2 * gc25_nativeAllConnMass G β h o x y







theorem gc25_ursell_nonpos_of_nativeResummation (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hres : gc25_NativeResummation G β h o x y) :
    eg_ursell3 G β h o x y ≤ 0 := by
  have hZ : 0 < gc15_Z0 G β h := gc15_Z0_pos G β h
  have hN : 0 ≤ gc25_nativeAllConnMass G β h o x y := gc25_nativeAllConnMass_nonneg G β h hβ hh o x y
  have hsum : ∑' m, gc15_threeGap G β h o x y m ≤ 0 := by rw [hres]; nlinarith [hN]
  have hpoly : (gc15_Z0 G β h) ^ 3 * eg_ursell3 G β h o x y ≤ 0 := by
    rw [gc15_u3_eq_tsum_threeGap G β h o x y hox hoy hxy]; exact hsum
  nlinarith [pow_pos hZ 3, hpoly]





theorem gc25_ghs_of_nativeResummation (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V)
    (hres : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → gc25_NativeResummation G β h o x y) :
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
    · exact gc25_ursell_nonpos_of_nativeResummation G β h hβ hh o x y hox hoy hxy
        (hres x y hox hoy hxy)




theorem gc25_aizenman_barsky_of_nativeResummation (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (o : V) (J : ℝ)
    (hres : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → gc25_NativeResummation G β h o x y)
    (hfactor : ∑ e ∈ G.edgeFinset, ghsBoundSym G β h o e
        = J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o) :
    bondEnergySusceptibility G β h o
      ≤ J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o :=
  aizenman_barsky_inequality G β h o J
    (gc25_ghs_of_nativeResummation G β h hβ hh o hres) hfactor
















theorem gc25_leadingGap_eq_disconnSum (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
          ({some o, some x, some y, none} : Finset (Option V))
        * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅
      - currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some o, none}
        * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some x, some y}
      = sourcePairDisconnSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
          ({some o, some x, some y, none} : Finset (Option V)) ∅ (some x) (some y) := by
  set J' := ghostCoupling h β (fun _ : Sym2 V => (1 : ℝ)) with hJ'
  obtain ⟨dOX, dOY, dOg, dXY, dXg, dYg⟩ := gc15_marks_distinct hox hoy hxy
  have hid := GhostCurrentRep.gcr_currentSum_ghostRep (withGhost G) β J'
    ({some o, some x, some y, none} : Finset (Option V)) (u := some x) (v := some y) dXY
  have hsd : ({some o, some x, some y, none} : Finset (Option V)) ∆ {some x, some y}
      = {some o, none} := by
    ext a
    simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
    by_cases h1 : a = some o <;> by_cases h2 : a = some x <;> by_cases h3 : a = some y <;>
      by_cases h4 : a = (none : Option V) <;> subst_vars <;> simp_all
  rw [hsd] at hid
  exact hid










theorem gc25_nativeAllConnMass_eq_gap (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    gc25_nativeAllConnMass G β h o x y
      = currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
          ({some o, some x, some y, none} : Finset (Option V))
        * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅
      - currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some o, none}
        * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some x, some y} := by
  unfold gc25_nativeAllConnMass
  set J' := ghostCoupling h β (fun _ : Sym2 V => (1 : ℝ)) with hJ'
  obtain ⟨dOX, dOY, dOg, dXY, dXg, dYg⟩ := gc15_marks_distinct hox hoy hxy
  rw [gc15_gquad o x y]
  have hid := GhostCurrentRep.gcr_currentSum_ghostRep (withGhost G) β J'
    ({some o, some x, some y, none} : Finset (Option V)) (u := some o) (v := none) dOg
  have hsd : ({some o, some x, some y, none} : Finset (Option V)) ∆ {some o, none}
      = {some x, some y} := by
    ext a
    simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
    by_cases h1 : a = some o <;> by_cases h2 : a = some x <;> by_cases h3 : a = some y <;>
      by_cases h4 : a = (none : Option V) <;> subst_vars <;> simp_all
  rw [hsd] at hid
  rw [mul_comm (currentSum (withGhost G) β J' {some o, none})
        (currentSum (withGhost G) β J' {some x, some y})]
  exact hid.symm




















theorem gc25_threeGap_sum_decomp (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    (∑' m, gc15_threeGap G β h o x y m)
      = gc15_Z0 G β h * gc25_nativeAllConnMass G β h o x y
        - gc15_Z0 G β h
            * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some o, some x}
            * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some y, none}
        - gc15_Z0 G β h
            * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some o, some y}
            * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some x, none}
        + 2 * (currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some o, none}
            * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some x, none}
            * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some y, none}) := by
  rw [← gc15_u3_eq_tsum_threeGap G β h o x y hox hoy hxy,
      gc15_u3_currentSum_poly G β h o x y hox hoy hxy,
      gc25_nativeAllConnMass_eq_gap G β h o x y hox hoy hxy,
      gc15_gquad o x y, gc15_gsingle o, gc15_gpair x y, gc15_gpair o x, gc15_gsingle y,
      gc15_gpair o y, gc15_gsingle x]
  unfold gc15_Z0
  ring







theorem gc25_three_switchingGaps_nonneg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    (currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some o, none}
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
        * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅) :=
  gc24_three_switchingGaps_nonneg G β h hβ hh o x y hox hoy hxy















theorem gc25_witness_structure :
    (∀ m : Finset (Fin 2), (0 : ℝ) ≤ (fun _ => (1 : ℝ)) m)
      ∧ (∀ i, ¬ (witEnds i).IsDiag)
      ∧ (¬ connK witEnds witM (0 : Fin 4) 3 ∧ sources witEnds witM = {0, 1, 2, 3}) := by
  refine ⟨fun _ => zero_le_one, ?_, ?_, ?_⟩
  · intro i; fin_cases i <;> decide
  · exact witM_not_connK_og
  · exact witM_sources






















theorem gc25_nativeAllConnMass_eq_edgecopy (β h : ℝ) (o x y : V) :
    gc25_nativeAllConnMass G β h o x y
      = ∑' m : ↥(withGhost G).edgeFinset → ℕ,
          (∑ S : Finset (Copy (withGhost G) m),
            (if RandomCurrent.sources (endsM (withGhost G) m) S
                  = (insert (none : Option V) (({o, x, y} : Finset V).map someEmb)) then (1 : ℝ) else 0)
              * (if RandomCurrent.sources (endsM (withGhost G) m) (univ \ S) = ∅ then 1 else 0)
              * (if ¬ RandomCurrent.connK (endsM (withGhost G) m) univ (some o) none then 1 else 0))
          * weight (withGhost G) β (ghostCoupling h β (fun _ => 1)) (ofEdgeFun (withGhost G) m) := by
  unfold gc25_nativeAllConnMass
  exact sourcePairDisconnSum_eq_edgecopy (withGhost G) β (ghostCoupling h β (fun _ => 1)) _ ∅ _ _












theorem gc25_backbone_not_signDefinite {ι : Type*} [DecidableEq ι] [Fintype ι]
    (ends : ι → Sym2 (Option V)) (m₁ m₂ : Finset ι) {o x y : V}
    (h₁ : connK ends m₁ (some x) (some y) ∧ connK ends m₁ (some o) (some y)
        ∧ connK ends m₁ (some o) (some x))
    (h₂ : ¬ connK ends m₂ (some x) (some y) ∧ ¬ connK ends m₂ (some o) (some y)
        ∧ ¬ connK ends m₂ (some o) (some x)) :
    asd_ghsBackboneFactor ends m₁ (some o) (some x) (some y) < 0
      ∧ 0 < asd_ghsBackboneFactor ends m₂ (some o) (some x) (some y) :=
  asd_ghsBackboneFactor_not_signDefinite ends m₁ m₂ h₁ h₂













theorem gc25_native_and_edgecopy_both_close (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    (gc25_NativeResummation G β h o x y → eg_ursell3 G β h o x y ≤ 0)
      ∧ (gc24_ThreeReplicaResummation G β h o x y → eg_ursell3 G β h o x y ≤ 0) :=
  ⟨gc25_ursell_nonpos_of_nativeResummation G β h hβ hh o x y hox hoy hxy,
   gc24_ursell_nonpos_of_threeReplicaResummation G β h o x y hox hoy hxy⟩

end StatMech.Walls
