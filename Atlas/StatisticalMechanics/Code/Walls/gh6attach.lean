/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












































import Mathlib
import Code.Walls.gh5currentrep
import Code.Sharpness.FluxEdgeCopyBridge
import Code.Sharpness.ClaimIsingFull

open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option maxHeartbeats 1600000

namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness
open StatMech.Sharpness.RandomCurrent StatMech.Sharpness.FluxEdgeCopy
open StatMech.Walls.GhcEqGap













variable {V : Type*} [Fintype V] [DecidableEq V]








theorem gh6_restricted_weight_bridge (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (Ac : Finset V) (m : ↥G.edgeFinset → ℕ) (A B : Finset V) :
    gc15_tpsum G β (StatMech.Sharpness.couplingIn J Ac) m A B
      = (gc85b_pcount (endsM G m) univ A B : ℝ)
          * weight G β (StatMech.Sharpness.couplingIn J Ac) (ofEdgeFun G m) :=
  gc85b_tpsum_eq_pcount G β (StatMech.Sharpness.couplingIn J Ac) m A B


























theorem gh6_restricted_expectation_ratio (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (Ac : Finset V) (k l : V) :
    StatMech.Sharpness.expectationJ G β (StatMech.Sharpness.couplingIn J Ac) {k, l}
      = StatMech.Sharpness.currentSum G β (StatMech.Sharpness.couplingIn J Ac) {k, l}
          / StatMech.Sharpness.currentSum G β (StatMech.Sharpness.couplingIn J Ac) ∅ :=
  StatMech.Sharpness.current_representation G β (StatMech.Sharpness.couplingIn J Ac) {k, l}








theorem gh6_expectation_times_Z_eq_currentSum (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (Ac : Finset V) (k l : V)
    (hZ : StatMech.Sharpness.currentSum G β (StatMech.Sharpness.couplingIn J Ac) ∅ ≠ 0) :
    StatMech.Sharpness.expectationJ G β (StatMech.Sharpness.couplingIn J Ac) {k, l}
        * StatMech.Sharpness.currentSum G β (StatMech.Sharpness.couplingIn J Ac) ∅
      = StatMech.Sharpness.currentSum G β (StatMech.Sharpness.couplingIn J Ac) {k, l} := by
  rw [gh6_restricted_expectation_ratio G β J Ac k l, div_mul_cancel₀ _ hZ]


























theorem gh6_weighted_attachment_reduces {ι : Type*} [DecidableEq ι] [Fintype ι]
    {W : Type*} [DecidableEq W] [Fintype W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (β h : ℝ) (o x y : V)
    (ends : ι → Sym2 W) (m : Finset ι) (V₁ V₂ V₁' V₂' : Finset W) (u u' : W)
    (wgtA diffA wgtB diffB : Finset ι → ℝ)
    (hwgtA : ∀ A, 0 ≤ wgtA A) (hdiffA : ∀ A, 0 ≤ diffA A)
    (hwgtB : ∀ B, 0 ≤ wgtB B) (hdiffB : ∀ B, 0 ≤ diffB B)
    (surv : ℝ)
    (hident : eg_ursell3 G β h o x y
      = surv
        - 2 * (∑ A ∈ m.powerset, (gh5_complMassDecoupled ends m V₁ V₂ u A : ℝ) * wgtA A * diffA A)
        - 2 * (∑ B ∈ m.powerset, (gh5_complMassDecoupled ends m V₁' V₂' u' B : ℝ) * wgtB B * diffB B)) :
    gh3_eq22_decomposition G β h o x y :=
  gh5_eq22_from_factored_identity G β h o x y ends m V₁ V₂ V₁' V₂' u u'
    wgtA diffA wgtB diffB hwgtA hdiffA hwgtB hdiffB surv hident


























































theorem gh6_status : True := trivial

end StatMech.Walls
