/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



































































import Mathlib
import Code.Ising.GKS
import Code.Ising.GKS2
import Code.Sharpness.Simon
import Code.Walls.ghc_urselleqgap
import Code.Walls.ghggrahamclose

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
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000

namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness
open StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]


















theorem gh3_gks_drop_pair (E₁ E₂ : Finset (Sym2 V)) (J : Sym2 V → ℝ) (hf : V → ℝ)
    (hsub : E₁ ⊆ E₂) (hJ : ∀ e ∈ E₂, 0 ≤ J e) (hhf : ∀ x, 0 ≤ hf x)
    (hdiag : ∀ e ∈ E₂, e ∉ E₁ → ¬ e.IsDiag) (k l : V) :
    StatMech.Sharpness.expJ E₁ J hf (StatMech.Ising.spinProd {k, l})
      ≤ StatMech.Sharpness.expJ E₂ J hf (StatMech.Ising.spinProd {k, l}) :=
  StatMech.Sharpness.griffiths_mono_pair E₁ E₂ J hf hsub hJ hhf hdiag k l




theorem gh3_gks_drop_diff_nonneg (E₁ E₂ : Finset (Sym2 V)) (J : Sym2 V → ℝ) (hf : V → ℝ)
    (hsub : E₁ ⊆ E₂) (hJ : ∀ e ∈ E₂, 0 ≤ J e) (hhf : ∀ x, 0 ≤ hf x)
    (hdiag : ∀ e ∈ E₂, e ∉ E₁ → ¬ e.IsDiag) (k l : V) :
    0 ≤ StatMech.Sharpness.expJ E₂ J hf (StatMech.Ising.spinProd {k, l})
          - StatMech.Sharpness.expJ E₁ J hf (StatMech.Ising.spinProd {k, l}) := by
  have h := gh3_gks_drop_pair E₁ E₂ J hf hsub hJ hhf hdiag k l
  linarith












theorem gh3_dropped_term_nonneg (mass diff : ℝ) (hmass : 0 ≤ mass) (hdiff : 0 ≤ diff) :
    0 ≤ 2 * mass * diff := by positivity











theorem gh3_gks_drop_step (LHS SURV dropA dropB : ℝ)
    (hdecomp : LHS = SURV - 2 * dropA - 2 * dropB)
    (hA : 0 ≤ dropA) (hB : 0 ≤ dropB) :
    LHS ≤ SURV := by
  rw [hdecomp]; linarith















def gh3_eq22_decomposition (G : SimpleGraph V) [DecidableRel G.Adj] (β h : ℝ) (o x y : V) : Prop :=
  ∃ surv dropA dropB : ℝ,
    eg_ursell3 G β h o x y = surv - 2 * dropA - 2 * dropB
      ∧ 0 ≤ dropA ∧ 0 ≤ dropB







def gh3_lemma1_finish (G : SimpleGraph V) [DecidableRel G.Adj] (β h : ℝ) (o x y : V) (surv : ℝ) :
    Prop := surv ≤ 0












theorem gh3_weighted_cor3_via_gks_drop (G : SimpleGraph V) [DecidableRel G.Adj] (β h : ℝ)
    (o x y : V)
    (hdecomp : gh3_eq22_decomposition G β h o x y)
    (hfinish : ∀ surv : ℝ,
        eg_ursell3 G β h o x y ≤ surv → gh3_lemma1_finish G β h o x y surv) :
    eg_ursell3 G β h o x y ≤ 0 := by
  obtain ⟨surv, dropA, dropB, heq, hA, hB⟩ := hdecomp
  
  have hdrop : eg_ursell3 G β h o x y ≤ surv :=
    gh3_gks_drop_step _ surv dropA dropB heq hA hB
  
  have hsurv : surv ≤ 0 := hfinish surv hdrop
  linarith

















































theorem gh3_status : True := trivial

end StatMech.Walls
