/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



























































import Mathlib
import Code.Walls.gh6attach
import Code.Walls.gh3weightedcor3
import Code.Walls.gh7resum

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
























theorem gh8_weighted_drop_nonneg {ι : Type*} [DecidableEq ι] [Fintype ι]
    {W : Type*} [DecidableEq W] [Fintype W]
    (ends : ι → Sym2 W) (m : Finset ι) (V₁ V₂ : Finset W) (u : W)
    (wgtA diffA : Finset ι → ℝ) (hwgt : ∀ A, 0 ≤ wgtA A) (hdiff : ∀ A, 0 ≤ diffA A) :
    0 ≤ ∑ A ∈ m.powerset, (gh5_complMassDecoupled ends m V₁ V₂ u A : ℝ) * wgtA A * diffA A := by
  apply Finset.sum_nonneg
  intro A hA
  have hmass : (0 : ℝ) ≤ (gh5_complMassDecoupled ends m V₁ V₂ u A : ℝ) := by positivity
  have := hwgt A
  have := hdiff A
  positivity





























def gh8_weighted_eq22 {ι : Type*} [DecidableEq ι] [Fintype ι]
    {W : Type*} [DecidableEq W] [Fintype W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (β h : ℝ) (o x y : V)
    (ends : ι → Sym2 W) (m : Finset ι) (u u' : W) : Prop :=
  ∃ (surv : ℝ) (V₁ V₂ V₁' V₂' : Finset W) (wgtA diffA wgtB diffB : Finset ι → ℝ),
    (∀ A, 0 ≤ wgtA A) ∧ (∀ A, 0 ≤ diffA A) ∧ (∀ B, 0 ≤ wgtB B) ∧ (∀ B, 0 ≤ diffB B)
    ∧ eg_ursell3 G β h o x y
        = surv
          - 2 * (∑ A ∈ m.powerset, (gh5_complMassDecoupled ends m V₁ V₂ u A : ℝ) * wgtA A * diffA A)
          - 2 * (∑ B ∈ m.powerset, (gh5_complMassDecoupled ends m V₁' V₂' u' B : ℝ) * wgtB B * diffB B)
    ∧ surv ≤ 0














theorem gh8_eq22_decomp_of_weighted {ι : Type*} [DecidableEq ι] [Fintype ι]
    {W : Type*} [DecidableEq W] [Fintype W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (β h : ℝ) (o x y : V)
    (ends : ι → Sym2 W) (m : Finset ι) (u u' : W)
    (heq22 : gh8_weighted_eq22 G β h o x y ends m u u') :
    gh3_eq22_decomposition G β h o x y := by
  obtain ⟨surv, V₁, V₂, V₁', V₂', wgtA, diffA, wgtB, diffB,
    hwgtA, hdiffA, hwgtB, hdiffB, hident, hsurv⟩ := heq22
  refine ⟨surv,
    ∑ A ∈ m.powerset, (gh5_complMassDecoupled ends m V₁ V₂ u A : ℝ) * wgtA A * diffA A,
    ∑ B ∈ m.powerset, (gh5_complMassDecoupled ends m V₁' V₂' u' B : ℝ) * wgtB B * diffB B,
    hident, ?_, ?_⟩
  · exact gh8_weighted_drop_nonneg ends m V₁ V₂ u wgtA diffA hwgtA hdiffA
  · exact gh8_weighted_drop_nonneg ends m V₁' V₂' u' wgtB diffB hwgtB hdiffB












theorem gh8_weighted_gks_drop {ι : Type*} [DecidableEq ι] [Fintype ι]
    {W : Type*} [DecidableEq W] [Fintype W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (β h : ℝ) (o x y : V)
    (ends : ι → Sym2 W) (m : Finset ι) (u u' : W)
    {surv : ℝ}
    (heq22 : ∃ (V₁ V₂ V₁' V₂' : Finset W) (wgtA diffA wgtB diffB : Finset ι → ℝ),
      (∀ A, 0 ≤ wgtA A) ∧ (∀ A, 0 ≤ diffA A) ∧ (∀ B, 0 ≤ wgtB B) ∧ (∀ B, 0 ≤ diffB B)
      ∧ eg_ursell3 G β h o x y
          = surv
            - 2 * (∑ A ∈ m.powerset, (gh5_complMassDecoupled ends m V₁ V₂ u A : ℝ) * wgtA A * diffA A)
            - 2 * (∑ B ∈ m.powerset, (gh5_complMassDecoupled ends m V₁' V₂' u' B : ℝ) * wgtB B * diffB B)) :
    eg_ursell3 G β h o x y ≤ surv := by
  obtain ⟨V₁, V₂, V₁', V₂', wgtA, diffA, wgtB, diffB,
    hwgtA, hdiffA, hwgtB, hdiffB, hident⟩ := heq22
  exact gh3_gks_drop_step _ surv _ _ hident
    (gh8_weighted_drop_nonneg ends m V₁ V₂ u wgtA diffA hwgtA hdiffA)
    (gh8_weighted_drop_nonneg ends m V₁' V₂' u' wgtB diffB hwgtB hdiffB)


















theorem gh8_ghs_of_weighted_eq22 {ι : Type*} [DecidableEq ι] [Fintype ι]
    {W : Type*} [DecidableEq W] [Fintype W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (β h : ℝ) (o x y : V)
    (ends : ι → Sym2 W) (m : Finset ι) (u u' : W)
    (heq22 : gh8_weighted_eq22 G β h o x y ends m u u') :
    eg_ursell3 G β h o x y ≤ 0 := by
  
  have hdecomp : gh3_eq22_decomposition G β h o x y :=
    gh8_eq22_decomp_of_weighted G β h o x y ends m u u' heq22
  
  obtain ⟨surv, V₁, V₂, V₁', V₂', wgtA, diffA, wgtB, diffB,
    hwgtA, hdiffA, hwgtB, hdiffB, hident, hsurv⟩ := heq22
  
  have hdrop : eg_ursell3 G β h o x y ≤ surv := by
    apply gh3_gks_drop_step _ surv _ _ hident
    · exact gh8_weighted_drop_nonneg ends m V₁ V₂ u wgtA diffA hwgtA hdiffA
    · exact gh8_weighted_drop_nonneg ends m V₁' V₂' u' wgtB diffB hwgtB hdiffB
  
  linarith













theorem gh8_lemma1_covariance (G : SimpleGraph V) [DecidableRel G.Adj] (β h : ℝ) (hβ : 0 ≤ β)
    (i j k : V) :
    StatMech.Ising.cov2 G β h i j * StatMech.Ising.cov2 G β h j k
      ≤ StatMech.Walls.VBG.vbg_var (StatMech.Ising.isingProb G β h) (fun s => StatMech.Ising.spin s j)
        * StatMech.Ising.cov2 G β h i k :=
  ghg_lemma1_is_vbg G β h hβ i j k

















































theorem gh8_status : True := trivial











theorem gh8_smallmodel_check {ι : Type*} [DecidableEq ι] [Fintype ι]
    {W : Type*} [DecidableEq W] [Fintype W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (β h : ℝ) (o x y : V)
    (ends : ι → Sym2 W) (m : Finset ι) (u u' : W)
    (hzero : eg_ursell3 G β h o x y = 0) :
    eg_ursell3 G β h o x y ≤ 0 := by
  apply gh8_ghs_of_weighted_eq22 G β h o x y ends m u u'
  refine ⟨0, ∅, ∅, ∅, ∅, (fun _ => 0), (fun _ => 0), (fun _ => 0), (fun _ => 0),
    (fun _ => le_refl 0), (fun _ => le_refl 0), (fun _ => le_refl 0), (fun _ => le_refl 0), ?_, le_refl 0⟩
  simp [hzero]

end StatMech.Walls
