/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





















































import Mathlib
import Code.Walls.gharesumassembly
import Code.Walls.gh9switchrearrange
import Code.Walls.gh8weightedassembly

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












theorem ghw_step1_resum (G : SimpleGraph V) [DecidableRel G.Adj] (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    (gc15_Z0 G β h) ^ 3 * eg_ursell3 G β h o x y
      = ∑' m : ↥(withGhost G).edgeFinset → ℕ, gc15_threeGap G β h o x y m :=
  gha_poly_resum G β h o x y hox hoy hxy








theorem ghw_step2_regroup {ι : Type*} [DecidableEq ι] [Fintype ι]
    {W : Type*} [DecidableEq W] [Fintype W]
    (ends : ι → Sym2 W) (m : Finset ι) (V₁ V₂ : Finset W) (u : W) :
    (gc85b_pcount ends m V₁ V₂ : ℝ)
      = ∑ A ∈ m.powerset, (gh4_compMass ends m V₁ V₂ u A : ℝ) :=
  gh9_pcount_regroup_real ends m V₁ V₂ u














theorem ghw_step3_gks_drop {ι : Type*} [DecidableEq ι] [Fintype ι]
    {W : Type*} [DecidableEq W] [Fintype W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (β h : ℝ) (o x y : V)
    (ends : ι → Sym2 W) (m : Finset ι) (u u' : W) {surv : ℝ}
    (heq22 : ∃ (V₁ V₂ V₁' V₂' : Finset W) (wgtA diffA wgtB diffB : Finset ι → ℝ),
      (∀ A, 0 ≤ wgtA A) ∧ (∀ A, 0 ≤ diffA A) ∧ (∀ B, 0 ≤ wgtB B) ∧ (∀ B, 0 ≤ diffB B)
      ∧ eg_ursell3 G β h o x y
          = surv
            - 2 * (∑ A ∈ m.powerset, (gh5_complMassDecoupled ends m V₁ V₂ u A : ℝ) * wgtA A * diffA A)
            - 2 * (∑ B ∈ m.powerset, (gh5_complMassDecoupled ends m V₁' V₂' u' B : ℝ) * wgtB B * diffB B)) :
    eg_ursell3 G β h o x y ≤ surv :=
  gh8_weighted_gks_drop G β h o x y ends m u u' heq22









theorem ghw_step4_lemma1 (G : SimpleGraph V) [DecidableRel G.Adj] (β h : ℝ) (hβ : 0 ≤ β)
    (i j k : V) :
    StatMech.Ising.cov2 G β h i j * StatMech.Ising.cov2 G β h j k
      ≤ StatMech.Walls.VBG.vbg_var (StatMech.Ising.isingProb G β h) (fun s => StatMech.Ising.spin s j)
        * StatMech.Ising.cov2 G β h i k :=
  StatMech.Walls.VBG.vbg_cor1 G β h hβ i j k













theorem ghw_chain_step3_step4 {ι : Type*} [DecidableEq ι] [Fintype ι]
    {W : Type*} [DecidableEq W] [Fintype W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (β h : ℝ) (o x y : V)
    (ends : ι → Sym2 W) (m : Finset ι) (u u' : W) {surv : ℝ}
    (heq22 : ∃ (V₁ V₂ V₁' V₂' : Finset W) (wgtA diffA wgtB diffB : Finset ι → ℝ),
      (∀ A, 0 ≤ wgtA A) ∧ (∀ A, 0 ≤ diffA A) ∧ (∀ B, 0 ≤ wgtB B) ∧ (∀ B, 0 ≤ diffB B)
      ∧ eg_ursell3 G β h o x y
          = surv
            - 2 * (∑ A ∈ m.powerset, (gh5_complMassDecoupled ends m V₁ V₂ u A : ℝ) * wgtA A * diffA A)
            - 2 * (∑ B ∈ m.powerset, (gh5_complMassDecoupled ends m V₁' V₂' u' B : ℝ) * wgtB B * diffB B))
    (hsurv : surv ≤ 0) :
    eg_ursell3 G β h o x y ≤ 0 := by
  have hdrop : eg_ursell3 G β h o x y ≤ surv :=
    ghw_step3_gks_drop G β h o x y ends m u u' heq22
  linarith














theorem ghw_ghs_assembly {ι : Type*} [DecidableEq ι] [Fintype ι]
    {W : Type*} [DecidableEq W] [Fintype W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (β h : ℝ) (o x y : V)
    (ends : ι → Sym2 W) (m : Finset ι) (u u' : W)
    (heq22 : gh8_weighted_eq22 G β h o x y ends m u u') :
    eg_ursell3 G β h o x y ≤ 0 :=
  gh8_ghs_of_weighted_eq22 G β h o x y ends m u u' heq22













theorem ghw_surv_is_free_existential {ι : Type*} [DecidableEq ι] [Fintype ι]
    {W : Type*} [DecidableEq W] [Fintype W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (β h : ℝ) (o x y : V)
    (ends : ι → Sym2 W) (m : Finset ι) (u u' : W)
    (hghs : eg_ursell3 G β h o x y ≤ 0) :
    gh8_weighted_eq22 G β h o x y ends m u u' :=
  gha_weighted_eq22_of_ghs G β h o x y ends m u u' hghs










theorem ghw_weighted_eq22_iff {ι : Type*} [DecidableEq ι] [Fintype ι]
    {W : Type*} [DecidableEq W] [Fintype W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (β h : ℝ) (o x y : V)
    (ends : ι → Sym2 W) (m : Finset ι) (u u' : W) :
    gh8_weighted_eq22 G β h o x y ends m u u' ↔ eg_ursell3 G β h o x y ≤ 0 :=
  ⟨ghw_ghs_assembly G β h o x y ends m u u',
   ghw_surv_is_free_existential G β h o x y ends m u u'⟩







theorem ghw_surv_not_bound_to_lemma1 {ι : Type*} [DecidableEq ι] [Fintype ι]
    {W : Type*} [DecidableEq W] [Fintype W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (β h : ℝ) (o x y : V)
    (ends : ι → Sym2 W) (m : Finset ι) (u u' : W) :
    gh9_perSuperposition_weighted_eq22 G β h o x y ends m u u'
      ↔ eg_ursell3 G β h o x y ≤ 0 := by
  rw [gh9_perSuperposition_iff_eq22]
  exact ghw_weighted_eq22_iff G β h o x y ends m u u'













theorem ghw_ghs_nonCircular (G : SimpleGraph V) [DecidableRel G.Adj]
    (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hbij : ∀ m : ↥(withGhost G).edgeFinset → ℕ,
        sources (withGhost G) (ofEdgeFun (withGhost G) m)
          = ({some o, some x, some y, none} : Finset (Option V)) →
        gc85b_ThreeCurrentBijection (endsM (withGhost G) m) univ (some o) (some x) (some y) none)
    (hsupp : gc82_ThreeGapAllConnSupported G β h o x y) :
    eg_ursell3 G β h o x y ≤ 0 :=
  gha_ghs_of_bijection G β h hβ hh o x y hox hoy hxy hbij hsupp
















































theorem ghw_status : True := trivial

end StatMech.Walls
