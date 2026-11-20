/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










































































import Mathlib
import Code.Walls.gc33witness
import Code.Walls.gc32surgery
import Code.Sharpness.ClaimIsingFull
import Code.Sharpness.CurrentRep
import Code.Sharpness.SimonLiebFull
import Code.Ising.GKS2

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

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]











theorem gc34_spinProd_le_one (A : Finset V) (s : StatMech.ConfigSpace V) :
    StatMech.Ising.spinProd A s ≤ 1 := by
  have := StatMech.Ising.one_sub_spinProd_nonneg A s
  linarith








theorem gc34_expectationJ_le_one (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V) :
    StatMech.Sharpness.expectationJ G β J A ≤ 1 := by
  unfold StatMech.Sharpness.expectationJ
  rw [div_le_one (StatMech.Sharpness.partitionJ_pos G β J)]
  unfold StatMech.Sharpness.partitionJ
  refine Finset.sum_le_sum (fun s _ => ?_)
  have hpos := StatMech.Sharpness.boltzmannJ_pos G β J s
  nlinarith [gc34_spinProd_le_one A s, hpos]
















theorem gc34_resummation_factor_mem_Icc (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (S A : Finset V) :
    0 ≤ StatMech.Sharpness.expectationJ G β (StatMech.Sharpness.couplingIn J S) A
      ∧ StatMech.Sharpness.expectationJ G β (StatMech.Sharpness.couplingIn J S) A ≤ 1 := by
  refine ⟨StatMech.Sharpness.ssl_expectationJ_nonneg G β (StatMech.Sharpness.couplingIn J S)
    hβ (fun e => ?_) A, gc34_expectationJ_le_one G β (StatMech.Sharpness.couplingIn J S) A⟩
  unfold StatMech.Sharpness.couplingIn
  split
  · exact hJ e
  · exact le_refl 0



















theorem gc34_sourceClusterResummation_witness :
    gc33_SourceClusterResummation gc33_G 1 gc33_J gc33_M ∅ 0 1 2 := by
  refine ⟨1, fun _ => gc33_mstar, one_pos, le_refl 1, ?_, ?_, ?_⟩
  · intro m hm
    rw [gc33_allFilter, Finset.mem_singleton] at hm
    exact gc33_mstar_in_noneFilter
  · intro a ha b hb hab
    rw [gc33_allFilter] at ha hb
    rw [Finset.mem_coe, Finset.mem_singleton] at ha hb
    rw [ha, hb]
  · intro m hm
    rw [gc33_allFilter, Finset.mem_singleton] at hm
    subst hm
    rw [one_mul]
    exact gc33_doubling








theorem gc34_witness_closes_surgery :
    gc31_MassDoublingSurgery gc33_G 1 gc33_J gc33_M ∅ 0 1 2 :=
  gc33_massDoubling_of_sourceClusterResummation gc33_G 1 gc33_J (by norm_num) gc33_J_nonneg
    gc33_M ∅ 0 1 2 gc34_sourceClusterResummation_witness



















theorem gc34_mass_summand_cut_factor {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (β : ℝ) (J : Sym2 V → ℝ)
    (m K : Sharpness.Current V) (p : Sym2 V → Prop) [DecidablePred p] :
    Sharpness.weight G β J K * Sharpness.weight G β J (fun e => m e - K e)
      = (Sharpness.weight G β J (StatMech.Ising.restrictCut K p)
          * Sharpness.weight G β J (StatMech.Ising.restrictCut (fun e => m e - K e) p))
        * (Sharpness.weight G β J (StatMech.Ising.restrictCut K (fun e => ¬ p e))
          * Sharpness.weight G β J (StatMech.Ising.restrictCut (fun e => m e - K e)
              (fun e => ¬ p e))) :=
  gc33_mass_summand_cut_factor G β J m K p











theorem gc34_sourceClusterResummation_iff {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (β : ℝ) (J : Sym2 V → ℝ)
    (M : Finset (Sharpness.Current V)) (B : Finset V) (o x y : V) :
    gc33_SourceClusterResummation G β J M B o x y
      ↔ ∃ (μ : ℝ) (Ψ : Sharpness.Current V → Sharpness.Current V),
          0 < μ ∧ μ ≤ 1
          ∧ (∀ m ∈ bbr_allFilter G M o x y, Ψ m ∈ bbr_noneFilter G M o x y)
          ∧ Set.InjOn Ψ (bbr_allFilter G M o x y)
          ∧ (∀ m ∈ bbr_allFilter G M o x y,
              2 * hnw_mass G β J m B ≤ μ * hnw_mass G β J (Ψ m) B) :=
  Iff.rfl













theorem gc34_status {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (β : ℝ) (J : Sym2 V → ℝ)
    (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (M : Finset (Sharpness.Current V)) (B : Finset V) (o x y : V) :
    (gc33_SourceClusterResummation G β J M B o x y
        → gc31_MassDoublingSurgery G β J M B o x y)
      ∧ (∀ A : Finset V,
          0 ≤ StatMech.Sharpness.expectationJ G β (StatMech.Sharpness.couplingIn J A) {o, x}
            ∧ StatMech.Sharpness.expectationJ G β (StatMech.Sharpness.couplingIn J A) {o, x} ≤ 1) := by
  refine ⟨gc33_massDoubling_of_sourceClusterResummation G β J hβ hJ M B o x y, ?_⟩
  intro A
  exact gc34_resummation_factor_mem_Icc G β J hβ hJ A {o, x}

end StatMech.Walls
