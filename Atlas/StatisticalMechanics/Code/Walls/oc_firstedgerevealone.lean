/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

















































import Mathlib
import Code.OSSS.FKRevealmentClose
import Code.OSSS.PerScaleRevealmentClose
import Code.OSSS.SharpnessFK

open scoped BigOperators

namespace StatMech

namespace Walls

open StatMech.OSSS
open StatMech.OSSS.AdaptMConditional
open StatMech.OSSS.RevealmentBoxCrossing
open StatMech.OSSS.FKRevealmentClose

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

variable {E : Type*} [Fintype E] [DecidableEq E]


















theorem oc_revealAdapt_first_eq_one {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ) (e₀ : E)
    (he₀ : (σ.symm e₀ : ℕ) = 0) (hnc : ∀ X, ¬ ∀ w, f w = f X) :
    revealAdapt μ σ f e₀ = 1 := by
  
  rw [revealAdapt_eq_reachProb hpos hμ1 σ f e₀]
  unfold reachProb Lindeberg.mean
  
  rw [he₀]
  
  have hpref : OSSS.Coding.prefixSet (σ : Fin n → E) 0 = ∅ := OSSS.Coding.prefixSet_zero _
  
  have hone : ∀ X, reachInd σ f 0 X = 1 := by
    intro X
    unfold reachInd
    rw [if_neg]
    intro hdet
    
    exact hnc X (fun w => hdet w (by rw [hpref]; intro a ha; simp at ha))
  
  calc ∑ X, reachInd σ f 0 X * μ X
        = ∑ X, (1 : ℝ) * μ X := by
          apply Finset.sum_congr rfl; intro X _; rw [hone X]
    _ = 1 := by simp only [one_mul]; exact hμ1















theorem oc_revealAdapt_first_gt {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ) (e₀ : E)
    (he₀ : (σ.symm e₀ : ℕ) = 0) (hnc : ∀ X, ¬ ∀ w, f w = f X) {c : ℝ} (hc : c < 1) :
    ¬ revealAdapt μ σ f e₀ ≤ c := by
  rw [oc_revealAdapt_first_eq_one hpos hμ1 σ f e₀ he₀ hnc]
  intro h
  exact absurd (lt_of_le_of_lt h hc) (by norm_num)










theorem oc_not_forall_revealAdapt_le {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ) (e₀ : E)
    (he₀ : (σ.symm e₀ : ℕ) = 0) (hnc : ∀ X, ¬ ∀ w, f w = f X) {c : ℝ} (hc : c < 1) :
    ¬ (∀ e, revealAdapt μ σ f e ≤ c) := by
  intro hall
  exact oc_revealAdapt_first_gt hpos hμ1 σ f e₀ he₀ hnc hc (hall e₀)











theorem oc_uniform_sum_eq_one :
    (∑ _ω : ConfigSpace (Fin 2), 1 / (Fintype.card (ConfigSpace (Fin 2)) : ℝ)) = 1 := by
  have hcard : (0 : ℝ) < (Fintype.card (ConfigSpace (Fin 2)) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one_div, div_self hcard.ne']



theorem oc_coord_nonconstant :
    ∀ X : ConfigSpace (Fin 2), ¬ ∀ w, Lindeberg.coord (0 : Fin 2) w = Lindeberg.coord 0 X := by
  intro X hall
  have h1 := hall (fun _ => true)
  have h0 := hall (fun _ => false)
  unfold Lindeberg.coord at h1 h0
  rw [if_pos rfl] at h1
  rw [if_neg (by decide)] at h0
  rw [← h0] at h1
  exact absurd h1 (by norm_num)






theorem oc_first_edge_reveal_one_witness :
    revealAdapt (fun _ : ConfigSpace (Fin 2) => 1 / (Fintype.card (ConfigSpace (Fin 2)) : ℝ))
      (Equiv.refl (Fin 2)) (Lindeberg.coord (0 : Fin 2)) (0 : Fin 2) = 1 :=
  oc_revealAdapt_first_eq_one (fun _ => by
      have hcard : (0 : ℝ) < (Fintype.card (ConfigSpace (Fin 2)) : ℝ) := by
        exact_mod_cast Fintype.card_pos
      positivity)
    oc_uniform_sum_eq_one (Equiv.refl (Fin 2)) (Lindeberg.coord (0 : Fin 2)) (0 : Fin 2)
    (by simp) oc_coord_nonconstant





theorem oc_not_forall_revealAdapt_le_witness {c : ℝ} (hc : c < 1) :
    ¬ (∀ e : Fin 2,
        revealAdapt (fun _ : ConfigSpace (Fin 2) => 1 / (Fintype.card (ConfigSpace (Fin 2)) : ℝ))
          (Equiv.refl (Fin 2)) (Lindeberg.coord (0 : Fin 2)) e ≤ c) := by
  intro hall
  have h0 := hall 0
  rw [oc_first_edge_reveal_one_witness] at h0
  exact absurd (lt_of_le_of_lt h0 hc) (by norm_num)

end Walls

end StatMech
