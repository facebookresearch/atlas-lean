/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/









































































import Mathlib
import Code.OSSS.RevealmentBoxCrossing
import Code.OSSS.FKRevealmentClose
import Code.OSSS.SharpnessFK
import Code.OSSS.Coding
import Code.OSSS.GrandCoupling
import Code.OSSS.AdaptMConditional
import Code.Walls.oc3_codinglawintegral

open scoped BigOperators
open Finset MeasureTheory

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace StatMech
namespace Walls

open StatMech.OSSS
open StatMech.OSSS.AdaptMConditional
open StatMech.OSSS.RevealmentBoxCrossing
open StatMech.OSSS.Coding
open StatMech.OSSS.GrandCoupling

variable {E : Type*} [Fintype E] [DecidableEq E]























theorem oc4_revealAdapt_first_as_cubeIntegral (μ : ConfigSpace E → ℝ)
    {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ) (e : E) :
    revealAdapt μ σ f e
      = ∫ u, truncIndC σ f (codeMap μ (σ : Fin n → E) u) ((σ.symm e : ℕ) + 1) ∂(Vcube n) := by
  unfold revealAdapt
  rw [integral_prod _ (integrable_truncInd μ σ f ((σ.symm e : ℕ) + 1))]
  have hredU : (∫ U, (∫ _V, truncInd μ σ f U ((σ.symm e : ℕ) + 1) ∂(Vcube n)) ∂(Vcube n))
      = ∫ U, truncInd μ σ f U ((σ.symm e : ℕ) + 1) ∂(Vcube n) := by
    apply integral_congr_ae; apply Filter.Eventually.of_forall; intro U
    simp only; rw [integral_const]; simp
  rw [hredU]
  apply integral_congr_ae; apply Filter.Eventually.of_forall; intro U
  exact truncInd_eq_truncIndC μ σ f U ((σ.symm e : ℕ) + 1)























theorem oc4_revealAdapt_first_eq_one_codingFrame {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ) (e₀ : E)
    (he₀ : (σ.symm e₀ : ℕ) = 0) (hnc : ∀ X, ¬ ∀ w, f w = f X) :
    revealAdapt μ σ f e₀ = 1 := by
  
  rw [oc4_revealAdapt_first_as_cubeIntegral μ σ f e₀]
  
  rw [oc3_codingLawIntegral μ hpos hμ1 σ (fun X => truncIndC σ f X ((σ.symm e₀ : ℕ) + 1))]
  
  have hone : ∀ X, truncIndC σ f X ((σ.symm e₀ : ℕ) + 1) = 1 := by
    intro X
    rw [he₀, truncIndC_succ_eq_reachInd σ f X 0]
    unfold reachInd
    rw [if_neg]
    
    intro hdet
    apply hnc X
    intro w
    exact hdet w (by rw [prefixSet_zero]; intro a ha; simp at ha)
  calc ∑ X, truncIndC σ f X ((σ.symm e₀ : ℕ) + 1) * μ X
      = ∑ X, (1 : ℝ) * μ X := by
        apply Finset.sum_congr rfl; intro X _; rw [hone X]
    _ = 1 := by simp only [one_mul]; exact hμ1















theorem oc4_revealAdapt_first_gt {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ) (e₀ : E)
    (he₀ : (σ.symm e₀ : ℕ) = 0) (hnc : ∀ X, ¬ ∀ w, f w = f X) {c : ℝ} (hc : c < 1) :
    ¬ revealAdapt μ σ f e₀ ≤ c := by
  rw [oc4_revealAdapt_first_eq_one_codingFrame hpos hμ1 σ f e₀ he₀ hnc]
  intro h
  exact absurd (lt_of_le_of_lt h hc) (by norm_num)










theorem oc4_not_forall_revealAdapt_le {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ) (e₀ : E)
    (he₀ : (σ.symm e₀ : ℕ) = 0) (hnc : ∀ X, ¬ ∀ w, f w = f X) {c : ℝ} (hc : c < 1) :
    ¬ (∀ e, revealAdapt μ σ f e ≤ c) := by
  intro hall
  exact oc4_revealAdapt_first_gt hpos hμ1 σ f e₀ he₀ hnc hc (hall e₀)








section FK

open StatMech.OSSS.MonotonicFK










theorem oc4_fk_revealAdapt_first_eq_one {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) {n : ℕ} (σ : Fin n ≃ Sym2 V)
    (f : ConfigSpace (Sym2 V) → ℝ) (e₀ : Sym2 V)
    (he₀ : (σ.symm e₀ : ℕ) = 0) (hnc : ∀ X, ¬ ∀ w, f w = f X) :
    revealAdapt (fkMass G p q) σ f e₀ = 1 :=
  oc4_revealAdapt_first_eq_one_codingFrame (fun ω => fkMass_pos G hp hp1 hq ω)
    (fkMass_sum_eq_one G hp hp1 hq) σ f e₀ he₀ hnc

end FK









theorem oc4_uniform_sum_eq_one :
    (∑ _ω : ConfigSpace (Fin 2), 1 / (Fintype.card (ConfigSpace (Fin 2)) : ℝ)) = 1 := by
  have hcard : (0 : ℝ) < (Fintype.card (ConfigSpace (Fin 2)) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one_div, div_self hcard.ne']



theorem oc4_coord_nonconstant :
    ∀ X : ConfigSpace (Fin 2), ¬ ∀ w, Lindeberg.coord (0 : Fin 2) w = Lindeberg.coord 0 X := by
  intro X hall
  have h1 := hall (fun _ => true)
  have h0 := hall (fun _ => false)
  unfold Lindeberg.coord at h1 h0
  rw [if_pos rfl] at h1
  rw [if_neg (by decide)] at h0
  rw [← h0] at h1
  exact absurd h1 (by norm_num)






theorem oc4_first_edge_one_witness :
    revealAdapt (fun _ : ConfigSpace (Fin 2) => 1 / (Fintype.card (ConfigSpace (Fin 2)) : ℝ))
      (Equiv.refl (Fin 2)) (Lindeberg.coord (0 : Fin 2)) (0 : Fin 2) = 1 :=
  oc4_revealAdapt_first_eq_one_codingFrame (fun _ => by
      have hcard : (0 : ℝ) < (Fintype.card (ConfigSpace (Fin 2)) : ℝ) := by
        exact_mod_cast Fintype.card_pos
      positivity)
    oc4_uniform_sum_eq_one (Equiv.refl (Fin 2)) (Lindeberg.coord (0 : Fin 2)) (0 : Fin 2)
    (by simp) oc4_coord_nonconstant





theorem oc4_not_forall_revealAdapt_le_witness {c : ℝ} (hc : c < 1) :
    ¬ (∀ e : Fin 2,
        revealAdapt (fun _ : ConfigSpace (Fin 2) => 1 / (Fintype.card (ConfigSpace (Fin 2)) : ℝ))
          (Equiv.refl (Fin 2)) (Lindeberg.coord (0 : Fin 2)) e ≤ c) := by
  intro hall
  have h0 := hall 0
  rw [oc4_first_edge_one_witness] at h0
  exact absurd (lt_of_le_of_lt h0 hc) (by norm_num)

end Walls
end StatMech
