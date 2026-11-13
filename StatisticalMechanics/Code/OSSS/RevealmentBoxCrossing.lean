/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





































































import Code.OSSS.RevealmentBoundAssembly
import Code.OSSS.CrossMonotone

open scoped BigOperators
open MeasureTheory

namespace StatMech

namespace OSSS

namespace RevealmentBoxCrossing

open OSSS.Monotonic OSSS.AdaptMConditional StatMech.Probability
open StatMech.OSSS.MonotonicFK
open StatMech.OSSS.AdaptDisintegration
open OSSS.GrandCoupling OSSS.Coding
open StatMech.OSSS.RevealmentBoundAssembly

variable {E : Type*} [Fintype E] [DecidableEq E]












noncomputable def truncIndC {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ)
    (X : ConfigSpace E) (t : ℕ) : ℝ :=
  if t ≤ stopValC σ f X then (1 : ℝ) else 0



lemma truncInd_eq_truncIndC (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (U : Fin n → ℝ) (t : ℕ) :
    truncInd μ σ f U t = truncIndC σ f (codeMap μ (σ : Fin n → E) U) t := by
  unfold truncInd truncIndC
  rw [stopVal_eq_stopValC]






noncomputable def reachInd {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ)
    (i : ℕ) (X : ConfigSpace E) : ℝ :=
  if detAtC (σ : Fin n → E) f X i then (0 : ℝ) else 1










theorem truncIndC_succ_eq_reachInd {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ)
    (X : ConfigSpace E) (i : ℕ) :
    truncIndC σ f X (i + 1) = reachInd σ f i X := by
  unfold truncIndC reachInd
  by_cases hdet : detAtC (σ : Fin n → E) f X i
  · 
    have hle : stopValC σ f X ≤ i := (cmn_stopValC_le_iff σ f X i).mpr hdet
    rw [if_neg (by omega : ¬ i + 1 ≤ stopValC σ f X), if_pos hdet]
  · 
    
    have hgt : ¬ stopValC σ f X ≤ i := fun h => hdet ((cmn_stopValC_le_iff σ f X i).mp h)
    rw [if_pos (by omega : i + 1 ≤ stopValC σ f X), if_neg hdet]











noncomputable def reachProb (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (e : E) : ℝ :=
  Lindeberg.mean μ (reachInd σ f (σ.symm e : ℕ))









theorem revealAdapt_eq_truncSum (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ) (e : E) :
    revealAdapt μ σ f e = ∑ X, truncIndC σ f X ((σ.symm e : ℕ) + 1) * μ X := by
  unfold revealAdapt
  rw [integral_prod _ (integrable_truncInd μ σ f ((σ.symm e : ℕ) + 1))]
  have hredU : (∫ U, (∫ _V, truncInd μ σ f U ((σ.symm e : ℕ) + 1) ∂(Vcube n)) ∂(Vcube n))
      = ∫ U, truncInd μ σ f U ((σ.symm e : ℕ) + 1) ∂(Vcube n) := by
    apply integral_congr_ae; apply Filter.Eventually.of_forall; intro U
    simp only; rw [integral_const]; simp
  rw [hredU]
  rw [show (fun U => truncInd μ σ f U ((σ.symm e : ℕ) + 1))
      = (fun U => truncIndC σ f (codeMap μ (σ : Fin n → E) U) ((σ.symm e : ℕ) + 1)) from by
    funext U; rw [truncInd_eq_truncIndC]]
  rw [integral_g_codeMap μ hpos hμ1 σ (fun X => truncIndC σ f X ((σ.symm e : ℕ) + 1))]












theorem revealAdapt_eq_reachProb {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ) (e : E) :
    revealAdapt μ σ f e = reachProb μ σ f e := by
  rw [revealAdapt_eq_truncSum μ hpos hμ1 σ f e]
  unfold reachProb Lindeberg.mean
  apply Finset.sum_congr rfl
  intro X _
  rw [truncIndC_succ_eq_reachInd σ f X (σ.symm e : ℕ)]








theorem reachProb_nonneg {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ) (e : E) :
    0 ≤ reachProb μ σ f e := by
  unfold reachProb Lindeberg.mean
  apply Finset.sum_nonneg
  intro X _
  apply mul_nonneg _ (le_of_lt (hpos X))
  unfold reachInd; split <;> norm_num



theorem reachProb_le_one {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ) (e : E) :
    reachProb μ σ f e ≤ 1 := by
  unfold reachProb Lindeberg.mean
  calc (∑ X, reachInd σ f (σ.symm e : ℕ) X * μ X)
      ≤ ∑ X, (1 : ℝ) * μ X := by
        apply Finset.sum_le_sum
        intro X _
        apply mul_le_mul_of_nonneg_right _ (le_of_lt (hpos X))
        unfold reachInd; split <;> norm_num
    _ = 1 := by simp only [one_mul]; exact hμ1













theorem revealAdapt_le_reachProb {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ) (e : E) :
    revealAdapt μ σ f e ≤ reachProb μ σ f e :=
  le_of_eq (revealAdapt_eq_reachProb hpos hμ1 σ f e)





theorem revealAdapt_le_of_reachProb_le {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ)
    {D : ℝ} (hreach : ∀ e, reachProb μ σ f e ≤ D) :
    ∀ e, revealAdapt μ σ f e ≤ D :=
  fun e => (revealAdapt_le_reachProb hpos hμ1 σ f e).trans (hreach e)















theorem os_cov_lower_bound_from_reachBound {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (hFKG : FKGLatticeCondition μ) (hmono : IsMonotonicMeasure μ)
    {n : ℕ} (σ : Fin n ≃ E) {f : ConfigSpace E → ℝ} (hf : Monotone f) (hf0 : 0 ≤ f)
    (hf1 : ∀ ω, f ω ≤ 1) (hidem : ∀ ω, f ω * f ω = f ω)
    (D : ℝ) (hDpos : 0 < D) (hreach : ∀ e, reachProb μ σ f e ≤ D) :
    Lindeberg.mean μ f * (1 - Lindeberg.mean μ f) / D
      ≤ ∑ e, Lindeberg.cov μ f (Lindeberg.coord e) :=
  os_cov_lower_bound_assembled hpos hμ1 hFKG hmono σ hf hf0 hf1 hidem D hDpos
    (revealAdapt_le_of_reachProb_le hpos hμ1 σ f hreach)















theorem os_cov_lower_bound_reach_poincare {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (hFKG : FKGLatticeCondition μ) (hmono : IsMonotonicMeasure μ)
    {n : ℕ} (σ : Fin n ≃ E) {f : ConfigSpace E → ℝ} (hf : Monotone f) (hf0 : 0 ≤ f)
    (hf1 : ∀ ω, f ω ≤ 1) (hidem : ∀ ω, f ω * f ω = f ω) :
    Lindeberg.mean μ f * (1 - Lindeberg.mean μ f)
      ≤ ∑ e, Lindeberg.cov μ f (Lindeberg.coord e) := by
  have h := os_cov_lower_bound_from_reachBound hpos hμ1 hFKG hmono σ hf hf0 hf1 hidem
    1 (by norm_num) (fun e => reachProb_le_one hpos hμ1 σ f e)
  simpa using h

end RevealmentBoxCrossing

end OSSS

end StatMech
