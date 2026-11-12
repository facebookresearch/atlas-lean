/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






































































import Code.OSSS.SpliceST1

open scoped BigOperators ENNReal
open Finset MeasureTheory

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

namespace StatMech

namespace OSSS

namespace AdaptDisintegration

open OSSS.Monotonic OSSS.Coding OSSS.GrandCoupling OSSS.GrandCouplingAssembly
open StatMech.Probability OSSS.AdaptiveTau OSSS.AdaptMConditional

variable {E : Type*} [Fintype E] [DecidableEq E]










lemma mmr_join_mono_tail {n : ℕ} (t : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ)
    {B B' : {i : Fin n // ¬ (i : ℕ) < t} → ℝ} (hBB : B ≤ B') :
    acp_join t A B ≤ acp_join t A B' := by
  intro i
  by_cases hit : (i : ℕ) < t
  · rw [tsc_acp_join_head t A B i hit, tsc_acp_join_head t A B' i hit]
  · rw [tsc_acp_join_tail t A B i hit, tsc_acp_join_tail t A B' i hit]
    exact hBB ⟨i, hit⟩














lemma mmr_margRand_eq_of_stop_le (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f g : ConfigSpace E → ℝ) (t s : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ)
    (hstop : ∀ B : {i : Fin n // ¬ (i : ℕ) < t} → ℝ, stopVal μ σ f (acp_join t A B) ≤ s) :
    atl_margRand μ σ f g t s A
      = (fun _ : {i : Fin n // ¬ (i : ℕ) < t} → ℝ =>
          ∫ V, g (codeMap μ (σ : Fin n → E) V) ∂(Vcube n)) := by
  funext B
  show (∫ V, g (codeMap μ (σ : Fin n → E)
          (adaptWt (acp_join t A B) V (stopVal μ σ f (acp_join t A B)) s)) ∂(Vcube n))
      = ∫ V, g (codeMap μ (σ : Fin n → E) V) ∂(Vcube n)
  congr 1; funext V
  rw [adaptWt_ge_stop (acp_join t A B) V (stopVal μ σ f (acp_join t A B)) s (hstop B)]








theorem mmr_margMonoRand_of_stop_le (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f g : ConfigSpace E → ℝ) (t s : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ)
    (hstop : ∀ B : {i : Fin n // ¬ (i : ℕ) < t} → ℝ, stopVal μ σ f (acp_join t A B) ≤ s) :
    atl_MargMonoRand μ σ f g t s A := by
  show Monotone (atl_margRand μ σ f g t s A)
  rw [mmr_margRand_eq_of_stop_le μ σ f g t s A hstop]
  exact monotone_const





theorem mmr_margMonoRand_at_n (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f g : ConfigSpace E → ℝ) (t : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
    atl_MargMonoRand μ σ f g t n A :=
  mmr_margMonoRand_of_stop_le μ σ f g t n A (fun B => stopVal_le μ σ f (acp_join t A B))














lemma mmr_margRand_f_at_zero_eq (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (t : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
    atl_margRand μ σ f f t 0 A
      = (fun B : {i : Fin n // ¬ (i : ℕ) < t} → ℝ =>
          f (codeMap μ (σ : Fin n → E) (acp_join t A B))) := by
  funext B
  show (∫ V, f (codeMap μ (σ : Fin n → E)
          (adaptWt (acp_join t A B) V (stopVal μ σ f (acp_join t A B)) 0)) ∂(Vcube n))
      = f (codeMap μ (σ : Fin n → E) (acp_join t A B))
  rw [show (fun V => f (codeMap μ (σ : Fin n → E)
          (adaptWt (acp_join t A B) V (stopVal μ σ f (acp_join t A B)) 0)))
        = (fun _ : Fin n → ℝ => f (codeMap μ (σ : Fin n → E) (acp_join t A B))) from by
    funext V; exact f_adapt_zero_eq σ (acp_join t A B) V]
  rw [integral_const, probReal_univ]; simp








theorem mmr_margMonoRand_f_at_zero {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hmono : IsMonotonicMeasure μ) {n : ℕ} (σ : Fin n ≃ E) {f : ConfigSpace E → ℝ}
    (hf : Monotone f) (t : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
    atl_MargMonoRand μ σ f f t 0 A := by
  show Monotone (atl_margRand μ σ f f t 0 A)
  rw [mmr_margRand_f_at_zero_eq μ σ f t A]
  intro B B' hBB
  exact hf ((codeMap_mono_u hpos hmono (σ : Fin n → E)) (mmr_join_mono_tail t A hBB))












theorem mmr_margMonoRand_of_const {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hmono : IsMonotonicMeasure μ) {n : ℕ} (σ : Fin n ≃ E) {f g : ConfigSpace E → ℝ}
    (hg : Monotone g) {Cg : ℝ} (hgC : ∀ ω, |g ω| ≤ Cg) (t s : ℕ)
    (A : {i : Fin n // (i : ℕ) < t} → ℝ) (m₀ : ℕ)
    (hconst : ∀ B : {i : Fin n // ¬ (i : ℕ) < t} → ℝ, stopVal μ σ f (acp_join t A B) = m₀) :
    atl_MargMonoRand μ σ f g t s A :=
  atl_margMonoRand_of_const hpos hmono σ hg hgC t s A m₀ hconst

end AdaptDisintegration

end OSSS

end StatMech
