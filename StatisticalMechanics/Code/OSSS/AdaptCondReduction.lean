/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


































import Code.OSSS.AdaptCondBBProof2

open scoped BigOperators ENNReal
open Finset MeasureTheory

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace StatMech

namespace OSSS

namespace AdaptDisintegration

open OSSS.Monotonic OSSS.Coding OSSS.GrandCoupling OSSS.GrandCouplingAssembly
open StatMech.Probability OSSS.AdaptiveTau OSSS.AdaptMConditional

variable {E : Type*} [Fintype E] [DecidableEq E]















lemma otc_factor_step (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (t : ℕ)
    {G : (Fin n → ℝ) → ℝ} (hGm : Measurable G) {CG : ℝ} (hGC : ∀ U, |G U| ≤ CG) :
    (∫ U, truncInd μ σ f U (t+1) * G U ∂(cube n))
      = ∫ A, acp_truncHead μ σ f t A
          * (∫ B, G (acp_join t A B) ∂(ubfTail n t)) ∂(ubfHead n t) := by
  have := ubf_integral_factor_of_factors (n := n) (t := t)
    (h := fun U => truncInd μ σ f U (t+1)) (h₀ := acp_truncHead μ σ f t)
    (hfac := acp_truncInd_factors μ σ f t)
    (hh₀m := acp_measurable_truncHead μ σ f t)
    (hh₀C := acp_truncHead_le_one μ σ f t)
    (hFm := hGm) (hFC := hGC)
  convert this using 1


lemma otc_truncHead_nonneg (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (t : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
    0 ≤ acp_truncHead μ σ f t A := truncInd_nonneg μ σ f _ (t + 1)




lemma otc_delta_eq (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (t : ℕ) :
    (∫ U, truncInd μ σ f U (t+1) ∂(cube n))
      = ∫ A, acp_truncHead μ σ f t A ∂(ubfHead n t) := by
  have h := otc_factor_step μ σ f t (G := fun _ : Fin n → ℝ => (1:ℝ))
    measurable_const (CG := 1) (fun _ => by norm_num)
  simp only [mul_one] at h
  rw [h]
  apply integral_congr_ae; apply Filter.Eventually.of_forall; intro A
  rw [integral_const]
  simp






lemma otc_diag_component (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    {f : ConfigSpace E → ℝ} (hfC : ∀ ω, |f ω| ≤ 1) (t : ℕ) (e : E) (s : ℕ)
    (hs : ∀ (A : {i : Fin n // (i : ℕ) < t} → ℝ),
        (∫ B, fiberDiag μ σ f e s (acp_join t A B) ∂(ubfTail n t))
          = Lindeberg.mean μ (fun ω => f ω * Lindeberg.coord e ω)) :
    (∫ U, fiberDiag μ σ f e s U * truncInd μ σ f U (t+1) ∂(cube n))
      = Lindeberg.mean μ (fun ω => f ω * Lindeberg.coord e ω)
          * ∫ U, truncInd μ σ f U (t+1) ∂(cube n) := by
  set Mfe := Lindeberg.mean μ (fun ω => f ω * Lindeberg.coord e ω) with hMfe
  rw [show (∫ U, fiberDiag μ σ f e s U * truncInd μ σ f U (t+1) ∂(cube n))
        = ∫ U, truncInd μ σ f U (t+1) * fiberDiag μ σ f e s U ∂(cube n) from by
    apply integral_congr_ae; apply Filter.Eventually.of_forall; intro U; simp only [mul_comm]]
  rw [otc_factor_step μ σ f t (acp_measurable_fiberDiag μ σ e s)
    (fun U => acp_fiberDiag_le_one μ σ hfC e s U)]
  rw [show (fun A => acp_truncHead μ σ f t A
        * (∫ B, fiberDiag μ σ f e s (acp_join t A B) ∂(ubfTail n t)))
      = (fun A => acp_truncHead μ σ f t A * Mfe) from by
    funext A; rw [hs A]]
  rw [integral_mul_const, otc_delta_eq μ σ f t, mul_comm]





lemma otc_cross_component (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    {f : ConfigSpace E → ℝ} (hfC : ∀ ω, |f ω| ≤ 1) (t : ℕ) (e : E) (s₁ s₂ : ℕ)
    (hs : ∀ (A : {i : Fin n // (i : ℕ) < t} → ℝ),
        Lindeberg.mean μ f * Lindeberg.mean μ (Lindeberg.coord e)
          ≤ ∫ B, fiberCross μ σ f e s₁ s₂ (acp_join t A B) ∂(ubfTail n t)) :
    Lindeberg.mean μ f * Lindeberg.mean μ (Lindeberg.coord e)
        * ∫ U, truncInd μ σ f U (t+1) ∂(cube n)
      ≤ ∫ U, fiberCross μ σ f e s₁ s₂ U * truncInd μ σ f U (t+1) ∂(cube n) := by
  set Mf := Lindeberg.mean μ f with hMf
  set Mc := Lindeberg.mean μ (Lindeberg.coord e) with hMc
  rw [show (∫ U, fiberCross μ σ f e s₁ s₂ U * truncInd μ σ f U (t+1) ∂(cube n))
        = ∫ U, truncInd μ σ f U (t+1) * fiberCross μ σ f e s₁ s₂ U ∂(cube n) from by
    apply integral_congr_ae; apply Filter.Eventually.of_forall; intro U; simp only [mul_comm]]
  rw [otc_factor_step μ σ f t (acp_measurable_fiberCross μ σ e s₁ s₂)
    (fun U => acp_fiberCross_le_one μ σ hfC e s₁ s₂ U)]
  rw [otc_delta_eq μ σ f t]
  rw [show Mf * Mc * ∫ A, acp_truncHead μ σ f t A ∂(ubfHead n t)
        = ∫ A, acp_truncHead μ σ f t A * (Mf * Mc) ∂(ubfHead n t) from by
    rw [integral_mul_const, mul_comm]]
  have hinnerm : Measurable (fun A : {i : Fin n // (i : ℕ) < t} → ℝ =>
      ∫ B, fiberCross μ σ f e s₁ s₂ (acp_join t A B) ∂(ubfTail n t)) := by
    have hjm : Measurable (fun p : ({i : Fin n // (i : ℕ) < t} → ℝ) × ({i : Fin n // ¬ (i : ℕ) < t} → ℝ) =>
        fiberCross μ σ f e s₁ s₂ (acp_join t p.1 p.2)) :=
      (acp_measurable_fiberCross μ σ e s₁ s₂).comp (ubfSplit n t).symm.measurable
    exact hjm.stronglyMeasurable.integral_prod_right'.measurable
  refine integral_mono ?_ ?_ (fun A => ?_)
  · refine ContinuousFKG.integrable_of_bdd _
      ((acp_measurable_truncHead μ σ f t).mul measurable_const) (C := 1 * |Mf * Mc|)
      (fun A => ?_)
    rw [abs_mul]
    exact mul_le_mul (acp_truncHead_le_one μ σ f t A) le_rfl (abs_nonneg _) (by norm_num)
  · refine ContinuousFKG.integrable_of_bdd _
      ((acp_measurable_truncHead μ σ f t).mul hinnerm) (C := 1 * 1) (fun A => ?_)
    rw [abs_mul]
    refine mul_le_mul (acp_truncHead_le_one μ σ f t A) ?_ (abs_nonneg _) (by norm_num)
    calc |∫ B, fiberCross μ σ f e s₁ s₂ (acp_join t A B) ∂(ubfTail n t)|
        ≤ ∫ B, |fiberCross μ σ f e s₁ s₂ (acp_join t A B)| ∂(ubfTail n t) :=
          abs_integral_le_integral_abs
      _ ≤ ∫ B, (1:ℝ) ∂(ubfTail n t) :=
          integral_mono (ContinuousFKG.integrable_of_bdd _
            (((acp_measurable_fiberCross μ σ e s₁ s₂).comp (ubfSplit n t).symm.measurable).comp
              (measurable_const.prodMk measurable_id)).abs
            (fun B => by rw [abs_abs]; exact acp_fiberCross_le_one μ σ hfC e s₁ s₂ _))
            (integrable_const 1)
            (fun B => acp_fiberCross_le_one μ σ hfC e s₁ s₂ _)
      _ = 1 := by simp
  · exact mul_le_mul_of_nonneg_left (hs A) (otc_truncHead_nonneg μ σ f t A)












theorem otc_adaptCondBBB_of_tailCondLaw {μ : ConfigSpace E → ℝ} {n : ℕ} (σ : Fin n ≃ E)
    {f : ConfigSpace E → ℝ} (hfC : ∀ ω, |f ω| ≤ 1) (hTCL : acp_TailCondLaw μ σ f) :
    AdaptCondBBB μ σ f := by
  intro t htn
  set e := (σ : Fin n → E) ⟨t, htn⟩ with he
  
  refine ⟨?_, ?_, ?_, ?_⟩
  · 
    exact otc_diag_component μ σ hfC t e t (fun A => (hTCL t htn A).1)
  · 
    exact otc_diag_component μ σ hfC t e (t+1) (fun A => (hTCL t htn A).2.1)
  · 
    exact otc_cross_component μ σ hfC t e t (t+1) (fun A => (hTCL t htn A).2.2.1)
  · 
    exact otc_cross_component μ σ hfC t e (t+1) t (fun A => (hTCL t htn A).2.2.2)

end AdaptDisintegration

end OSSS

end StatMech
