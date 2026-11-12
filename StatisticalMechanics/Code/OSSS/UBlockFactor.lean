/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
















































import Code.OSSS.AdaptDisintegration

open scoped BigOperators ENNReal
open Finset MeasureTheory

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace StatMech

namespace OSSS

namespace AdaptDisintegration

open StatMech.Probability










noncomputable def ubfHead (n t : ℕ) : Measure ({i : Fin n // (i : ℕ) < t} → ℝ) :=
  Measure.pi (fun _ => unitMeasure)



noncomputable def ubfTail (n t : ℕ) : Measure ({i : Fin n // ¬ (i : ℕ) < t} → ℝ) :=
  Measure.pi (fun _ => unitMeasure)

instance (n t : ℕ) : IsProbabilityMeasure (ubfHead n t) := by
  unfold ubfHead; infer_instance

instance (n t : ℕ) : IsProbabilityMeasure (ubfTail n t) := by
  unfold ubfTail; infer_instance





noncomputable def ubfSplit (n t : ℕ) :
    (Fin n → ℝ) ≃ᵐ
      (({i : Fin n // (i : ℕ) < t} → ℝ) × ({i : Fin n // ¬ (i : ℕ) < t} → ℝ)) :=
  MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => ℝ) (fun i => (i : ℕ) < t)


lemma ubfSplit_apply_fst (n t : ℕ) (U : Fin n → ℝ) (i : {i : Fin n // (i : ℕ) < t}) :
    ((ubfSplit n t) U).1 i = U (i : Fin n) := rfl


lemma ubfSplit_apply_snd (n t : ℕ) (U : Fin n → ℝ) (i : {i : Fin n // ¬ (i : ℕ) < t}) :
    ((ubfSplit n t) U).2 i = U (i : Fin n) := rfl












theorem ubf_pi_block_split (n t : ℕ) :
    MeasurePreserving (ubfSplit n t) (cube n) ((ubfHead n t).prod (ubfTail n t)) := by
  show MeasurePreserving (ubfSplit n t) (Measure.pi (fun _ : Fin n => unitMeasure))
    ((Measure.pi (fun _ : {i : Fin n // (i : ℕ) < t} => unitMeasure)).prod
      (Measure.pi (fun _ : {i : Fin n // ¬ (i : ℕ) < t} => unitMeasure)))
  exact measurePreserving_piEquivPiSubtypeProd (fun _ : Fin n => unitMeasure) (fun i => (i : ℕ) < t)










lemma ubf_integrable_of_bdd {n : ℕ} {F : (Fin n → ℝ) → ℝ} (hF : Measurable F)
    {C : ℝ} (hC : ∀ U, |F U| ≤ C) : Integrable F (cube n) :=
  ContinuousFKG.integrable_of_bdd (cube n) hF hC











theorem ubf_integral_factor (n t : ℕ)
    {h₀ : ({i : Fin n // (i : ℕ) < t} → ℝ) → ℝ} (hh₀m : Measurable h₀)
    {Ch : ℝ} (hh₀C : ∀ A, |h₀ A| ≤ Ch)
    {F : (Fin n → ℝ) → ℝ} (hFm : Measurable F)
    {CF : ℝ} (hFC : ∀ U, |F U| ≤ CF) :
    (∫ U, h₀ (((ubfSplit n t) U).1) * F U ∂(cube n))
      = ∫ A, h₀ A * (∫ B, F ((ubfSplit n t).symm (A, B)) ∂(ubfTail n t)) ∂(ubfHead n t) := by
  have hCh0 : 0 ≤ Ch := le_trans (abs_nonneg _) (hh₀C (fun _ => 0))
  
  set G : (({i : Fin n // (i : ℕ) < t} → ℝ) × ({i : Fin n // ¬ (i : ℕ) < t} → ℝ)) → ℝ :=
    fun p => h₀ p.1 * F ((ubfSplit n t).symm p) with hG
  
  have hsymm_meas : Measurable (ubfSplit n t).symm := (ubfSplit n t).symm.measurable
  have hGm : Measurable G := (hh₀m.comp measurable_fst).mul (hFm.comp hsymm_meas)
  have hGC : ∀ p, |G p| ≤ Ch * CF := by
    intro p; rw [hG, abs_mul]
    exact mul_le_mul (hh₀C _) (hFC _) (abs_nonneg _) hCh0
  have hGint : Integrable G ((ubfHead n t).prod (ubfTail n t)) :=
    ContinuousFKG.integrable_of_bdd _ hGm hGC
  
  have hmp := ubf_pi_block_split n t
  have hpull : (∫ U, h₀ (((ubfSplit n t) U).1) * F U ∂(cube n))
      = ∫ p, G p ∂((ubfHead n t).prod (ubfTail n t)) := by
    rw [← hmp.integral_comp' G]
    apply integral_congr_ae; apply Filter.Eventually.of_forall; intro U
    simp only [hG]
    rw [MeasurableEquiv.symm_apply_apply]
  rw [hpull, integral_prod G hGint]
  
  apply integral_congr_ae; apply Filter.Eventually.of_forall; intro A
  simp only [hG]
  rw [integral_const_mul]













theorem ubf_integral_factor_of_factors (n t : ℕ)
    {h : (Fin n → ℝ) → ℝ} {h₀ : ({i : Fin n // (i : ℕ) < t} → ℝ) → ℝ}
    (hfac : ∀ U, h U = h₀ (((ubfSplit n t) U).1))
    (hh₀m : Measurable h₀) {Ch : ℝ} (hh₀C : ∀ A, |h₀ A| ≤ Ch)
    {F : (Fin n → ℝ) → ℝ} (hFm : Measurable F) {CF : ℝ} (hFC : ∀ U, |F U| ≤ CF) :
    (∫ U, h U * F U ∂(cube n))
      = ∫ A, h₀ A * (∫ B, F ((ubfSplit n t).symm (A, B)) ∂(ubfTail n t)) ∂(ubfHead n t) := by
  rw [show (∫ U, h U * F U ∂(cube n))
        = ∫ U, h₀ (((ubfSplit n t) U).1) * F U ∂(cube n) from by
    apply integral_congr_ae; apply Filter.Eventually.of_forall; intro U; simp only [hfac]]
  exact ubf_integral_factor n t hh₀m hh₀C hFm hFC

end AdaptDisintegration

end OSSS

end StatMech
