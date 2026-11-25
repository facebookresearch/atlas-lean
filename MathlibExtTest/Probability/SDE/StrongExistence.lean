/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Probability.SDE.StrongExistence
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

private theorem zero_ito {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) P)
    (t : ℝ≥0) : itoIntegral P F B (fun _ _ ↦ 0) t =ᵐ[P] (fun _ ↦ 0) := by
  have hi := lintegral_itoIntegral_sq_of_isProgressive hB hBF hInd
    (isProgressive_const F (0 : ℝ)) t (by simp)
  have hz : ∫⁻ ω, ‖itoIntegral P F B (fun _ _ ↦ 0) t ω‖ₑ^2 ∂P = 0 := by simpa using hi
  have hm := (memLp_itoIntegral P F B (fun _ _ ↦ 0) t).aestronglyMeasurable.aemeasurable
  have ha := (lintegral_eq_zero_iff' (hm.eNorm.pow_const 2)).1 hz
  filter_upwards [ha] with ω hω
  simpa only [Pi.zero_apply, sq_eq_zero_iff, eNorm_eq_zero] using hω

private theorem constant_solution {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) P)
    (x : ℝ) : IsScalarSDESolution P F B (fun _ ↦ 0) (fun _ ↦ 0) x (fun _ _ ↦ x) := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  refine ⟨fun _ ↦ measurable_const, fun _ ↦ continuous_const, ?_, ?_⟩
  · intro t
    simp only [integrandDist, sub_zero, lintegral_const, Measure.restrict_apply_univ,
      Real.volume_Ioc]
    finiteness
  · intro t
    filter_upwards [zero_ito hB hBF hInd t] with ω hω
    simp [hω]

private theorem exponential_solution {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) P)
    (x : ℝ) : IsScalarSDESolution P F B (fun _ ↦ 0) id x
      (fun t _ ↦ x * Real.exp (t : ℝ)) := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  have hc : Continuous fun s : ℝ ↦ x * Real.exp (s.toNNReal : ℝ) := by fun_prop
  refine ⟨fun _ ↦ measurable_const, fun _ ↦ by fun_prop, ?_, ?_⟩
  · intro T
    have hs : IntegrableOn (fun s : ℝ ↦ (x * Real.exp (s.toNNReal : ℝ))^2)
        (Ioc (0 : ℝ) T) := ((hc.pow 2).intervalIntegrable 0 T).1
    have he := ofReal_integral_eq_lintegral_ofReal hs
      (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _)
    have hinner : (∫⁻ s in Ioc (0 : ℝ) T, ‖x * Real.exp (s.toNNReal : ℝ)‖ₑ^2) ≠ ∞ := by
      simp only [Real.eNorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
      rw [← he]
      simp
    simpa only [integrandDist, sub_zero, lintegral_const, measure_univ, mul_one] using hinner
  · intro t
    have he : (∫ s in (0 : ℝ)..t, x * Real.exp (s.toNNReal : ℝ)) = x * (Real.exp (t : ℝ) - 1) := by
      calc
        _ = ∫ s in (0 : ℝ)..t, x * Real.exp s := by
          apply intervalIntegral.integral_congr
          intro s hs
          rw [uIcc_of_le t.coe_nonneg] at hs
          dsimp only
          rw [Real.coe_toNNReal s hs.1]
        _ = _ := by rw [intervalIntegral.integral_const_mul, integral_exp]; simp
    filter_upwards [zero_ito hB hBF hInd t] with ω hω
    simp only [id_eq, hω, add_zero]
    rw [he]
    ring

section
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {F : Filtration ℝ≥0 mΩ} [F.IsComplete P] {B : ℝ≥0 → Ω → ℝ}
variable (hB : IsBrownianReal B P) (hBF : Adapted F B)
variable (hInd : ∀ s t, s ≤ t →
  Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) P)

example : ∃ Y : ℝ≥0 → Ω → ℝ,
    IsScalarSDESolution P F B (fun _ ↦ 0) id 2 Y ∧
    Y ≡ᵐ[P] (fun t _ ↦ 2 * Real.exp (t : ℝ)) := by
  obtain ⟨Y, hY, -, hu⟩ := exists_unique_scalar_sde_solution hB hBF hInd
    (LipschitzWith.const' 0) LipschitzWith.id 2
  exact ⟨Y, hY, hu _ (exponential_solution hB.toIsPreBrownianReal hBF hInd 2)⟩

example : ∃ Y : ℝ≥0 → Ω → ℝ,
    IsScalarSDESolution P F B (fun _ ↦ (3 : ℝ)) (fun z ↦ -2 * z) 4 Y ∧
    (∫⁻ ω, (⨆ s : Icc (0 : ℝ≥0) 1, ‖Y s ω‖ₑ)^2 ∂P) ≤
      ENNReal.ofReal (480 * Real.exp 144) ∧
    ∀ Z, IsScalarSDESolution P F B (fun _ ↦ (3 : ℝ)) (fun z ↦ -2 * z) 4 Z → Y ≡ᵐ[P] Z := by
  have hb : LipschitzWith 2 (fun z : ℝ ↦ -2 * z) := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    simp only [dist_eq_norm, Real.norm_eq_abs]
    rw [show -2 * u - -2 * v = -2 * (u - v) by ring, abs_mul]
    norm_num
  obtain ⟨Y, hY, hm, hu⟩ := exists_unique_scalar_sde_solution hB hBF hInd
    (LipschitzWith.const' 3) hb 4
  refine ⟨Y, hY, ?_, hu⟩
  have h := hm 1 2 (by norm_num)
  norm_num at h ⊢
  exact h

example : ∃ Y : ℝ≥0 → Ω → ℝ,
    IsScalarSDESolution P F B abs (fun z ↦ z + 1) 2 Y ∧
    (∫⁻ ω, (⨆ s : Icc (0 : ℝ≥0) 1, ‖Y s ω‖ₑ)^2 ∂P) ≤
      ENNReal.ofReal (36 * Real.exp 36) := by
  have ha : LipschitzWith 1 (abs : ℝ → ℝ) := by
    simpa only [Real.norm_eq_abs] using!
      (lipschitzWith_one_norm : LipschitzWith 1 (norm : ℝ → ℝ))
  have hb : LipschitzWith 1 (fun z : ℝ ↦ z + 1) := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    simp
  obtain ⟨Y, hY, hm, -⟩ := exists_unique_scalar_sde_solution hB hBF hInd ha hb 2
  refine ⟨Y, hY, ?_⟩
  have h := hm 1 2 (by norm_num)
  norm_num at h ⊢
  exact h

example : ∃ Y : ℝ≥0 → Ω → ℝ,
    IsScalarSDESolution P F B (fun _ ↦ 0) (fun _ ↦ 0) 5 Y ∧
    Y ≡ᵐ[P] (fun _ _ ↦ 5) ∧
    ∀ T : ℝ≥0, (∫⁻ ω, (⨆ s : Icc (0 : ℝ≥0) T, ‖Y s ω‖ₑ)^2 ∂P) ≤ 75 := by
  obtain ⟨Y, hY, hm, hu⟩ := exists_unique_scalar_sde_solution hB hBF hInd
    (LipschitzWith.const 0) (LipschitzWith.const 0) 5
  refine ⟨Y, hY, hu _ (constant_solution hB.toIsPreBrownianReal hBF hInd 5), ?_⟩
  intro T
  have h := hm T T le_rfl
  norm_num at h
  exact h
end

section
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {F : Filtration ℝ≥0 mΩ} {B X : ℝ≥0 → Ω → ℝ}
variable (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
variable (hInd : ∀ s t, s ≤ t →
  Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) P)

example {σ b : ℝ → ℝ} {K : ℝ≥0} {x : ℝ}
    (hX : IsScalarSDESolution P F B σ b x X) (hσ : LipschitzWith K σ) (hb : LipschitzWith K b) :
    (∫⁻ ω, (⨆ s : Icc (0 : ℝ≥0) 0, ‖X s ω‖ₑ)^2 ∂P) ≤ ENNReal.ofReal (3 * x^2) := by
  simpa using IsScalarSDESolution.lintegral_iSup_sq_le hB hBF hInd hX hσ hb
    (t := 0) (T := 0) le_rfl

example (hX : IsScalarSDESolution P F B (fun _ ↦ (3 : ℝ)) (fun _ ↦ (2 : ℝ)) 5 X) :
    (∫⁻ ω, (⨆ s : Icc (0 : ℝ≥0) 2, ‖X s ω‖ₑ)^2 ∂P) ≤ 603 := by
  have h := IsScalarSDESolution.lintegral_iSup_sq_le hB hBF hInd hX
    (LipschitzWith.const 3) (LipschitzWith.const 2) (t := 2) (T := 2) le_rfl
  norm_num at h ⊢
  exact h
end
