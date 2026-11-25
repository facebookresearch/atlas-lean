/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Probability.SDE.Stability
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
variable {F : Filtration ℝ≥0 mΩ} {B X Y : ℝ≥0 → Ω → ℝ}
variable (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
variable (hInd : ∀ s t, s ≤ t →
  Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) P)
variable {σ b : ℝ → ℝ} {x y : ℝ} {K : ℝ≥0}

example (hX : IsScalarSDESolution P F B σ b x X) (hb : LipschitzWith K b) (t : ℝ≥0) :
    MemLp (X t) 2 P := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  exact hX.memLp hb t

example (hX : IsScalarSDESolution P F B σ b x X)
    (hY : IsScalarSDESolution P F B σ b y Y)
    (hσ : LipschitzWith K σ) (hb : LipschitzWith K b) {t T : ℝ≥0} (ht : t ≤ T) :
    ∫ ω, (X t ω - Y t ω)^2 ∂P ≤ 3 * (x - y)^2 * Real.exp (3 * (K : ℝ)^2 * (1 + T) * (t : ℝ)) :=
  IsScalarSDESolution.integral_sub_sq_le hB hBF hInd hX hY hσ hb ht

example (hX : IsScalarSDESolution P F B σ b x X)
    (hY : IsScalarSDESolution P F B σ b y Y)
    (hσ : LipschitzWith K σ) (hb : LipschitzWith K b) :
    ∫⁻ ω, ‖X 0 ω - Y 0 ω‖ₑ^2 ∂P ≤ ENNReal.ofReal (3 * (x - y)^2) := by
  simpa using IsScalarSDESolution.lintegral_sub_sq_le hB hBF hInd hX hY hσ hb
    (t := 0) (T := 0) le_rfl

example (hX : IsScalarSDESolution P F B σ b x X)
    (hY : IsScalarSDESolution P F B σ b x Y)
    (hσ : LipschitzWith K σ) (hb : LipschitzWith K b) : X ≡ᵐ[P] Y :=
  IsScalarSDESolution.indistinguishable hB hBF hInd hX hY hσ hb

example (t : ℝ≥0) : ∫ _ω : Ω, ((1 : ℝ) - 4)^2 ∂P ≤ 27 := by
  have h := IsScalarSDESolution.integral_sub_sq_le hB hBF hInd
    (constant_solution hB hBF hInd 1) (constant_solution hB hBF hInd 4)
    (LipschitzWith.const 0) (LipschitzWith.const 0) (t := t) (T := t) le_rfl
  norm_num at h ⊢
  exact h

example : (Real.exp 1 - 4 * Real.exp 1)^2 ≤ 27 * Real.exp 9 := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  have h := IsScalarSDESolution.integral_sub_sq_le hB hBF hInd
    (exponential_solution hB hBF hInd 1) (exponential_solution hB hBF hInd 4)
    (LipschitzWith.const' 0) LipschitzWith.id (t := 1) (T := 2) (by norm_num)
  norm_num [integral_const] at h ⊢
  exact h

example (hY : IsScalarSDESolution P F B (fun _ ↦ 0) id x Y) :
    Y ≡ᵐ[P] (fun t _ ↦ x * Real.exp (t : ℝ)) :=
  IsScalarSDESolution.indistinguishable hB hBF hInd hY
    (exponential_solution hB hBF hInd x) (LipschitzWith.const' 0) LipschitzWith.id

end
