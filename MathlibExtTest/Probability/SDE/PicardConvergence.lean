/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Probability.SDE.PicardConvergence

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

section
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {F : Filtration ℝ≥0 mΩ} [F.IsComplete P] {B : ℝ≥0 → Ω → ℝ}
variable (hB : IsBrownianReal B P) (hBF : Adapted F B)
variable (hInd : ∀ s t, s ≤ t →
  Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) P)

example : ∃ X J : ℕ → ℝ≥0 → Ω → ℝ,
    X 0 = (fun _ _ ↦ (1 : ℝ)) ∧
    (∀ n t, J n t =ᵐ[P] itoIntegral P F B (fun s ω ↦ |X n s ω|) t) ∧
    (∀ n, X (n + 1) = fun t ω ↦ 1 + J n t ω + ∫ s in (0 : ℝ)..t, X n s.toNNReal ω) ∧
    (∫⁻ ω, (⨆ s : Icc (0 : ℝ≥0) 1, ‖X 3 s ω - X 2 s ω‖ₑ)^2 ∂P) ≤ 288 := by
  have ha : LipschitzWith 1 (abs : ℝ → ℝ) := by
    simpa only [Real.norm_eq_abs] using!
      (lipschitzWith_one_norm : LipschitzWith 1 (norm : ℝ → ℝ))
  obtain ⟨X, J, h0, hX, hJ⟩ := exists_scalar_sde_picard_sequence hB hBF hInd
    ha LipschitzWith.id 1
  refine ⟨X, J, h0, fun n ↦ (hJ n).2.2.2.1, fun n ↦ (hJ n).2.2.2.2, ?_⟩
  have h := lintegral_iSup_picard_succ_sub_sq_le hB.toIsPreBrownianReal hBF hInd
    ha LipschitzWith.id 1 X J h0 hX hJ 2 2 1 (by norm_num)
  norm_num at h
  exact h

example : ∃ X J : ℕ → ℝ≥0 → Ω → ℝ,
    (∀ n t, J n t =ᵐ[P] itoIntegral P F B (fun _ _ ↦ (-3 : ℝ)) t) ∧
    (∀ n, X (n + 1) = fun t ω ↦ 5 + J n t ω + ∫ _s in (0 : ℝ)..t, (2 : ℝ)) ∧
    ∀ T : ℝ≥0, (∫⁻ ω, (⨆ s : Icc (0 : ℝ≥0) T, ‖X 2 s ω - X 1 s ω‖ₑ)^2 ∂P) = 0 := by
  obtain ⟨X, J, h0, hX, hJ⟩ := exists_scalar_sde_picard_sequence hB hBF hInd
    (LipschitzWith.const (-3)) (LipschitzWith.const 2) 5
  refine ⟨X, J, fun n ↦ (hJ n).2.2.2.1, fun n ↦ (hJ n).2.2.2.2, ?_⟩
  intro T
  have h := lintegral_iSup_picard_succ_sub_sq_le hB.toIsPreBrownianReal hBF hInd
    (LipschitzWith.const (-3)) (LipschitzWith.const 2) 5 X J h0 hX hJ T 1 T le_rfl
  exact le_antisymm (by simpa using h) bot_le

example : ∃ X J : ℕ → ℝ≥0 → Ω → ℝ, ∃ Y : ℝ≥0 → Ω → ℝ,
    (∀ n t, J n t =ᵐ[P] itoIntegral P F B (fun s ω ↦ |X n s ω|) t) ∧
    (∀ n, X (n + 1) = fun t ω ↦ 1 + J n t ω + ∫ s in (0 : ℝ)..t, X n s.toNNReal ω) ∧
    IsProgressive F Y ∧ (∀ ω, Continuous (Y · ω)) ∧
    (∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      TendstoUniformlyOn (fun n s ↦ X n s ω) (Y · ω) atTop (Icc 0 T)) ∧
    (∫⁻ ω, (⨆ s : Icc (0 : ℝ≥0) 2, ‖Y s ω‖ₑ)^2 ∂P) ≠ ∞ ∧
    Tendsto (fun n ↦ ∫⁻ ω, (⨆ s : Icc (0 : ℝ≥0) 2,
      ‖X n s ω - Y s ω‖ₑ)^2 ∂P) atTop (𝓝 0) := by
  have ha : LipschitzWith 1 (abs : ℝ → ℝ) := by
    simpa only [Real.norm_eq_abs] using!
      (lipschitzWith_one_norm : LipschitzWith 1 (norm : ℝ → ℝ))
  obtain ⟨X, J, h0, hX, hJ⟩ := exists_scalar_sde_picard_sequence hB hBF hInd
    ha LipschitzWith.id 1
  obtain ⟨Y, hYp, hYc, hU, hL⟩ := exists_scalar_sde_picard_limit hB.toIsPreBrownianReal
    hBF hInd ha LipschitzWith.id 1 X J h0 hX hJ
  exact ⟨X, J, Y, fun n ↦ (hJ n).2.2.2.1, fun n ↦ (hJ n).2.2.2.2,
    hYp, hYc, hU, (hL 2).1, (hL 2).2⟩
end

section
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {F : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}
variable (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
variable (hInd : ∀ s t, s ≤ t →
  Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) P)
variable {σ b : ℝ → ℝ} {K : ℝ≥0} (hσ : LipschitzWith K σ) (hb : LipschitzWith K b)
variable (x : ℝ) (X J : ℕ → ℝ≥0 → Ω → ℝ) (h0 : X 0 = fun _ _ ↦ x)
variable (hX : ∀ n, IsProgressive F (X n) ∧ (∀ ω, Continuous (X n · ω)) ∧
  ∀ T, integrandDist P (X n) (fun _ _ ↦ 0) T ≠ ∞)
variable (hJ : ∀ n, Martingale (J n) F P ∧ IsProgressive F (J n) ∧
  (∀ ω, Continuous (J n · ω)) ∧
  (∀ t, J n t =ᵐ[P] itoIntegral P F B (fun s ω ↦ σ (X n s ω)) t) ∧
  X (n + 1) = fun t ω ↦ x + J n t ω + ∫ s in (0 : ℝ)..t, b (X n s.toNNReal ω))

example (n : ℕ) :
    (∫⁻ ω, (⨆ s : Icc (0 : ℝ≥0) 0, ‖X (n + 1) s ω - X n s ω‖ₑ)^2 ∂P) = 0 := by
  have h := lintegral_iSup_picard_succ_sub_sq_le hB hBF hInd hσ hb x X J h0 hX hJ
    0 n 0 le_rfl
  exact le_antisymm (by simpa using h) bot_le

example [F.IsComplete P] : ∃ Y : ℝ≥0 → Ω → ℝ,
    Adapted F Y ∧ (∀ ω, Continuous (Y · ω)) ∧
    ∀ᵐ ω ∂P, ∀ t, Tendsto (fun n ↦ X n t ω) atTop (𝓝 (Y t ω)) := by
  obtain ⟨Y, hYp, hYc, hU, -⟩ := exists_scalar_sde_picard_limit hB hBF hInd
    hσ hb x X J h0 hX hJ
  refine ⟨Y, hYp.adapted, hYc, ?_⟩
  filter_upwards [hU] with ω hω
  intro t
  exact (hω t).tendsto_at ⟨zero_le, le_rfl⟩
end
