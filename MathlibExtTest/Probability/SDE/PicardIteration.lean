/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Probability.SDE.PicardIteration
import MathlibExt.Probability.SDE.Stability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

section
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {F : Filtration ℝ≥0 mΩ} [F.IsComplete P] {B : ℝ≥0 → Ω → ℝ}
variable (hB : IsBrownianReal B P) (hBF : Adapted F B)
variable (hInd : ∀ s t, s ≤ t →
  Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) P)

example : ∃ X : ℝ≥0 → Ω → ℝ,
    IsScalarSDESolution P F B (fun _ ↦ (-3 : ℝ)) (fun _ ↦ (2 : ℝ)) 5 X ∧
    (∫⁻ ω, (⨆ s : Icc (0 : ℝ≥0) 2, ‖X s ω - 5‖ₑ)^2 ∂P) ≤ 176 := by
  obtain ⟨X, J, h0, hX, hJ⟩ := exists_scalar_sde_picard_sequence hB hBF hInd
    (LipschitzWith.const (-3)) (LipschitzWith.const 2) 5
  have he (t : ℝ≥0) (ω : Ω) : X 1 t ω = 5 + J 0 t ω + (t : ℝ) * 2 := by
    rw [(hJ 0).2.2.2.2]
    simp
  refine ⟨X 1, ⟨(hX 1).1.adapted, (hX 1).2.1, (hX 1).2.2, ?_⟩, ?_⟩
  · intro t
    filter_upwards [(hJ 0).2.2.2.1 t] with ω hω
    rw [he, hω]
    simp
  · have hb := lintegral_iSup_ito_const_add_drift_sq_le hB.toIsPreBrownianReal hBF hInd
      (-3) 2 (hJ 0).1 (hJ 0).2.2.1 (hJ 0).2.2.2.1 2
    have hd (s : Icc (0 : ℝ≥0) 2) (ω : Ω) :
        X 1 s ω - 5 = J 0 s ω + (s : ℝ) * 2 := by
      rw [he]
      ring
    norm_num [Real.eNorm_eq_ofReal_abs] at hb
    simpa only [hd, Real.eNorm_eq_ofReal_abs] using hb

example : ∃ X J : ℕ → ℝ≥0 → Ω → ℝ,
    X 0 = (fun _ _ ↦ (1 : ℝ)) ∧
    (∀ n, IsProgressive F (X n) ∧ (∀ ω, Continuous (X n · ω)) ∧
      ∀ T, integrandDist P (X n) (fun _ _ ↦ 0) T ≠ ∞) ∧
    (∀ n t, J n t =ᵐ[P] itoIntegral P F B (fun s ω ↦ |X n s ω|) t) ∧
    ∀ n, X (n + 1) = (fun t ω ↦ 1 + J n t ω + ∫ s in (0 : ℝ)..t, X n s.toNNReal ω) := by
  have ha : LipschitzWith 1 (abs : ℝ → ℝ) := by
    simpa only [Real.norm_eq_abs] using!
      (lipschitzWith_one_norm : LipschitzWith 1 (norm : ℝ → ℝ))
  obtain ⟨X, J, h0, hX, hJ⟩ := exists_scalar_sde_picard_sequence hB hBF hInd
    ha LipschitzWith.id 1
  exact ⟨X, J, h0, hX, fun n ↦ (hJ n).2.2.2.1, fun n ↦ (hJ n).2.2.2.2⟩
end

section
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {F : Filtration ℝ≥0 mΩ} {B X Y J L : ℝ≥0 → Ω → ℝ}
variable (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
variable (hInd : ∀ s t, s ≤ t →
  Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) P)

example (a : ℝ) (hXp : IsProgressive F X) (hYp : IsProgressive F Y)
    (hJm : Martingale J F P) (hLm : Martingale L F P)
    (hJc : ∀ ω, Continuous (J · ω)) (hLc : ∀ ω, Continuous (L · ω))
    (hJe : ∀ t, J t =ᵐ[P] itoIntegral P F B (fun _ _ ↦ a) t)
    (hLe : ∀ t, L t =ᵐ[P] itoIntegral P F B (fun _ _ ↦ a) t)
    (t : ℝ≥0) (hXe : integrandDist P X (fun _ _ ↦ 0) t ≠ ∞)
    (hYe : integrandDist P Y (fun _ _ ↦ 0) t ≠ ∞) :
    (∫⁻ ω, (⨆ s : Icc (0 : ℝ≥0) t, ‖J s ω - L s ω‖ₑ)^2 ∂P) = 0 := by
  have h := lintegral_iSup_ito_version_sub_le hB hBF hInd (LipschitzWith.const a)
    hXp hYp hJm hLm hJc hLc hJe hLe t hXe hYe
  exact le_antisymm (by simpa using h) bot_le

example {H : ℝ≥0 → Ω → ℝ} (hH : IsProgressive F H)
    (hJm : Martingale J F P) (hJc : ∀ ω, Continuous (J · ω))
    (hJe : ∀ t, J t =ᵐ[P] itoIntegral P F B H t) :
    (∫⁻ ω, (⨆ s : Icc (0 : ℝ≥0) 0, ‖J s ω‖ₑ)^2 ∂P) = 0 := by
  have h := lintegral_iSup_ito_version_sq_le hB hBF hInd hH hJm hJc hJe 0 (by simp [integrandDist])
  exact le_antisymm (by simpa [integrandDist] using h) bot_le

example [IsProbabilityMeasure P] :
    (∫⁻ _ω : Ω, (⨆ s : Icc (0 : ℝ≥0) 2,
      ‖(∫ _u in (0 : ℝ)..s, (6 : ℝ)) - (∫ _u in (0 : ℝ)..s, (3 : ℝ))‖ₑ)^2 ∂P) ≤ 36 := by
  have hb : LipschitzWith 3 (fun z : ℝ ↦ 3 * z) := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    simp only [dist_eq_norm, Real.norm_eq_abs]
    rw [show 3 * u - 3 * v = 3 * (u - v) by ring, abs_mul]
    norm_num
  have h := lintegral_iSup_timeIntegral_comp_sub_le P (X := fun _ _ ↦ 2) (Y := fun _ _ ↦ 1)
    hb (fun _ ↦ continuous_const) (fun _ ↦ continuous_const) 2
  norm_num [integrandDist, Real.eNorm_eq_ofReal_abs, Real.volume_Ioc] at h ⊢
  exact h
end

section
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {F : Filtration ℝ≥0 mΩ} {B X Y J L : ℝ≥0 → Ω → ℝ}
variable (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
variable (hInd : ∀ s t, s ≤ t →
  Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) P)

example {σ b : ℝ → ℝ} (hσ : LipschitzWith 1 σ) (hb : LipschitzWith 1 b)
    (hXp : IsProgressive F X) (hYp : IsProgressive F Y)
    (hXc : ∀ ω, Continuous (X · ω)) (hYc : ∀ ω, Continuous (Y · ω))
    (hJm : Martingale J F P) (hLm : Martingale L F P)
    (hJc : ∀ ω, Continuous (J · ω)) (hLc : ∀ ω, Continuous (L · ω))
    (hJe : ∀ t, J t =ᵐ[P] itoIntegral P F B (fun s ω ↦ σ (X s ω)) t)
    (hLe : ∀ t, L t =ᵐ[P] itoIntegral P F B (fun s ω ↦ σ (Y s ω)) t)
    (hXe : integrandDist P X (fun _ _ ↦ 0) 2 ≠ ∞)
    (hYe : integrandDist P Y (fun _ _ ↦ 0) 2 ≠ ∞) :
    (∫⁻ ω, (⨆ s : Icc (0 : ℝ≥0) 2,
      ‖(5 + J s ω + ∫ u in (0 : ℝ)..s, b (X u.toNNReal ω)) -
        (5 + L s ω + ∫ u in (0 : ℝ)..s, b (Y u.toNNReal ω))‖ₑ)^2 ∂P) ≤
      12 * integrandDist P X Y 2 := by
  have h := lintegral_iSup_picard_sub_le hB hBF hInd hσ hb hXp hYp hXc hYc
    hJm hLm hJc hLc hJe hLe 5 2 hXe hYe
  norm_num at h
  exact h
end
