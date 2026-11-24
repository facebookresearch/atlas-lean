/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Probability.SDE.LipschitzIntegrands
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

example {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X Y : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) :
    integrandDist P (fun s ω ↦ 3 * X s ω + 2) (fun s ω ↦ 3 * Y s ω + 2) t ≤
      9 * integrandDist P X Y t := by
  have hf : LipschitzWith 3 (fun x : ℝ ↦ 3 * x + 2) := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    simp only [Real.dist_eq, NNReal.coe_ofNat]
    rw [show 3*x+2-(3*y+2) = 3*(x-y) by ring, abs_mul]
    norm_num
  convert integrandDist_comp_lipschitz_le hf P X Y t using 1
  norm_num

example {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} (hX : IsProgressive F X)
    {f : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) (t : ℝ≥0)
    (hX2 : integrandDist P X (fun _ _ ↦ 0) t ≠ ∞) :
    IsItoApproximable P F (fun s ω ↦ f (X s ω)) t :=
  isItoApproximable_comp_lipschitz hX hf t hX2

-- A constant map annihilates distance even for inputs of infinite energy.
example {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X Y : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) :
    integrandDist P (fun s ω ↦ (fun _ : ℝ ↦ 7) (X s ω))
      (fun s ω ↦ (fun _ : ℝ ↦ 7) (Y s ω)) t = 0 := by
  exact le_antisymm (by simpa using
    integrandDist_comp_lipschitz_le (LipschitzWith.const (7 : ℝ)) P X Y t) bot_le

-- The bound is attained at nonunit slope and horizon, even with a nonzero offset.
example {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] :
    integrandDist P (fun _ _ ↦ (3 : ℝ) * 1 + 2) (fun _ _ ↦ (3 : ℝ) * 0 + 2) 2 = 18 := by
  norm_num [integrandDist, lintegral_const, Real.eNorm_eq_ofReal_abs, Real.volume_Ioc]

example {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    (F : Filtration ℝ≥0 mΩ) (t : ℝ≥0) :
    IsItoApproximable P F (fun _ _ ↦ (2 : ℝ)) t := by
  have hf : LipschitzWith 0 (fun _ : ℝ ↦ (2 : ℝ)) := LipschitzWith.const _
  exact isItoApproximable_comp_lipschitz (isProgressive_const F (0 : ℝ)) hf t
    (by simp [integrandDist])

example {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) P)
    {X Y : ℝ≥0 → Ω → ℝ} (hX : IsProgressive F X) (hY : IsProgressive F Y)
    {K : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzWith K f) (t : ℝ≥0)
    (hX2 : integrandDist P X (fun _ _ ↦ 0) t ≠ ∞)
    (hY2 : integrandDist P Y (fun _ _ ↦ 0) t ≠ ∞) :
    ∫⁻ ω, ‖itoIntegral P F B (fun s ω ↦ f (X s ω)) t ω -
      itoIntegral P F B (fun s ω ↦ f (Y s ω)) t ω‖ₑ^2 ∂P ≤
        (K : ℝ≥0∞)^2 * integrandDist P X Y t :=
  lintegral_itoIntegral_sub_comp_lipschitz_le hB hBF hInd hX hY hf t hX2 hY2

-- Nondifferentiability of a coefficient is irrelevant to these estimates.
example {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} (hX : IsProgressive F X)
    (t : ℝ≥0) (hX2 : integrandDist P X (fun _ _ ↦ 0) t ≠ ∞) :
    IsItoApproximable P F (fun s ω ↦ |X s ω|) t := by
  have hf : LipschitzWith 1 (abs : ℝ → ℝ) := by
    simpa only [Real.norm_eq_abs] using!
      (lipschitzWith_one_norm : LipschitzWith 1 (norm : ℝ → ℝ))
  exact isItoApproximable_comp_lipschitz hX hf t hX2

-- The zero horizon needs no finite-energy assumption on the input process.
example {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} (hX : IsProgressive F X)
    {f : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    IsItoApproximable P F (fun s ω ↦ f (X s ω)) 0 :=
  isItoApproximable_comp_lipschitz hX hf 0 (by simp [integrandDist])
