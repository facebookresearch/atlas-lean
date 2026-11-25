/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Process.ContinuousDoobLp

/-! # Tests for Doob's continuous-time maximal inequality -/

open MeasureTheory
open MathlibExt.Probability.ContinuousDoobWanted.Submartingale
open scoped NNReal ENNReal

namespace MathlibExtTest.Probability.Process.ContinuousDoobLp

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

-- A strictly increasing deterministic submartingale and a fractional exponent.
example (ℱ : Filtration ℝ≥0 m) (t : ℝ≥0) :
    (⨆ s : Set.Icc (0 : ℝ≥0) t, ENNReal.ofReal (s : ℝ≥0)) ^ (3 / 2 : ℝ) ≤
      ENNReal.ofReal ((3 : ℝ) ^ (3 / 2 : ℝ)) * ENNReal.ofReal t ^ (3 / 2 : ℝ) := by
  have hX : Submartingale (fun (s : ℝ≥0) (_ : Ω) ↦ (s : ℝ)) ℱ μ := by
    refine ⟨fun _ ↦ stronglyMeasurable_const, fun i j hij ↦ ?_, fun _ ↦ integrable_const _⟩
    rw [condExp_const (ℱ.le i)]
    exact Filter.Eventually.of_forall fun _ ↦ NNReal.coe_le_coe.mpr hij
  have h := lintegral_iSup_rpow_le hX (fun s _ ↦ s.coe_nonneg) (fun _ ↦ NNReal.continuous_coe)
    (p := 3 / 2) (by norm_num) t
  norm_num [lintegral_const] at h ⊢
  exact h

-- On the singleton interval the running maximum reduces to the initial value.
example {ℱ : Filtration ℝ≥0 m} {X : ℝ≥0 → Ω → ℝ} (hX : Submartingale X ℱ μ)
    (h0 : ∀ t ω, 0 ≤ X t ω) (hc : ∀ ω, Continuous fun t ↦ X t ω) {p : ℝ} (hp : 1 < p) :
    ∫⁻ ω, ENNReal.ofReal (X 0 ω) ^ p ∂μ ≤
      ENNReal.ofReal ((p / (p - 1)) ^ p) * ∫⁻ ω, ENNReal.ofReal (X 0 ω) ^ p ∂μ := by
  have hsingle (ω : Ω) :
      (⨆ s : Set.Icc (0 : ℝ≥0) 0, ENNReal.ofReal (X s ω)) = ENNReal.ofReal (X 0 ω) := by
    refine le_antisymm (iSup_le fun s ↦ ?_) (le_iSup_of_le ⟨0, le_rfl, le_rfl⟩ le_rfl)
    rw [le_antisymm s.property.2 s.property.1]
  simpa only [hsingle] using lintegral_iSup_rpow_le hX h0 hc hp 0

end MathlibExtTest.Probability.Process.ContinuousDoobLp
