/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Distribution.PlemeljLimitTemperedDistribution

open Filter MeasureTheory
open scoped Topology

namespace MathlibExt.Analysis.Distribution.PlemeljLimitTemperedDistributionWanted

-- Each kernel at ε = 1 cancels the matching linear factor on a Schwartz test function.
example (φ : SchwartzMap ℝ ℂ) :
    uPlusEps 1 (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ) + Complex.I) φ) = (∫ x, φ x) ∧
    uMinusEps 1 (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ) - Complex.I) φ) = ∫ x, φ x := by
  constructor
  · apply integral_congr_ae
    apply ae_of_all
    intro x
    have hx : (x : ℂ) + Complex.I ≠ 0 := fun h => by simpa using congrArg Complex.im h
    have hg : (fun x : ℝ => (x : ℂ) + Complex.I).HasTemperateGrowth := by fun_prop
    simp [SchwartzMap.smulLeftCLM_apply_apply hg, hx]
  · apply integral_congr_ae
    apply ae_of_all
    intro x
    have hx : (x : ℂ) - Complex.I ≠ 0 := fun h => by simpa using congrArg Complex.im h
    have hg : (fun x : ℝ => (x : ℂ) - Complex.I).HasTemperateGrowth := by fun_prop
    simp [SchwartzMap.smulLeftCLM_apply_apply hg, hx]

-- Reflection exchanges the two kernels with a minus sign, also in the boundary limit.
example (φ : SchwartzMap ℝ ℂ) (hφ : Function.Even (φ : ℝ → ℂ)) :
    ∃ z : ℂ, Tendsto (fun ε => uPlusEps ε φ) (𝓝[>] 0) (𝓝 z) ∧
      Tendsto (fun ε => uMinusEps ε φ) (𝓝[>] 0) (𝓝 (-z)) := by
  obtain ⟨u, _, hu, _⟩ := exists_temperedDistribution_tendsto_inv_add_mul_I.2
  refine ⟨u φ, hu φ, (hu φ).neg.congr fun ε => ?_⟩
  rw [uPlusEps, uMinusEps, ← integral_neg, ← integral_neg_eq_self
    (fun x : ℝ => ((x : ℂ) - ε * Complex.I)⁻¹ * φ x)]
  have heven (x : ℝ) : φ (-x) = φ x := hφ x
  simp only [Complex.ofReal_neg, heven, ← neg_add', inv_neg, neg_mul]

end MathlibExt.Analysis.Distribution.PlemeljLimitTemperedDistributionWanted
