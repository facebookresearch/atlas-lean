/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.ContinuousDoob

/-!
# Tests for Doob's `L²` inequality in continuous time

Non-vacuity on a constant martingale, where the inequality reads `c² ≤ 4 c²`, and the boundary
horizon `t = 0`.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace MathlibExtTest.Probability.ContinuousDoob

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A constant process is a martingale with continuous paths, and the inequality applies. -/
example (ℱ : Filtration ℝ≥0 m0) (c : ℝ) (t : ℝ≥0) :
    ∫⁻ ω, (⨆ s : Set.Icc (0 : ℝ≥0) t, ENNReal.ofReal |(fun (_ : ℝ≥0) (_ : Ω) ↦ c) s ω|) ^ 2 ∂μ ≤
      4 * ∫⁻ ω, ENNReal.ofReal ((fun (_ : ℝ≥0) (_ : Ω) ↦ c) t ω ^ 2) ∂μ :=
  (martingale_const ℱ μ c).lintegral_iSup_sq_le_of_continuous (fun _ ↦ continuous_const)
    (fun _ ↦ memLp_const c) t

/-- At the horizon `t = 0` the supremum runs over the single time `0`. -/
example {ℱ : Filtration ℝ≥0 m0} {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M ℱ μ)
    (hcont : ∀ ω, Continuous fun t ↦ M t ω) (hL2 : ∀ t, MemLp (M t) 2 μ) :
    ∫⁻ ω, (⨆ s : Set.Icc (0 : ℝ≥0) 0, ENNReal.ofReal |M s ω|) ^ 2 ∂μ ≤
      4 * ∫⁻ ω, ENNReal.ofReal (M 0 ω ^ 2) ∂μ :=
  hM.lintegral_iSup_sq_le_of_continuous hcont hL2 0

end MathlibExtTest.Probability.ContinuousDoob
