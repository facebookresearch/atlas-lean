/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Statistics.BootstrapStandardDeviation
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Tests for the consistency of the bootstrap standard deviation
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal
open MathlibExt.Probability.Statistics.BootstrapWanted

namespace MathlibExtTest.Probability.Statistics.BootstrapStandardDeviation

/-- For i.i.d. standard normal data (the coordinates of a sequence drawn from the product of
standard normal laws), the bootstrap standard deviation converges to `1` in conditional
probability, almost surely. -/
private theorem gaussian_bootstrap_sd :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1), ∀ ε > 0, Tendsto (fun nm : ℕ × ℕ =>
        (((nm.1 + 1 : ℕ) : ℝ) ^ nm.2)⁻¹ *
          ((Finset.univ.filter fun I : Fin nm.2 → Fin (nm.1 + 1) =>
            ε < |Real.sqrt ((nm.2 : ℝ)⁻¹ * ∑ j, (ω (I j) -
              (nm.2 : ℝ)⁻¹ * ∑ l, ω (I l)) ^ 2) - 1|).card : ℝ))
      (atTop ×ˢ atTop) (𝓝 0) := by
  have hcoord (i : ℕ) := measurePreserving_eval_infinitePi (fun _ : ℕ => gaussianReal 0 1) i
  have hL2 : MemLp (fun ω : ℕ → ℝ => ω 0) 2
      (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) := by
    have h := memLp_id_gaussianReal' (μ := 0) (v := 1) 2 (by simp)
    rw [← (hcoord 0).map_eq] at h
    exact h.comp_of_map (measurable_pi_apply 0).aemeasurable
  have hvar : variance (fun ω : ℕ → ℝ => ω 0)
      (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) = ((1 : ℝ≥0) : ℝ) := by
    rw [← variance_id_map (measurable_pi_apply 0).aemeasurable, (hcoord 0).map_eq,
      variance_id_gaussianReal]
  have H := bootstrap_sd_tendsto (P := Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)
    (X := fun i (ω : ℕ → ℝ) => ω i) measurable_pi_apply
    (iIndepFun_infinitePi (P := fun _ : ℕ => gaussianReal 0 1) (X := fun _ => id)
      fun _ => measurable_id)
    (fun i => (hcoord i).hasLaw.identDistrib (hcoord 0).hasLaw) hL2 hvar zero_lt_one
  simpa only [NNReal.coe_one, Real.sqrt_one] using H

/-- Along the classical bootstrap, which draws `n + 1` values from `n + 1` observations, the
conditional probability that the bootstrap standard deviation of standard normal data is more than
`ε` away from `1` tends to `0`, almost surely. -/
example : ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1), ∀ ε > 0,
    Tendsto (fun n : ℕ =>
        (((n + 1 : ℕ) : ℝ) ^ (n + 1))⁻¹ *
          ((Finset.univ.filter fun I : Fin (n + 1) → Fin (n + 1) =>
            ε < |Real.sqrt (((n + 1 : ℕ) : ℝ)⁻¹ * ∑ j, (ω (I j) -
              ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ l, ω (I l)) ^ 2) - 1|).card : ℝ))
      atTop (𝓝 0) := by
  filter_upwards [gaussian_bootstrap_sd] with ω hω ε hε
  exact (hω ε hε).comp (tendsto_id.prodMk (tendsto_add_atTop_nat 1))

end MathlibExtTest.Probability.Statistics.BootstrapStandardDeviation
