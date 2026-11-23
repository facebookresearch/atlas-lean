/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.ItoRiemannSums

/-!
# Tests for Itô–Riemann sums of deterministic integrands

The empty partition (`n = 0`), the constant integrand `g = 1` (the Itô–Riemann sums telescope to
`B t - B 0`, matching the limit `g t B t - g 0 B 0 - ∫ g' B = B t - B 0`), the Riemann–Stieltjes
limit at `t = 0`, and the noiseless Ornstein–Uhlenbeck case `σ = 0`.
-/

open MeasureTheory Filter Topology ProbabilityTheory ProbabilityTheory.ElementaryIntegrand Real
open scoped NNReal

namespace MathlibExtTest.Probability.ItoRiemannSums

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

/-- With no cells the Itô–Riemann sum is `0`. -/
example (g : ℝ → ℝ) (t : ℝ≥0) (B : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    (riemann F g t 0).itoIntegral B t ω = 0 := by
  simp [itoIntegral, riemann]

/-- For `g = 1` the Itô–Riemann sums telescope to `B t - B 0` as soon as `n ≥ 1`. -/
example (t : ℝ≥0) (n : ℕ) (hn : 0 < n) (B : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    (riemann F (fun _ ↦ 1) t n).itoIntegral B t ω = B t ω - B 0 ω := by
  rw [itoIntegral_riemann]
  simp only [one_mul]
  have h := Finset.sum_range_sub (fun k : ℕ ↦ B (Real.toNNReal (t * k / n)) ω) n
  push_cast at h
  rw [h, mul_div_assoc, div_self (by exact_mod_cast hn.ne'), mul_one, Real.toNNReal_coe]
  simp

/-- The limit for `g = 1` is `B t - B 0`: the derivative term vanishes. -/
example {B : ℝ≥0 → Ω → ℝ} {ω : Ω} (hω : Continuous (B · ω)) (t : ℝ≥0) :
    Tendsto (fun n ↦ (riemann F (fun _ ↦ (1 : ℝ)) t n).itoIntegral B t ω) atTop
      (𝓝 (B t ω - B 0 ω)) := by
  simpa using tendsto_itoIntegral_riemann F (contDiff_const (c := (1 : ℝ))) hω t

/-- For `g u = u` the limit is `t w t - ∫_0^t w`. -/
example {w : ℝ → ℝ} (hw : Continuous w) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun n : ℕ ↦ ∑ k ∈ Finset.range n,
        t * k / n * (w (t * (k + 1) / n) - w (t * k / n))) atTop
      (𝓝 (t * w t - ∫ u in (0 : ℝ)..t, w u)) := by
  simpa using tendsto_sum_mul_sub_uniform (g := fun u ↦ u) contDiff_id hw ht

/-- With `θ = 0` the Ornstein–Uhlenbeck solution is `X₀ + σ (B t - B 0)`, and the Itô–Riemann
form converges to it. -/
example {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (σ : ℝ) (X₀ : Ω → ℝ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, Tendsto (fun n ↦ X₀ ω + σ *
        (riemann F (fun _ ↦ (1 : ℝ)) t n).itoIntegral B t ω)
      atTop (𝓝 (X₀ ω + σ * (B t ω - B 0 ω))) := by
  filter_upwards [hB.ae_tendsto_ou_itoIntegral_riemann F 0 σ X₀] with ω hω t
  simpa [ouPathSolution, Real.toNNReal_coe] using hω t

end MathlibExtTest.Probability.ItoRiemannSums
