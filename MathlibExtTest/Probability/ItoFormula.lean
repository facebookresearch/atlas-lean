/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.ItoFormula

/-!
# Tests for Itô's formula

Boundary values of `leftPointProcess`, the Riemann sums of a constant, and Itô's formula
instantiated for `f = id` (where it reduces to `∫_0^t 1 dB = B t - B 0`) and for `f = sin`
(`sin (B t) = sin (B 0) + ∫_0^t cos (B u) dB u - (1/2) ∫_0^t sin (B u) du`).
-/

open MeasureTheory ProbabilityTheory Filter Topology Real
open scoped NNReal ENNReal

namespace MathlibExtTest.Probability.ItoFormula

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ} {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}

/-- With no cells the left-point step process is `0`. -/
example (g : ℝ → ℝ) (t u : ℝ≥0) (ω : Ω) : leftPointProcess g B t 0 u ω = 0 := by
  simp [leftPointProcess]

/-- Riemann sums of a constant `c` on `[0, t]` tend to `t c`. -/
example (c t : ℝ) (ht : 0 ≤ t) :
    Tendsto (fun n : ℕ ↦ ∑ _k ∈ Finset.range n, c * (t / n)) atTop (𝓝 (t * c)) := by
  simpa using tendsto_sum_riemann_uniform (g := fun _ ↦ c) continuous_const ht

/-- Itô's formula for `f = id`: `B t = B 0 + ∫_0^t 1 dB` almost surely. -/
example (hB : IsBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance)
      (F s) P) (hBm : Measurable fun p : ℝ≥0 × Ω ↦ B p.1 p.2) (t : ℝ≥0) :
    (fun ω ↦ B t ω) =ᵐ[P] fun ω ↦ B 0 ω + itoIntegral P F B (fun _ _ ↦ 1) t ω := by
  have h := ito_formula hB hBF hInd hBm (f := fun x ↦ x) contDiff_id 1 (by simp) (by simp) t
  simpa using h

/-- Itô's formula for `f = sin`. -/
example (hB : IsBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance)
      (F s) P) (hBm : Measurable fun p : ℝ≥0 × Ω ↦ B p.1 p.2) (t : ℝ≥0) :
    (fun ω ↦ sin (B t ω)) =ᵐ[P] fun ω ↦ sin (B 0 ω) +
      itoIntegral P F B (fun u ω' ↦ cos (B u ω')) t ω +
        (1 / 2) * ∫ u in (0 : ℝ)..t, -sin (B (Real.toNNReal u) ω) := by
  have h := ito_formula hB hBF hInd hBm (f := sin) contDiff_sin 1
    (fun x ↦ by simpa using abs_cos_le_one x) (fun x ↦ by simpa using abs_sin_le_one x) t
  simpa using h

end MathlibExtTest.Probability.ItoFormula
