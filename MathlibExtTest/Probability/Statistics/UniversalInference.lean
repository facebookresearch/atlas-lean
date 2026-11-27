/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.UniversalInference
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Tactic.NormNum

@[expose] public section

open MeasureTheory MathlibExt.Probability.Statistics.UniversalInference
open scoped ENNReal

namespace MathlibExtTest.Probability.Statistics.UniversalInference

/-! ### A non-degenerate model: a point-mass family on `Bool` -/

/-- The model `P_θ = δ_θ` on `Bool`, as densities with respect to counting measure. -/
noncomputable def pt (θ y : Bool) : ℝ≥0∞ := if y = θ then 1 else 0

theorem measurable_pt : Measurable (Function.uncurry pt) := measurable_of_countable _

theorem lintegral_pt (θ : Bool) : ∫⁻ y, pt θ y ∂Measure.count = 1 := by
  rw [lintegral_count, tsum_fintype]
  cases θ <;> simp [pt]

/-- The fixed-alternative Markov bound, at `α = 1/2`, for `q₀ = pt false` and `q₁ = pt true`:
the ratio `q₁ / q₀` is infinite exactly where `q₀` vanishes, an event of probability zero. -/
example : (Measure.count.withDensity (pt false)) {y | (1 / 2 : ℝ≥0∞)⁻¹ * pt false y < pt true y}
    ≤ 1 / 2 :=
  withDensity_inv_mul_lt_le _ (measurable_of_countable _) (measurable_of_countable _)
    (lintegral_pt true).le (by norm_num) (by norm_num)

/-- Theorem 1 for an i.i.d. sample of size `3`, a trivial first half (`𝒲 = Unit`) and the
estimate `θ̂₁ = true`, at the true parameter `false`. -/
example :
    ((Measure.dirac ()).prod (Measure.pi fun _ : Fin 3 => Measure.count.withDensity (pt false)))
        {w | false ∉ universalConfidenceSet (fun θ (y : Fin 3 → Bool) => ∏ i, pt θ (y i))
          (1 / 2) ((fun _ : Unit => true) w.1) w.2} ≤ 1 / 2 :=
  measure_not_mem_universalConfidenceSet_le_pi _ _ measurable_pt (fun θ => (lintegral_pt θ).le)
    measurable_const false (by norm_num) (by norm_num)

/-- The constant null estimate `θ̂₀ = false`, the maximiser over the singleton `{false}`. -/
def est0 (_ : Fin 3 → Bool) : Bool := false

/-- The constant first-half estimate `θ̂₁ = true`. -/
def est1 (_ : Unit) : Bool := true

/-- Theorem 3 for `H₀ : θ* ∈ {false}`, with `θ̂₀ = false` (the maximiser over a singleton) and
`θ̂₁ = true`: the type I error at `α = 1/2` is at most `1/2`. -/
example :
    ((Measure.dirac ()).prod (Measure.pi fun _ : Fin 3 => Measure.count.withDensity (pt false)))
        {w | (1 / 2 : ℝ≥0∞)⁻¹ * ∏ i, pt (est0 w.2) (w.2 i) < ∏ i, pt (est1 w.1) (w.2 i)} ≤
      1 / 2 :=
  measure_splitLRT_reject_le_pi (Θ₀ := {false}) (θhat₀ := est0) (θstar := false)
    Measure.count (Measure.dirac ()) measurable_pt (fun θ => (lintegral_pt θ).le)
    (measurable_const (a := true)) (fun y θ hθ => by rw [Set.mem_singleton_iff.1 hθ]; rfl)
    rfl (by norm_num) (by norm_num)

end MathlibExtTest.Probability.Statistics.UniversalInference
