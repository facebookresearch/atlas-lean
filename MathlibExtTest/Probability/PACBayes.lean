/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.PACBayes

/-! Non-vacuity tests for Catoni's PAC-Bayes bound. -/

@[expose] public section

open MeasureTheory InformationTheory
open scoped ENNReal
open MathlibExt.Probability.PACBayes

namespace MathlibExtTest.Probability.PACBayes

/-- Catoni's bound for the `{0, 1}`-valued loss `θ ≠ z` on `Θ = 𝒵 = Bool`, for any prior and
data distribution, sample size `10`, `λ = 1` and `δ = 1/10`. -/
example (π D : Measure Bool) [IsProbabilityMeasure π] [IsProbabilityMeasure D] :
    (Measure.pi fun _ : Fin 10 => D)
      {S | ¬ ∀ ρ : Measure Bool, IsProbabilityMeasure ρ → klDiv ρ π ≠ ⊤ →
        ∫ θ, (∫ z, (if θ = z then (0 : ℝ) else 1) ∂D) ∂ρ ≤
          ∫ θ, (((10 : ℕ) : ℝ)⁻¹ * ∑ i, (if θ = S i then (0 : ℝ) else 1)) ∂ρ
          + 1 * 1 ^ 2 / (8 * ((10 : ℕ) : ℝ)) + ((klDiv ρ π).toReal + Real.log (1 / (1 / 10))) / 1}
      ≤ ENNReal.ofReal (1 / 10) :=
  catoni_pacBayes (ℓ := fun θ z => if θ = z then (0 : ℝ) else 1) π D
    (measurable_of_countable _) (fun θ z => by split_ifs <;> norm_num)
    (by norm_num) one_pos (by norm_num)

/-- Hoeffding's lemma for an indicator-type function. -/
example (D : Measure Bool) [IsProbabilityMeasure D] (t : ℝ) :
    ∫ z, Real.exp (t * (∫ z', (if z' then (1 : ℝ) else 0) ∂D - (if z then 1 else 0))) ∂D ≤
      Real.exp (1 ^ 2 * t ^ 2 / 8) :=
  integral_exp_mul_sub_le D (measurable_of_countable _) (fun z => by split_ifs <;> norm_num) t

end MathlibExtTest.Probability.PACBayes
