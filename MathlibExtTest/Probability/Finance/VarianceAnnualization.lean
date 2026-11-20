/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Finance.VarianceAnnualization

/-! # Tests for `MathlibExt.Probability.Finance.VarianceAnnualization` -/

namespace MathlibExtTest.VarianceAnnualization

/-- `Fin 2` zero-returns instance: every period return is `0`, so `σ2 = 0`. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsFiniteMeasure μ] :
    ProbabilityTheory.variance
        (fun ω => ∑ i : Fin 2, (fun _ : Fin 2 => (0 : Ω → ℝ)) i ω) μ
      = (Fintype.card (Fin 2) : ℝ) * (0 : ℝ) :=
  MathlibExt.Probability.Finance.VarianceAnnualization.variance_sum_eq_card_mul_of_uncorrelated
    (R := fun _ => 0) (σ2 := 0)
    (fun i => by simp [MeasureTheory.MemLp.zero])
    (fun i => by simp [ProbabilityTheory.variance_zero])
    (fun i j _ => by simp)

/-- `Fin 1` instance: one period gives `variance = 1 * σ2`. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsFiniteMeasure μ] {R : Fin 1 → Ω → ℝ}
    (hR : ∀ i, MeasureTheory.MemLp (R i) 2 μ) {σ2 : ℝ}
    (hvar : ∀ i, ProbabilityTheory.variance (R i) μ = σ2)
    (huncorr : ∀ i j, i ≠ j → ProbabilityTheory.covariance (R i) (R j) μ = 0) :
    ProbabilityTheory.variance (fun ω => ∑ i, R i ω) μ = 1 * σ2 := by
  have h :=
    MathlibExt.Probability.Finance.VarianceAnnualization.variance_sum_eq_card_mul_of_uncorrelated
      hR hvar huncorr
  simpa using h

end MathlibExtTest.VarianceAnnualization
