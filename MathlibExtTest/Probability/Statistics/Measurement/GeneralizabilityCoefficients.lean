/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Measurement.GeneralizabilityCoefficients

/-!
# Tests for the generalizability and dependability coefficients

With components (4, 2, 6) and three items, dependability is 3/5,
generalizability is 2/3, and the order chain and variance-ratio
readings are exercised through the production theorems.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace MathlibExtTest.Probability.Statistics.Measurement

open MathlibExt.Probability.Statistics.Measurement

private theorem test_dependability_value :
    dependabilityCoefficient 4 2 6 3 = 3 / 5 := by
  simp only [dependabilityCoefficient,
    MathlibExt.Probability.Statistics.LinearModel.ErrorsInVariables.attenuationFactor]
  norm_num

private theorem test_generalizability_value :
    generalizabilityCoefficient 4 6 3 = 2 / 3 := by
  simp only [generalizabilityCoefficient,
    MathlibExt.Probability.Statistics.LinearModel.ErrorsInVariables.attenuationFactor]
  norm_num

private theorem test_hypotheses_hold :
    (0 : ℝ) < 4 + 6 / ((3 : ℕ) : ℝ) ∧ (0 : ℝ) < 4 + (2 + 6) / ((3 : ℕ) : ℝ) := by
  constructor <;> norm_num

private theorem test_order_chain_fixture :
    0 ≤ dependabilityCoefficient 4 2 6 3
      ∧ dependabilityCoefficient 4 2 6 3 ≤ generalizabilityCoefficient 4 6 3
      ∧ generalizabilityCoefficient 4 6 3 ≤ 1 :=
  dependability_le_generalizability (sigmaP2 := 4) (sigmaI2 := 2) (sigmae2 := 6) (m := 3)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    test_hypotheses_hold.1 test_hypotheses_hold.2

private theorem test_order_chain_values :
    (0 : ℝ) ≤ 3 / 5 ∧ (3 / 5 : ℝ) ≤ 2 / 3 ∧ (2 / 3 : ℝ) ≤ 1 := by
  have h := test_order_chain_fixture
  rwa [test_dependability_value, test_generalizability_value] at h

private theorem test_strict_value :
    dependabilityCoefficient 4 2 6 3 < generalizabilityCoefficient 4 6 3 :=
  dependability_lt_generalizability (sigmaP2 := 4) (sigmaI2 := 2) (sigmae2 := 6) (m := 3)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem test_strict_values : (3 / 5 : ℝ) < 2 / 3 := by
  have h := test_strict_value
  rwa [test_dependability_value, test_generalizability_value] at h

private theorem test_zero_item_equality :
    dependabilityCoefficient 4 0 6 3 = generalizabilityCoefficient 4 6 3
      ∧ dependabilityCoefficient 4 0 6 3 = 2 / 3 := by
  have h := dependability_eq_generalizability_of_itemVariance_eq_zero 4 6 3
  exact ⟨h, h.trans test_generalizability_value⟩

private theorem test_zero_item_order_chain :
    0 ≤ dependabilityCoefficient 4 0 6 3
      ∧ dependabilityCoefficient 4 0 6 3 ≤ generalizabilityCoefficient 4 6 3
      ∧ generalizabilityCoefficient 4 6 3 ≤ 1
      ∧ dependabilityCoefficient 4 0 6 3 = generalizabilityCoefficient 4 6 3 := by
  have h := dependability_le_generalizability (sigmaP2 := 4) (sigmaI2 := 0) (sigmae2 := 6)
    (m := 3) (by norm_num) le_rfl (by norm_num) (by norm_num)
    test_hypotheses_hold.1 (by norm_num)
  exact ⟨h.1, h.2.1, h.2.2, test_zero_item_equality.1⟩

private theorem test_variance_ratio_values
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (grandMean : ℝ)
    (X : Fin 1 → Fin 3 → Ω → ℝ) (P : Fin 1 → Ω → ℝ)
    (I : Fin 3 → Ω → ℝ) (e : Fin 1 → Fin 3 → Ω → ℝ)
    (hX : ∀ i, X 0 i = fun ω => grandMean + P 0 ω + I i ω + e 0 i ω)
    (hI_mem : ∀ i, MemLp (I i) 2 μ)
    (he_mem : ∀ i, MemLp (e 0 i) 2 μ)
    (hI_cov : ∀ i j, cov[I i, I j; μ] = if i = j then (2 : ℝ) else 0)
    (he_cov : ∀ i j, cov[e 0 i, e 0 j; μ] = if i = j then (6 : ℝ) else 0)
    (hIe_cov : ∀ i j, cov[I i, e 0 j; μ] = 0)
    (hP_var : Var[P 0; μ] = 4) :
    Var[P 0; μ] / (Var[P 0; μ] + Var[Delta_p grandMean X P 0; μ]) = 3 / 5
      ∧ Var[P 0; μ] / (Var[P 0; μ] + Var[delta_p grandMean X P I 0; μ]) = 2 / 3
      ∧ Var[P 0; μ] / (Var[P 0; μ] + Var[Delta_p grandMean X P 0; μ])
        < Var[P 0; μ] / (Var[P 0; μ] + Var[delta_p grandMean X P I 0; μ]) := by
  have h := dependability_generalizability_eq_variance_ratio grandMean X P I e 4 2 6 0
    hX hI_mem he_mem hI_cov he_cov hIe_cov hP_var
  simp only [Fintype.card_fin] at h
  rw [← h.1, ← h.2]
  exact ⟨test_dependability_value, test_generalizability_value, test_strict_value⟩

private theorem test_zero_variance_totalized :
    dependabilityCoefficient 0 0 0 1 = 0
      ∧ generalizabilityCoefficient 0 0 1 = 0 := by
  simp only [dependabilityCoefficient, generalizabilityCoefficient,
    MathlibExt.Probability.Statistics.LinearModel.ErrorsInVariables.attenuationFactor]
  norm_num

end MathlibExtTest.Probability.Statistics.Measurement
