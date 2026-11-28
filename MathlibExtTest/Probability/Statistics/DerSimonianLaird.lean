/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Statistics.DerSimonianLaird

namespace MathlibExtTest.Probability.Statistics.DerSimonianLaird

open WantedExt.Probability.Statistics.DerSimonianLairdWanted

/-- With unit sampling and between-study variances, estimates `0` and `2` give estimator,
pooled mean, and pooled variance all equal to `1`. -/
example : dlEstimator (fun _ : Fin 2 => 1) ![0, 2] = 1 ∧
    pooledEstimate (fun _ : Fin 2 => 1) 1 ![0, 2] = 1 ∧
    (∑ _i : Fin 2, ((1 : ℝ) + 1)⁻¹)⁻¹ = 1 := by
  have h := equal_variances le_rfl 1 one_pos ![0, 2] 1 zero_le_one
  rw [h.1, h.2.1, h.2.2]
  norm_num [Fin.sum_univ_two, max_def]

/-- With identical observations, the negative untruncated estimate is cut off at zero. -/
example : dlEstimator (fun _ : Fin 2 => 1) (fun _ => 3) = 0 := by
  have h := (equal_variances le_rfl 1 one_pos (fun _ : Fin 2 => 3) 0 le_rfl).1
  norm_num [Fin.sum_univ_two, max_def] at h
  exact h

open MeasureTheory ProbabilityTheory in
/-- Total variances `2` and `4` give optimal variance `4/3`, less than the uniform-weight
variance formula `3/2`. The theorem applies to uniform weights as a competitor. -/
example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (δ e : Fin 2 → Ω → ℝ) (m : ℝ) (hmodel : RandomEffectsModel μ δ e ![1, 3] 1) :
    (∫ ω, pooledEstimate ![1, 3] 1 (fun i => m + δ i ω + e i ω) ∂μ) = m ∧
      Var[fun ω => pooledEstimate ![1, 3] 1 (fun i => m + δ i ω + e i ω); μ] = 4 / 3 ∧
      (4 / 3 : ℝ) ≤ Var[fun ω => ∑ i : Fin 2, (1 / 2) * (m + δ i ω + e i ω); μ] ∧
      (4 / 3 : ℝ) < 3 / 2 ∧
      (∑ i : Fin 2, (1 / 2 : ℝ) ^ 2 * ((![1, 3] : Fin 2 → ℝ) i + 1)) = 3 / 2 := by
  have hv (i : Fin 2) : 0 < (![1, 3] : Fin 2 → ℝ) i := by fin_cases i <;> norm_num
  have h := pooledEstimate_optimal (μ := μ) (hk := le_rfl) (v := ![1, 3]) (hv := hv)
    (Δsq := 1) (m := m) (hΔ := zero_le_one) (δ := δ) (e := e) (hmodel := hmodel)
    (c := fun _ => 1 / 2) (hc := by norm_num [Fin.sum_univ_two])
  have hopt : (∑ i : Fin 2, (((![1, 3] : Fin 2 → ℝ) i) + 1)⁻¹)⁻¹ = 4 / 3 := by
    norm_num [Fin.sum_univ_two]
  rw [hopt] at h
  exact ⟨h.1, h.2.1, h.2.2, by norm_num, by norm_num [Fin.sum_univ_two]⟩

end MathlibExtTest.Probability.Statistics.DerSimonianLaird
