/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.MetaAnalysis

@[expose] public section

open MeasureTheory ProbabilityTheory
open MathlibExt.Probability.Statistics.MetaAnalysis

namespace MathlibExtTest.Probability.Statistics.MetaAnalysis

/-- Fisher's statistic of p-values all equal to `1` is `0`. -/
example : fisherStatistic (fun _ : Fin 4 => (1 : ℝ)) = 0 := by simp [fisherStatistic]

/-- Fisher's statistic of `k` p-values equal to `e⁻¹` is `2k`. -/
example (k : ℕ) : fisherStatistic (fun _ : Fin k => Real.exp (-1)) = 2 * k := by
  simp [fisherStatistic]

/-- Junk value: a p-value `0` contributes `log 0 = 0` (a null event under a uniform law). -/
example : fisherStatistic ![(0 : ℝ), 1] = 0 := by simp [fisherStatistic]

/-- Non-vacuity of Fisher's theorem: one uniform p-value gives `-2 log U ~ χ²₂`. -/
example : HasLaw (fun u : ℝ => fisherStatistic fun _ : Fin 1 => u) (chiSquareMeasure 2)
    (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  have : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := ⟨by simp⟩
  simpa using hasLaw_fisherStatistic (k := 1) one_pos (p := fun _ => id) (fun _ => HasLaw.id)
    iIndepFun.of_subsingleton

/-- `-2 log U` is exponential with rate `1/2` for `U` uniform on `[0, 1]`. -/
example : HasLaw (fun u : ℝ => -2 * Real.log u) (gammaMeasure 1 (1 / 2))
    (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
  hasLaw_neg_two_mul_log_uniform

/-- Stouffer's statistic with equal weights of two z-scores equal to `1` is `√2`. -/
example : stoufferStatistic ![1, 1] ![(1 : ℝ), 1] = √2 := by
  rw [stoufferStatistic]
  norm_num [Fin.sum_univ_two]

/-- Junk value: with the zero weight vector Stouffer's statistic is `0 / 0 = 0`
(`hasLaw_stoufferStatistic` assumes `w ≠ 0`). -/
example (z : Fin 3 → ℝ) : stoufferStatistic 0 z = 0 := by simp [stoufferStatistic]

/-- Non-vacuity of Stouffer's theorem: a single standard normal z-score with weight `2`. -/
example : HasLaw (fun x : ℝ => stoufferStatistic ![2] fun _ => x) (gaussianReal 0 1)
    (gaussianReal 0 1) :=
  hasLaw_stoufferStatistic (by simp) (fun _ => HasLaw.id) (iIndepFun.of_subsingleton)

/-- Inverse-variance weights for variances `1, 2` are `2/3, 1/3`. -/
example : inverseVarianceWeights ![1, 2] = ![2 / 3, 1 / 3] := by
  ext i
  fin_cases i <;> norm_num [inverseVarianceWeights, Fin.sum_univ_two]

/-- Their variance is `(1 + 1/2)⁻¹ = 2/3`; equal weights give `(1 + 2)/4 = 3/4 ≥ 2/3`. -/
example : (∑ j, (![(1 : ℝ), 2] j)⁻¹)⁻¹ = 2 / 3 ∧
    (∑ j, (![(1 : ℝ), 2] j)⁻¹)⁻¹ ≤ ∑ i, (![1 / 2, 1 / 2] i) ^ 2 * ![(1 : ℝ), 2] i := by
  refine ⟨by norm_num [Fin.sum_univ_two], inv_sum_inv_le_sum_sq_mul ?_ ?_⟩
  · intro i; fin_cases i <;> norm_num
  · norm_num [Fin.sum_univ_two]

end MathlibExtTest.Probability.Statistics.MetaAnalysis
