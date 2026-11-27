/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.SplitConformalExactCoverage
public import MathlibExt.Probability.Distributions.BetaBinomialSampleRank
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

@[expose] public section

open MeasureTheory MathlibExt.Probability.Statistics.SplitConformal
  MathlibExt.Probability.Statistics.SplitConformalExactCoverage
  MathlibExt.Probability.Distributions.BetaBinomialSampleRank

namespace MathlibExtTest.Probability.Statistics.SplitConformalExactCoverage

/-- The uniform law on `[0, 1]`, an atomless probability measure, for non-vacuity checks. -/
noncomputable abbrev unifIcc : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)

instance : IsProbabilityMeasure unifIcc := ⟨by simp [unifIcc]⟩

/-! ### The deterministic count -/

theorem injective_two_zero_one : Function.Injective ![(2 : ℝ), 0, 1] := by
  intro i j h
  fin_cases i <;> fin_cases j <;> first | rfl | (norm_num at h)

/-- Distinct values `(2, 0, 1)`: exactly two coordinates have rank count below `2`. -/
example : (Finset.univ.filter fun i => rankCount ![(2 : ℝ), 0, 1] i < 2).card = 2 :=
  card_filter_rankCount_lt_of_injective injective_two_zero_one (by simp)

/-- With ties the count can exceed `k`: for `(0, 0, 1)` and `k = 1`, two coordinates have no
coordinate strictly below them. This is why the exact-coverage theorem assumes no ties. -/
example : (Finset.univ.filter fun i => rankCount ![(0 : ℝ), 0, 1] i < 1).card = 2 := by
  simp only [rankCount, Finset.card_filter, Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num

/-! ### Exact coverage and the upper bound are not vacuous -/

/-- I.i.d. uniform scores (`n = 3` calibration scores and one test score) are exchangeable and
almost surely distinct, so the coverage at `k = 2` is exactly `2 / 4`. -/
example :
    (Measure.pi fun _ : Fin (3 + 1) => unifIcc)
        {ω | (ω (Fin.last 3) : WithTop ℝ) ≤ splitConformalThreshold 2 ω} = (2 : ENNReal) / (3 + 1) :=
  measure_coe_le_splitConformalThreshold_eq_of_ae_injective _ (map_comp_perm_pi unifIcc)
    (ae_injective_pi unifIcc) (by norm_num) (by norm_num)

/-- The upper bound at `α = 1/4`, `n = 3`: coverage at most `1 - 1/4 + 1/4 = 1`; at `α = 1/2`,
`n = 9`, coverage at most `1/2 + 1/10`. -/
example :
    (Measure.pi fun _ : Fin (9 + 1) => unifIcc)
        {ω | (ω (Fin.last 9) : WithTop ℝ) ≤
          splitConformalThreshold ⌈(1 - (1 / 2 : ℝ)) * ((9 : ℕ) + 1)⌉₊ ω} ≤
      ENNReal.ofReal (1 - 1 / 2 + 1 / ((9 : ℕ) + 1)) :=
  measure_coe_le_splitConformalThreshold_le _ (map_comp_perm_pi unifIcc)
    (ae_injective_pi unifIcc) (by norm_num) (by norm_num)

/-- `k = n + 1`: the threshold is `⊤` and the exact coverage is `1`. -/
example (n : ℕ) :
    (Measure.pi fun _ : Fin (n + 1) => unifIcc)
        {ω | (ω (Fin.last n) : WithTop ℝ) ≤ splitConformalThreshold (n + 1) ω} =
      ((n + 1 : ℕ) : ENNReal) / (n + 1) :=
  measure_coe_le_splitConformalThreshold_eq_of_ae_injective _ (map_comp_perm_pi unifIcc)
    (ae_injective_pi unifIcc) (by omega) le_rfl

end MathlibExtTest.Probability.Statistics.SplitConformalExactCoverage
