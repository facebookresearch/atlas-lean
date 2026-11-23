/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.KaplanMeier

@[expose] public section

open MeasureTheory Finset
open MathlibExt.Probability.Statistics.KaplanMeier

namespace MathlibExtTest.Probability.Statistics.KaplanMeier

/-- Non-vacuity witness: three subjects observed at times `1, 2, 3`: a death at `1`, a censoring
at `2`, a death at `3`. -/
noncomputable def D₀ : CensoredData 3 where
  time := ![1, 2, 3]
  strictMono_time := by
    refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
    fin_cases i <;> norm_num
  deaths := ![1, 0, 1]
  censored := ![0, 1, 0]

theorem D₀_size : D₀.size = 3 := by decide

theorem D₀_atRisk : D₀.atRisk 0 = 3 ∧ D₀.atRisk 1 = 2 ∧ D₀.atRisk 2 = 1 := by decide

/-- The Kaplan–Meier factors are `2/3`, `1` (no death at the censoring time) and `0`. -/
theorem D₀_kmFactor : D₀.kmFactor 0 = 2 / 3 ∧ D₀.kmFactor 1 = 1 ∧ D₀.kmFactor 2 = 0 := by
  obtain ⟨h0, h1, h2⟩ := D₀_atRisk
  refine ⟨?_, ?_, ?_⟩ <;> simp only [CensoredData.kmFactor, h0, h1, h2] <;>
    norm_num [D₀]

/-- `Ŝ(2) = 2/3`: the censoring at `2` does not change the estimate. -/
example : D₀.kmSurvival 2 = 2 / 3 := by
  obtain ⟨h0, h1, -⟩ := D₀_kmFactor
  have : univ.filter (fun j : Fin 3 => D₀.time j ≤ 2) = {0, 1} := by
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
    fin_cases j <;> norm_num [D₀]
  rw [CensoredData.kmSurvival, this, prod_pair (by decide), h0, h1]
  norm_num

/-- The censored subject's time has positive survival. -/
example : 0 < D₀.kmSurvival (D₀.time 1) :=
  D₀.kmSurvival_pos_of_censored_pos (by decide)

/-- Self-consistency at `t = 2`: `3 · 2/3 = 1 + 1 · (2/3) / (2/3)`. -/
example : (D₀.size : ℝ) * D₀.kmSurvival 2 =
    (∑ j with 2 < D₀.time j, ((D₀.deaths j : ℝ) + D₀.censored j)) +
      ∑ j with D₀.time j ≤ 2,
        (D₀.censored j : ℝ) * (D₀.kmSurvival 2 / D₀.kmSurvival (D₀.time j)) :=
  D₀.size_mul_kmSurvival 2

/-- The Kaplan–Meier measure (leftover mass at `τ = 4`) is a probability measure, and the NPMLE
property holds for, e.g., a unit point mass at `2.5`. -/
example : IsProbabilityMeasure (D₀.kmMeasure 4) := D₀.kmMeasure_isProbabilityMeasure 4

example : D₀.likelihood (Measure.dirac (5 / 2)) ≤ D₀.likelihood (D₀.kmMeasure 4) :=
  D₀.likelihood_le_kmMeasure _ fun j => by fin_cases j <;> norm_num [D₀]

/-- The survival function of the Kaplan–Meier measure at `t = 2` is `Ŝ(2)`. -/
example : (D₀.kmMeasure 4).real (Set.Ioi 2) = D₀.kmSurvival 2 :=
  D₀.kmMeasure_real_Ioi (by norm_num)

/-- Uncensored data: two deaths at time `0` and one at time `1`. -/
noncomputable def D₁ : CensoredData 2 where
  time := ![0, 1]
  strictMono_time := by
    refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
    fin_cases i; norm_num
  deaths := ![2, 1]
  censored := ![0, 0]

/-- Without censoring `Ŝ` is the empirical survival function: `Ŝ(0) = 1/3`. -/
example : D₁.kmSurvival 0 = 1 / 3 := by
  rw [D₁.kmSurvival_of_censored_eq_zero (fun j => by fin_cases j <;> rfl) (by decide)]
  have : univ.filter (fun j : Fin 2 => (0 : ℝ) < D₁.time j) = {1} := by
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    fin_cases j <;> norm_num [D₁]
  rw [this, sum_singleton, show D₁.size = 3 by decide]
  norm_num [D₁]

/-- Boundary (junk-free by design): at a time where nobody is at risk there are no deaths and the
factor is `1`. -/
example : (⟨![0], Subsingleton.strictMono _, ![0], ![0]⟩ :
    CensoredData 1).kmFactor 0 = 1 := by
  simp [CensoredData.kmFactor]

#print axioms CensoredData.likelihood_le_kmMeasure
#print axioms CensoredData.size_mul_kmSurvival

end MathlibExtTest.Probability.Statistics.KaplanMeier
