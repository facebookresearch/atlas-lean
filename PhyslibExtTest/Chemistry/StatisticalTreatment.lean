/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Chemistry.StatisticalTreatment
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Statistical treatment checks

Instances pinning the pooled SD, both outlier procedures on concrete samples, both LOD
conventions, the exact t-interval coverage on a normal sample, and boundary cases (no claim at
`n = 1`; no rejection on degenerate input).
-/

namespace Chemistry.StatisticalTreatmentTest

open MeasureTheory ProbabilityTheory Chemistry.StatisticalTreatment
open MathlibExt.Probability.FiniteProbability (sampleMean sampleVarUnbiased sampleMean_eq_sum_div
  sampleVarUnbiased_eq_sum_div)

@[expose] public section

-- Pooled-SD instance: n1 = 5 with s1² = 0.025, n2 = 4 with s2² = 0.02/3;
-- pooled variance (4*0.025 + 3*(0.02/3))/7 = 0.12/7.
example : pooledVariance 5 4 0.025 (0.02 / 3) = 0.12 / 7 := by
  have e1 : ((5 - 1 : ℕ) : ℝ) = 4 := by norm_num
  have e2 : ((4 - 1 : ℕ) : ℝ) = 3 := by norm_num
  have eD : ((5 + 4 - 2 : ℕ) : ℝ) = 7 := by norm_num
  unfold pooledVariance
  rw [e1, e2, eD]
  norm_num

-- Pooled-SD instance: the pooled SD is the square root of 0.12/7.
example : pooledStdDev 5 4 0.025 (0.02 / 3) = Real.sqrt (0.12 / 7) := by
  have e1 : ((5 - 1 : ℕ) : ℝ) = 4 := by norm_num
  have e2 : ((4 - 1 : ℕ) : ℝ) = 3 := by norm_num
  have eD : ((5 + 4 - 2 : ℕ) : ℝ) = 7 := by norm_num
  unfold pooledStdDev pooledVariance
  rw [e1, e2, eD]
  congr 1
  norm_num

/-! ### Dixon's Q on the sample `9.8, 10.0, 10.2, 10.5` -/

/-- Four replicate measurements; the suspect is the largest, `10.5`. -/
noncomputable def dixonSample : Fin 4 → ℝ := ![9.8, 10.0, 10.2, 10.5]

lemma dixonSample_iSup : (⨆ i, dixonSample i) = 10.5 :=
  le_antisymm (ciSup_le fun i => by fin_cases i <;> norm_num [dixonSample])
    (le_ciSup_of_le (Set.finite_range _).bddAbove 3 (by norm_num [dixonSample]))

lemma dixonSample_iInf : (⨅ i, dixonSample i) = 9.8 :=
  le_antisymm (ciInf_le_of_le (Set.finite_range _).bddBelow 0 (by norm_num [dixonSample]))
    (le_ciInf fun i => by fin_cases i <;> norm_num [dixonSample])

/-- Range `10.5 - 9.8 = 0.7`. -/
lemma dixonSample_range : sampleRange dixonSample = 0.7 := by
  rw [sampleRange, dixonSample_iSup, dixonSample_iInf]
  norm_num

/-- The nearest other observation to `10.5` is `10.2`: gap `0.3`. -/
lemma dixonSample_gap : nearestGap dixonSample 3 = 0.3 := by
  have : Nonempty {i : Fin 4 // i ≠ 3} := ⟨⟨0, by decide⟩⟩
  refine le_antisymm
    (ciInf_le_of_le (Set.finite_range _).bddBelow ⟨2, by decide⟩ (by norm_num [dixonSample]))
    (le_ciInf fun ⟨i, hi⟩ => ?_)
  fin_cases i
  all_goals first
    | exact absurd rfl hi
    | norm_num [dixonSample, abs_of_pos, abs_of_nonneg]

/-- Q = 0.3/0.7 = 3/7. -/
lemma dixonSample_Q : dixonQ dixonSample 3 = 3 / 7 := by
  rw [dixonQ_of_ne _ _ (by rw [dixonSample_range]; norm_num), dixonSample_range, dixonSample_gap]
  norm_num

-- The suspect is extreme (it is the sample maximum).
example : IsExtremeObservation dixonSample 3 :=
  Or.inl (by rw [dixonSample_iSup]; norm_num [dixonSample])

-- Dixon procedure instance: Q = 3/7 rejects at qcrit = 0.41.
example : dixonReject dixonSample 3 0.41 :=
  ⟨Or.inl (by rw [dixonSample_iSup]; norm_num [dixonSample]), by rw [dixonSample_Q]; norm_num⟩

-- Dixon procedure instance: Q = 3/7 does not reject at qcrit = 0.56.
example : ¬ dixonReject dixonSample 3 0.56 := by
  rintro ⟨-, h⟩
  rw [dixonSample_Q] at h
  norm_num at h

-- A non-extreme observation (`10.0`) is never rejected, whatever its Q.
example (q : ℝ) : ¬ dixonReject dixonSample 1 q := by
  rintro ⟨h | h, -⟩
  · rw [dixonSample_iSup] at h
    norm_num [dixonSample] at h
  · rw [dixonSample_iInf] at h
    norm_num [dixonSample] at h

/-! ### Grubbs' G on the sample `0, 0, 0, 4` -/

/-- Mean `1`, sample variance `(1 + 1 + 1 + 9) / 3 = 4`, standard deviation `2`, largest absolute
deviation `3`. -/
noncomputable def grubbsSample : Fin 4 → ℝ := ![0, 0, 0, 4]

lemma grubbsSample_mean : sampleMean grubbsSample = 1 := by
  rw [sampleMean_eq_sum_div, Fin.sum_univ_four, Fintype.card_fin]
  norm_num [grubbsSample]

lemma grubbsSample_sd : sampleStdDev grubbsSample = 2 := by
  have hv : sampleVarUnbiased grubbsSample = 4 := by
    rw [sampleVarUnbiased_eq_sum_div, grubbsSample_mean, Fin.sum_univ_four, Fintype.card_fin]
    norm_num [grubbsSample]
  rw [sampleStdDev, hv, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

lemma grubbsSample_maxDev : (⨆ i, |grubbsSample i - sampleMean grubbsSample|) = 3 := by
  rw [grubbsSample_mean]
  exact le_antisymm (ciSup_le fun i => by fin_cases i <;> norm_num [grubbsSample])
    (le_ciSup_of_le (Set.finite_range _).bddAbove 3 (by norm_num [grubbsSample]))

/-- G = 3/2. -/
lemma grubbsSample_G : grubbsG grubbsSample = 3 / 2 := by
  rw [grubbsG_of_ne _ (by rw [grubbsSample_sd]; norm_num), grubbsSample_maxDev, grubbsSample_sd]

-- Grubbs procedure instance: G = 1.5 rejects at gcrit = 1.4 and not at gcrit = 1.6.
example : grubbsReject grubbsSample 1.4 := by
  unfold grubbsReject
  rw [grubbsSample_G]
  norm_num

example : ¬ grubbsReject grubbsSample 1.6 := by
  unfold grubbsReject
  rw [grubbsSample_G]
  norm_num

-- Every standardized residual is at most G: observation `0` has `|0 - 1| / 2 = 1/2 ≤ 3/2`.
example : |grubbsSample 0 - sampleMean grubbsSample| / sampleStdDev grubbsSample
    ≤ grubbsG grubbsSample :=
  div_le_grubbsG _ (by rw [grubbsSample_sd]; norm_num) 0

-- LOD under the k = 3 convention: s = 0.02, m = 0.5 gives 0.12.
example : lodK3 0.02 0.5 = 0.12 := by
  unfold lodK3
  norm_num

-- LOD under the k = 3.3 convention: s = 0.02, m = 0.5 gives 0.132.
example : lodK33 0.02 0.5 = 0.132 := by
  unfold lodK33
  norm_num

-- t-interval duality instance: 10.1 lies within half-width 0.2 of 10.0
-- (half-width 0.8*0.5/√4 = 0.2).
example : (10.1 : ℝ) ∈ tInterval 10.0 0.5 4 0.8 := by
  have hsqrt : Real.sqrt ((4 : ℕ) : ℝ) = 2 := by
    rw [show ((4 : ℕ) : ℝ) = 2 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [mem_tInterval_iff]
  unfold tHalfWidth
  rw [hsqrt]
  norm_num

-- Exact coverage on a concrete normal sample: the coordinates of `ℝ³` under the product of three
-- standard normal laws, so every hypothesis of `tInterval_coverage` is met.
example {α : ℝ} (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    (Measure.pi fun _ : Fin 3 => gaussianReal 0 1).real
      {x | (0 : ℝ) ∈ tInterval (sampleMean x) (sampleStdDev x) 3
        (cdfQuantile (studentTMeasure (3 - 1)) (1 - α / 2))} = 1 - α :=
  tInterval_coverage (by norm_num) 0 one_ne_zero hα HasLaw.id

-- Boundary: n = 1 gives no t-procedure claim (the sample variance degenerates to 0).
example (x : Fin 1 → ℝ) : sampleVarUnbiased x = 0 := sampleVarUnbiased_fin_one x

-- Boundary: hypotheses needing 2 ≤ n are vacuous at n = 1.
example : ¬ (2 ≤ 1) := by decide

-- Boundary: zero-spread input gives no Grubbs claim.
example (x : Fin 3 → ℝ) (h : sampleStdDev x = 0) : grubbsG x = 0 := grubbsG_of_sd_zero x h

-- Boundary: no-spread input gives Q = 0, hence no Dixon rejection at a nonnegative threshold.
example (x : Fin 3 → ℝ) (j : Fin 3) (h : sampleRange x = 0) : dixonQ x j = 0 :=
  dixonQ_of_no_spread x j h

-- Boundary: constant samples have zero SD, so Grubbs reports 0 end to end.
example (c : ℝ) (x : Fin 5 → ℝ) (h : ∀ i, x i = c) : grubbsG x = 0 :=
  grubbsG_of_sd_zero x (sampleStdDev_const 5 (by norm_num) c x h)

end

end Chemistry.StatisticalTreatmentTest
