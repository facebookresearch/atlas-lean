/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Statistics.NormalTheoryTwoSample

/-!
# Tests for `MathlibExt.Probability.Statistics.NormalTheoryTwoSample`

Values of `pooledVariance`, `twoSampleTStatistic` and `varianceRatio` computed from their
definitions on concrete data, including the degenerate zero-spread sample. The hypotheses of the
main theorems are discharged on the canonical model (the product of the two sample laws with the
coordinate projections), so they are satisfiable; the theorems are then applied there, at the
smallest admissible sample sizes (`t_1` and `F(1, 1)`), and at a conventional level.
-/

namespace ProbabilityTheory.NormalTheoryTwoSampleTest

open MeasureTheory ProbabilityTheory Real Filter

/-! ### Definitions on concrete data -/

/-- `x = (1, 3)`, `y = (2, 4, 6)`: `x̄ = 2`, `ȳ = 4`, the sums of squares are `2` and `8`, so
`S_p² = 10 / 3`. -/
example : pooledVariance ![(1 : ℝ), 3] ![(2 : ℝ), 4, 6] = 10 / 3 := by
  norm_num [pooledVariance, Fin.sum_univ_succ]

/-- On the same data, `T = (2 - 4) / √(10/3 · (1/2 + 1/3)) = -2 / (5/3) = -6/5`. -/
example : twoSampleTStatistic 0 ![(1 : ℝ), 3] ![(2 : ℝ), 4, 6] = -6 / 5 := by
  rw [twoSampleTStatistic, show pooledVariance ![(1 : ℝ), 3] ![(2 : ℝ), 4, 6] = 10 / 3 by
    norm_num [pooledVariance, Fin.sum_univ_succ]]
  norm_num [Fin.sum_univ_succ]
  rw [show (25 : ℝ) = 5 ^ 2 by norm_num, show (9 : ℝ) = 3 ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num), Real.sqrt_sq (by norm_num)]
  norm_num

/-- The hypothesized difference shifts the numerator: with `δ = -2` the statistic is `0`. -/
example : twoSampleTStatistic (-2) ![(1 : ℝ), 3] ![(2 : ℝ), 4, 6] = 0 := by
  norm_num [twoSampleTStatistic, Fin.sum_univ_succ]

/-- `S_X² = 2 / 1`, `S_Y² = 8 / 2`, so `S_X² / S_Y² = 1 / 2`. -/
example : varianceRatio ![(1 : ℝ), 3] ![(2 : ℝ), 4, 6] = 1 / 2 := by
  norm_num [varianceRatio, Fin.sum_univ_succ]

/-- Degenerate data: constant samples have `S_p² = 0`, and the statistic takes the junk value `0`
(division by `√0 = 0`), whatever `δ` is. The theorems never see this case: it has probability
zero under the normal model. -/
example (δ : ℝ) : pooledVariance ![(1 : ℝ), 1] ![(1 : ℝ), 1, 1] = 0 ∧
    twoSampleTStatistic δ ![(1 : ℝ), 1] ![(1 : ℝ), 1, 1] = 0 := by
  refine ⟨by norm_num [pooledVariance, Fin.sum_univ_succ], ?_⟩
  norm_num [twoSampleTStatistic, pooledVariance, Fin.sum_univ_succ]

/-! ### The hypotheses are satisfiable: the canonical two-sample model -/

/-- The product of the two sample laws. -/
noncomputable abbrev model (m n : ℕ) (μ₁ μ₂ : ℝ) (v₁ v₂ : NNReal) :
    Measure ((Fin m → ℝ) × (Fin n → ℝ)) :=
  (Measure.pi fun _ : Fin m => gaussianReal μ₁ v₁).prod
    (Measure.pi fun _ : Fin n => gaussianReal μ₂ v₂)

lemma hasLaw_fst (m n : ℕ) (μ₁ μ₂ : ℝ) (v₁ v₂ : NNReal) :
    HasLaw Prod.fst (Measure.pi fun _ : Fin m => gaussianReal μ₁ v₁) (model m n μ₁ μ₂ v₁ v₂) :=
  measurePreserving_fst.hasLaw

lemma hasLaw_snd (m n : ℕ) (μ₁ μ₂ : ℝ) (v₁ v₂ : NNReal) :
    HasLaw Prod.snd (Measure.pi fun _ : Fin n => gaussianReal μ₂ v₂) (model m n μ₁ μ₂ v₁ v₂) :=
  measurePreserving_snd.hasLaw

lemma indep_fst_snd (m n : ℕ) (μ₁ μ₂ : ℝ) (v₁ v₂ : NNReal) :
    IndepFun (Prod.fst : (Fin m → ℝ) × (Fin n → ℝ) → _) Prod.snd (model m n μ₁ μ₂ v₁ v₂) :=
  indepFun_prod measurable_id measurable_id

/-! ### The theorems applied on the canonical model -/

/-- Smallest sample sizes, `m = 1`, `n = 2`: one degree of freedom, the Cauchy law `t_1`. -/
example (μ₁ μ₂ : ℝ) {v : NNReal} (hv : v ≠ 0) :
    HasLaw (fun p : (Fin 1 → ℝ) × (Fin 2 → ℝ) => twoSampleTStatistic (μ₁ - μ₂) p.1 p.2)
      (studentTMeasure 1) (model 1 2 μ₁ μ₂ v v) :=
  hasLaw_twoSampleTStatistic le_rfl (by norm_num) le_rfl μ₁ μ₂ hv
    (hasLaw_fst 1 2 μ₁ μ₂ v v) (hasLaw_snd 1 2 μ₁ μ₂ v v) (indep_fst_snd 1 2 μ₁ μ₂ v v)

/-- The `95%` pooled interval for `m = 5`, `n = 7` (`t_10`) has coverage exactly `19/20`. -/
example (μ₁ μ₂ : ℝ) {v : NNReal} (hv : v ≠ 0) :
    (model 5 7 μ₁ μ₂ v v).real {p | |(∑ i, p.1 i) / (5 : ℕ) - (∑ j, p.2 j) / (7 : ℕ) - (μ₁ - μ₂)| ≤
        cdfQuantile (studentTMeasure (5 + 7 - 2)) (1 - (1 / 20) / 2) *
          √(pooledVariance p.1 p.2 * (1 / (5 : ℕ) + 1 / (7 : ℕ)))} = 1 - 1 / 20 :=
  twoSample_t_interval_coverage_eq (by norm_num) (by norm_num) (by norm_num) μ₁ μ₂ hv
    ⟨by norm_num, by norm_num⟩ (hasLaw_fst 5 7 μ₁ μ₂ v v) (hasLaw_snd 5 7 μ₁ μ₂ v v)
    (indep_fst_snd 5 7 μ₁ μ₂ v v)

/-- The every-threshold identity at a negative threshold: both sides are `0`, the `t` side
computed directly (empty interval), so the identity forces the coverage event to be null. -/
example (μ₁ μ₂ : ℝ) {v : NNReal} (hv : v ≠ 0) :
    (model 2 2 μ₁ μ₂ v v).real {p | |(∑ i, p.1 i) / (2 : ℕ) - (∑ j, p.2 j) / (2 : ℕ) - (μ₁ - μ₂)| ≤
        (-1) * √(pooledVariance p.1 p.2 * (1 / (2 : ℕ) + 1 / (2 : ℕ)))} = 0 := by
  rw [twoSample_t_interval_measureReal_eq (by norm_num) (by norm_num) (by norm_num) μ₁ μ₂ hv
    (-1) (hasLaw_fst 2 2 μ₁ μ₂ v v) (hasLaw_snd 2 2 μ₁ μ₂ v v) (indep_fst_snd 2 2 μ₁ μ₂ v v),
    Set.Icc_eq_empty (by norm_num), measureReal_empty]

/-- Two-sided and one-sided pooled `t` tests at level `α` have size exactly `α`. -/
example (μ₁ μ₂ : ℝ) {v : NNReal} (hv : v ≠ 0) {α : ℝ} (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    (model 3 4 μ₁ μ₂ v v).real {p | cdfQuantile (studentTMeasure (3 + 4 - 2)) (1 - α / 2) <
        |twoSampleTStatistic (μ₁ - μ₂) p.1 p.2|} = α ∧
    (model 3 4 μ₁ μ₂ v v).real {p | cdfQuantile (studentTMeasure (3 + 4 - 2)) (1 - α) <
        twoSampleTStatistic (μ₁ - μ₂) p.1 p.2} = α :=
  ⟨twoSample_t_test_size_eq (by norm_num) (by norm_num) (by norm_num) μ₁ μ₂ hv hα
      (hasLaw_fst 3 4 μ₁ μ₂ v v) (hasLaw_snd 3 4 μ₁ μ₂ v v) (indep_fst_snd 3 4 μ₁ μ₂ v v),
    twoSample_t_one_sided_test_size_eq (by norm_num) (by norm_num) (by norm_num) μ₁ μ₂ hv hα
      (hasLaw_fst 3 4 μ₁ μ₂ v v) (hasLaw_snd 3 4 μ₁ μ₂ v v) (indep_fst_snd 3 4 μ₁ μ₂ v v)⟩

/-- Smallest `F` case, `m = n = 2`: with different variances the pivot is `F(1, 1)`. -/
example (μ₁ μ₂ : ℝ) {v₁ v₂ : NNReal} (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) :
    HasLaw (fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) => varianceRatio p.1 p.2 / ((v₁ : ℝ) / v₂))
      (snedecorFMeasure 1 1) (model 2 2 μ₁ μ₂ v₁ v₂) :=
  hasLaw_varianceRatio_div le_rfl le_rfl μ₁ μ₂ hv₁ hv₂ (hasLaw_fst 2 2 μ₁ μ₂ v₁ v₂)
    (hasLaw_snd 2 2 μ₁ μ₂ v₁ v₂) (indep_fst_snd 2 2 μ₁ μ₂ v₁ v₂)

/-- Equal variances: the ratio itself is `F(3, 5)`, and the one-sided `F` test has size `α`. -/
example (μ₁ μ₂ : ℝ) {v : NNReal} (hv : v ≠ 0) {α : ℝ} (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    HasLaw (fun p : (Fin 4 → ℝ) × (Fin 6 → ℝ) => varianceRatio p.1 p.2)
      (snedecorFMeasure (4 - 1) (6 - 1)) (model 4 6 μ₁ μ₂ v v) ∧
    (model 4 6 μ₁ μ₂ v v).real {p | cdfQuantile (snedecorFMeasure (4 - 1) (6 - 1)) (1 - α) <
        varianceRatio p.1 p.2} = α :=
  ⟨hasLaw_varianceRatio (by norm_num) (by norm_num) μ₁ μ₂ hv (hasLaw_fst 4 6 μ₁ μ₂ v v)
      (hasLaw_snd 4 6 μ₁ μ₂ v v) (indep_fst_snd 4 6 μ₁ μ₂ v v),
    varianceRatio_test_size_eq (by norm_num) (by norm_num) μ₁ μ₂ hv hα
      (hasLaw_fst 4 6 μ₁ μ₂ v v) (hasLaw_snd 4 6 μ₁ μ₂ v v) (indep_fst_snd 4 6 μ₁ μ₂ v v)⟩

/-- The `90%` interval for `v₁ / v₂` with unequal true variances has coverage exactly `9/10`. -/
example (μ₁ μ₂ : ℝ) :
    (model 3 3 μ₁ μ₂ 2 5).real {p | varianceRatio p.1 p.2 /
          cdfQuantile (snedecorFMeasure (3 - 1) (3 - 1)) (1 - (1 / 10) / 2) ≤
            ((2 : NNReal) : ℝ) / (5 : NNReal) ∧
        ((2 : NNReal) : ℝ) / (5 : NNReal) ≤ varianceRatio p.1 p.2 /
          cdfQuantile (snedecorFMeasure (3 - 1) (3 - 1)) ((1 / 10) / 2)} = 1 - 1 / 10 :=
  varianceRatio_interval_coverage_eq (by norm_num) (by norm_num) μ₁ μ₂ (by norm_num)
    (by norm_num) ⟨by norm_num, by norm_num⟩ (hasLaw_fst 3 3 μ₁ μ₂ 2 5)
    (hasLaw_snd 3 3 μ₁ μ₂ 2 5) (indep_fst_snd 3 3 μ₁ μ₂ 2 5)

/-! ### Slutsky transfer -/

/-- The Slutsky corollary along `m N = n N = N + 2`, `N → ∞`, with a standard normal limit. -/
example {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X Y : ∀ N : ℕ, Ω → Fin (N + 2) → ℝ} (hX : ∀ N, AEMeasurable (X N) P)
    (hY : ∀ N, AEMeasurable (Y N) P) {δ : ℝ}
    (hZ : TendstoInDistribution (fun N ω => ((∑ i, X N ω i) / (N + 2 : ℕ) -
      (∑ j, Y N ω j) / (N + 2 : ℕ) - δ) / (1 * √(1 / (N + 2 : ℕ) + 1 / (N + 2 : ℕ)))) atTop id
      (fun _ => P) (gaussianReal 0 1))
    (hS : TendstoInMeasure P (fun N ω => pooledVariance (X N ω) (Y N ω)) atTop
      (fun _ => (1 : ℝ) ^ 2)) :
    TendstoInDistribution (fun N ω => twoSampleTStatistic δ (X N ω) (Y N ω)) atTop id
      (fun _ => P) (gaussianReal 0 1) :=
  tendstoInDistribution_twoSampleTStatistic hX hY one_pos hZ hS

end ProbabilityTheory.NormalTheoryTwoSampleTest
