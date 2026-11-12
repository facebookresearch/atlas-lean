/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.StatisticalGenetics.RareVariantInference.GenomicControlEstimated

@[expose] public section

open MeasureTheory ProbabilityTheory
  MathlibExt.Biology.StatisticalGenetics.RareVariantInference
  MathlibExt.Biology.StatisticalGenetics.RareVariantInference.GenomicControl
  MathlibExt.Biology.StatisticalGenetics.RareVariantInference.GenomicControlEstimated
  MathlibExt.Probability.Statistics.MultipleTesting
open scoped NNReal ENNReal

namespace MathlibExtTest.Biology.StatisticalGenetics.RareVariantInference.GenomicControlEstimated

/-! ### The estimator and the corrected statistics, computed from the definitions -/

/-- Scores `(1, 2)`: `λ̂ = (1 + 4) / 2 = 5/2`. -/
example : lambdaHat ![(1 : ℝ), 2] = 5 / 2 := by
  simp [lambdaHat, Fin.sum_univ_two]
  norm_num

/-- `T₀ = 1 / (5/2) = 2/5` and `T₁ = 4 / (5/2) = 8/5`; they sum to `m = 2`. -/
example : gcStat ![(1 : ℝ), 2] 0 = 2 / 5 ∧ gcStat ![(1 : ℝ), 2] 1 = 8 / 5 := by
  constructor <;> simp [gcStat, lambdaHat, Fin.sum_univ_two] <;> norm_num

example : gcStat ![(1 : ℝ), 2] 0 + gcStat ![(1 : ℝ), 2] 1 = 2 :=
  gcStat_two_add _ (by simp [Fin.sum_univ_two]; norm_num)

/-- Boundary: the self-coupling bound `T_j ≤ m` is attained when only gene `j` has signal. -/
example : gcStat ![(1 : ℝ), 0] 0 = 2 := by
  simp [gcStat, lambdaHat, Fin.sum_univ_two]

example (j : Fin 3) : gcStat (fun _ => (1 : ℝ)) j = 1 := by
  simp [gcStat, lambdaHat]

/-- Boundary: with all scores zero, `λ̂ = 0` and the statistic is `0` by convention. -/
example (j : Fin 3) : gcStat (0 : Fin 3 → ℝ) j = 0 := by
  simp [gcStat, lambdaHat]

example (z : Fin 4 → ℝ) (j : Fin 4) : 0 ≤ gcStat z j ∧ gcStat z j ≤ 4 :=
  ⟨gcStat_nonneg z j, by simpa using gcStat_le_card z j⟩

/-- Cross-coupling: raising gene `1` from `2` to `3` lowers `T₀` from `2/5` to `2/10`. -/
example : gcStat (Function.update ![(1 : ℝ), 2] 1 3) 0 < gcStat ![(1 : ℝ), 2] 0 :=
  gcStat_update_lt _ (by decide) (by simp) (by norm_num)

/-! ### The `χ²₁` reference tail -/

example : 0 < chiSqOneTail 3 := chiSqOneTail_pos (by norm_num)

example : chiSqOneTailReal 2 < chiSqOneTailReal 1 :=
  chiSqOneTailReal_lt_of_lt zero_le_one one_lt_two

example : chiSqOneTail 1 < 1 / 2 := chiSqOneTail_one_lt_half

/-! ### Exact calibration with `λ̂` is impossible -/

/-- On any law, the corrected statistic never exceeds `m = 3`. -/
example : (Measure.dirac ()) {ω | (3 : ℝ) < gcStatRV (fun (_ : Fin 3) (_ : Unit) => (1 : ℝ)) 0 ω}
    = 0 :=
  measure_lt_gcStatRV_eq_zero _ 0 (by norm_num)

example : ¬ ∀ c, (Measure.dirac ()) {ω | c < gcStatRV (fun (_ : Fin 3) (_ : Unit) => (1 : ℝ)) 0 ω}
    = chiSqOneTail c :=
  not_forall_measure_lt_gcStatRV_eq _ 0

/-! ### Two independent Gaussian null genes (T38's model plus independence)

The sample space is `ℝ × ℝ` with `𝒩(0, 1) ⊗ 𝒩(0, 1)`; the two scores are the coordinates. -/

/-- The product measure of two standard Gaussians. -/
noncomputable abbrev P2 : Measure (ℝ × ℝ) := (gaussianReal 0 1).prod (gaussianReal 0 1)

/-- Two null scores with common variance `λ = 1` in T38's `CommonInflationModel`. -/
noncomputable def G2 : CommonInflationModel P2 (Fin 2) where
  lam := 1
  lam_ne_zero := one_ne_zero
  score := ![Prod.fst, Prod.snd]
  hasLaw_score := fun i => by
    fin_cases i
    · exact ⟨measurable_fst.aemeasurable, by simp⟩
    · exact ⟨measurable_snd.aemeasurable, by simp⟩

theorem G2_measurable : ∀ i, Measurable (G2.score i) := fun i => by
  fin_cases i
  · exact measurable_fst
  · exact measurable_snd

theorem G2_indep : IndepFun (G2.score 0) (G2.score 1) P2 :=
  indepFun_prod (μ := gaussianReal 0 1) (ν := gaussianReal 0 1) measurable_id measurable_id

/-- True-`λ` calibration holds at every threshold, `λ̂` calibration fails at `c ≥ 2`. -/
example : (∀ c, P2 {ω | c < G2.score 0 ω ^ 2 / G2.lam} = chiSqOneTail c) ∧
    ∀ c, (2 : ℝ) ≤ c → P2 {ω | c < gcStatRV G2.score 0 ω} < chiSqOneTail c := by
  simpa using calibrated_true_and_not_calibrated_estimated G2 0

/-- Anti-conservative at threshold `1`: rejection probability `≥ 1/2 > P(χ²₁ > 1)`. -/
example : chiSqOneTail 1 < P2 {ω | 1 ≤ gcStatRV G2.score 0 ω} :=
  chiSqOneTail_lt_measure_one_le_gcStatRV_two G2 G2_measurable G2_indep

example : 1 / 2 ≤ P2 {ω | gcStatRV G2.score 0 ω < 1} :=
  half_le_measure_gcStatRV_two_lt_one G2 G2_measurable G2_indep

/-- The calibration assumption of `RareVariantInference.MultipleTesting` fails here. -/
example : ¬ MultipleTesting.IsTailCalibratedFamily P2 (gcStatRV G2.score)
    (fun _ => chiSqOneTailReal) {0, 1} :=
  not_isTailCalibratedFamily_gcStatRV_two G2 G2_measurable G2_indep (by simp)

/-- The `χ²₁` p-values of the corrected statistics are not PRDS. -/
example : ¬ IsPRDSOn P2 (MultipleTesting.tailPValue (gcStatRV G2.score) fun _ => chiSqOneTailReal)
    {0} :=
  not_isPRDSOn_tailPValue_gcStatRV_two_of_indep G2 G2_measurable G2_indep (by simp)

/-- Negative coupling: `Cov(T₀, T₁) < 0`, and `T₀` is nondegenerate. -/
example : cov[gcStatRV G2.score 0, gcStatRV G2.score 1; P2] < 0 ∧
    0 < Var[gcStatRV G2.score 0; P2] :=
  ⟨covariance_gcStatRV_two_neg G2 G2_measurable G2_indep,
    variance_gcStatRV_two_pos G2 G2_measurable G2_indep⟩

example : ∃ i k : Fin 2, i ≠ k ∧ cov[gcStatRV G2.score i, gcStatRV G2.score k; P2] < 0 :=
  exists_covariance_gcStatRV_neg G2_measurable (ae_sum_sq_ne_zero G2 G2_measurable)
    (variance_gcStatRV_two_pos G2 G2_measurable G2_indep)

/-! ### The calibration assumption and Bonferroni -/

example (hcal : ∀ i ∈ ({0, 1} : Finset (Fin 2)), ∀ s, P2 {ω | s ≤ gcStatRV G2.score i ω} ≤
    chiSqOneTail s) :
    MultipleTesting.IsTailCalibratedFamily P2 (gcStatRV G2.score) (fun _ => chiSqOneTailReal)
      {0, 1} :=
  (isTailCalibratedFamily_gcStatRV_iff G2_measurable _).2 hcal

example {s : ℝ} (hcal : ∀ i ∈ ({0, 1} : Finset (Fin 2)), P2 {ω | s ≤ gcStatRV G2.score i ω} ≤
    chiSqOneTail s) :
    P2 {ω | ∃ i ∈ ({0, 1} : Finset (Fin 2)), s ≤ gcStatRV G2.score i ω} ≤ 2 * chiSqOneTail s := by
  simpa using measure_exists_le_gcStatRV_le G2.score hcal

/-! ### Sandwich bounds for a random `λ̂`

One score `x ∼ 𝒩(0, 2)` (true `λ = 2`). -/

/-- `L ≡ λ`: the upper sandwich with `E = univ`, `κ = 1` recovers the exact tail as a bound. -/
example (c : ℝ) (hc : 0 ≤ c) : gaussianReal 0 2 {x | c < x ^ 2 / 2} ≤ chiSqOneTail c := by
  have h := measure_lt_div_le_chiSqOneTail_add (P := gaussianReal 0 2) (two_ne_zero)
    HasLaw.id (L := fun _ => 2) one_pos (E := Set.univ) (fun _ _ => by simp) hc
  simpa using h

/-- `L ≡ 2` against `λ = 2`: the lower sandwich with `κ = 1`. -/
example (c : ℝ) (hc : 0 ≤ c) : chiSqOneTail c ≤ gaussianReal 0 2 {x | c < x ^ 2 / 2} := by
  have h := chiSqOneTail_le_measure_lt_div_add (P := gaussianReal 0 2) (κ := 1) (two_ne_zero)
    HasLaw.id (L := fun _ => 2) (E := Set.univ) (fun _ _ => by norm_num) hc
  simpa using h

/-- Under-estimated `λ̂ ≡ 1 = λ / 2`: anti-conservative. -/
example : chiSqOneTail 1 < gaussianReal 0 2 {x | 1 < x ^ 2 / 1} :=
  chiSqOneTail_lt_measure_lt_div_of_le_mul two_ne_zero HasLaw.id (L := fun _ => 1)
    (κ := 1 / 2) (by norm_num) (by norm_num) (fun _ => by norm_num) one_pos

/-- Over-estimated `λ̂ ≡ 4 = 2 λ`: conservative. -/
example : gaussianReal 0 2 {x | 1 < x ^ 2 / 4} < chiSqOneTail 1 :=
  measure_lt_div_lt_chiSqOneTail_of_mul_le two_ne_zero HasLaw.id (L := fun _ => 4)
    (κ := 2) (by norm_num) (fun _ => by norm_num) one_pos

/-! ### The PRDS separation criterion on a counter-monotone pair

Two equally likely outcomes; `p₁ = 1 - p₀`. -/

/-- A counter-monotone pair of p-values on `Bool`. -/
def pBool : Fin 2 → Bool → ℝ := ![fun b => if b then 0 else 1, fun b => if b then 1 else 0]

example : ¬ IsPRDSOn (Measure.dirac true + Measure.dirac false) pBool {0} := by
  refine not_isPRDSOn_of_separated (i := 0) (k := 1) (s := 0) (t := 1) (u := 1 / 2)
    (fun _ => measurable_of_countable _) (by simp) zero_le_one ?_ ?_
    (ae_of_all _ fun b hb => ?_) (ae_of_all _ fun b h1 _ => ?_)
  · have : {b | pBool 0 b ≤ 0} = {true} := by ext b; cases b <;> simp [pBool]
    simp [this]
  · have : {b | 0 < pBool 0 b ∧ pBool 0 b ≤ 1} = {false} := by ext b; cases b <;> simp [pBool]
    simp [this]
  · revert hb; cases b <;> norm_num [pBool]
  · cases b <;> simp [pBool] at h1 ⊢

end MathlibExtTest.Biology.StatisticalGenetics.RareVariantInference.GenomicControlEstimated
