/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.ProcessInference
public import MathlibExtTest.Probability.Statistics.Survival.CoxPartialLikelihood

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Finset
open MathlibExt.Probability.Statistics.ProcessInference
open MathlibExt.Probability.Statistics.CoxPartialLikelihood
open MathlibExtTest.Probability.Statistics.CoxPartialLikelihood

namespace MathlibExtTest.Probability.Statistics.ProcessInference

/-! ### `waldInterval`: interior, boundary, exterior -/

example : (1 : ℝ) ∈ waldInterval 0 1 2 := by
  rw [mem_waldInterval_iff]; norm_num

/-- The endpoint `est + z * se` is covered (closed interval). -/
example : (2 : ℝ) ∈ waldInterval 0 1 2 := by
  rw [mem_waldInterval_iff]; norm_num

example : (3 : ℝ) ∉ waldInterval 0 1 2 := by
  rw [mem_waldInterval_iff]; norm_num

/-- With standard error `s / √n`, membership is the studentized event. -/
example : (0 : ℝ) ∈ waldInterval 1 (2 / √(4 : ℕ)) 1 := by
  rw [mem_waldInterval_div_sqrt_iff (by norm_num)]
  have : √((4 : ℕ) : ℝ) = 2 := by
    rw [show ((4 : ℕ) : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [this]; norm_num

/-! ### `gridBand`: simultaneous membership is strictly stronger than one coordinate -/

/-- Grid point `0` is inside its interval but grid point `1` is not, so the function is
outside the simultaneous band. -/
example : (![0, 5] : Fin 2 → ℝ) ∉ gridBand ![0, 0] ![1, 1] 2 := by
  intro h
  have h1 := mem_waldInterval_iff.1 (h 1)
  norm_num at h1

example : (![0, 5] : Fin 2 → ℝ) 0 ∈ waldInterval 0 1 2 := by
  rw [mem_waldInterval_iff]; norm_num

example : (![1, -1] : Fin 2 → ℝ) ∈ gridBand ![0, 0] ![1, 1] 2 := by
  intro j
  rw [mem_waldInterval_iff]
  fin_cases j <;> norm_num

/-! ### `logRankRejects` on the two-subject sample from the Cox test file

`O - E = 1 / 2` and the Breslow information is `1 / 4`, so the test rejects exactly when
`z * (1 / 2) < 1 / 2`, i.e. `z < 1`. -/

theorem observedMinusExpected_T₀ : observedMinusExpected T₀ δ₀ g₀ = 1 / 2 := by
  rw [observedMinusExpected, filter_δ₀, Fin.sum_univ_two]
  simp only [numAtRisk, numAtRiskIn, riskSet_T₀_zero, riskSet_T₀_one, filter_g₀_univ,
    filter_g₀_one]
  norm_num [groupIndicator, g₀]

theorem breslowInformation_T₀ : breslowInformation T₀ δ₀ g₀ = 1 / 4 := by
  rw [breslowInformation, filter_δ₀, Fin.sum_univ_two]
  simp only [numAtRisk, numAtRiskIn, riskSet_T₀_zero, riskSet_T₀_one, filter_g₀_univ,
    filter_g₀_one]
  norm_num

theorem sqrt_quarter : √(1 / 4 : ℝ) = 1 / 2 := by
  rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

example : logRankRejects T₀ δ₀ g₀ (1 / 2) := by
  rw [logRankRejects, observedMinusExpected_T₀, breslowInformation_T₀, sqrt_quarter]
  norm_num

example : ¬ logRankRejects T₀ δ₀ g₀ 2 := by
  rw [logRankRejects, observedMinusExpected_T₀, breslowInformation_T₀, sqrt_quarter]
  norm_num

/-! ### Non-vacuity: the hypotheses of the pointwise and band theorems are satisfiable

Under the standard normal on `ℝ`, the estimator `β + ω / √n` has `√n (est - β) = ω` for
`n ≥ 1`, so the process-limit hypothesis holds with limit `id`. -/

/-- A witness estimator: `β + ω / √n`. -/
noncomputable def estW (β : ℝ) (n : ℕ) (ω : ℝ) : ℝ := β + ω / √(n : ℝ)

theorem sqrt_mul_estW_sub {β : ℝ} {n : ℕ} (hn : 0 < n) (ω : ℝ) :
    √(n : ℝ) * (estW β n ω - β) = ω := by
  have h : √(n : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast hn)).ne'
  rw [estW, add_sub_cancel_left, mul_div_cancel₀ _ h]

theorem tendstoInDistribution_estW (β : ℝ) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) * (estW β n ω - β)) atTop id
      (fun _ ↦ gaussianReal 0 1) (gaussianReal 0 1) where
  forall_aemeasurable n := by unfold estW; fun_prop
  aemeasurable_limit := aemeasurable_id
  tendsto := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    apply Subtype.ext
    change (gaussianReal 0 1).map id = (gaussianReal 0 1).map _
    congr 1
    funext ω
    exact (sqrt_mul_estW_sub hn ω).symm

theorem sqrt_one_nnreal : √((1 : NNReal) : ℝ) = 1 := by simp

/-- The pointwise Wald coverage theorem applies to the witness: coverage of
`[estW - z / √n, estW + z / √n]` tends to the standard-normal mass of `[-z, z]`. -/
example (β z : ℝ) :
    Tendsto (fun n : ℕ ↦ (gaussianReal 0 1).real
        {ω | β ∈ waldInterval (estW β n ω) (1 / √(n : ℝ)) z}) atTop
      (𝓝 ((gaussianReal 0 1).real (Set.Icc (-z) z))) := by
  have hse : TendstoInMeasure (gaussianReal 0 1) (fun (_ : ℕ) (_ : ℝ) ↦ (1 : ℝ)) atTop
      (fun _ ↦ √((1 : NNReal) : ℝ)) := by
    rw [sqrt_one_nnreal]
    exact tendstoInMeasure_of_tendsto_ae (fun _ ↦ aestronglyMeasurable_const)
      (ae_of_all _ fun _ ↦ tendsto_const_nhds)
  exact tendsto_coverage_waldInterval one_ne_zero z (tendstoInDistribution_estW β) HasLaw.id hse
    (fun _ ↦ aemeasurable_const)

/-- The grid witness: both grid coordinates share the same Gaussian `ω`. -/
noncomputable def estGrid (A : Fin 2 → ℝ) (n : ℕ) (ω : ℝ) : Fin 2 → ℝ :=
  fun j ↦ A j + ω / √(n : ℝ)

theorem tendstoInDistribution_estGrid (A : Fin 2 → ℝ) :
    TendstoInDistribution (fun (n : ℕ) ω j ↦ √(n : ℝ) * (estGrid A n ω j - A j)) atTop
      (fun ω _ ↦ ω) (fun _ ↦ gaussianReal 0 1) (gaussianReal 0 1) where
  forall_aemeasurable n := by unfold estGrid; fun_prop
  aemeasurable_limit := by fun_prop
  tendsto := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    apply Subtype.ext
    change (gaussianReal 0 1).map _ = (gaussianReal 0 1).map _
    congr 1
    funext ω j
    have h : √(n : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast hn)).ne'
    simp only [estGrid, add_sub_cancel_left, mul_div_cancel₀ _ h]

/-- The simultaneous grid-band theorem applies to the witness. -/
example (A : Fin 2 → ℝ) (z : ℝ) :
    Tendsto (fun n : ℕ ↦ (gaussianReal 0 1).real
        {ω | A ∈ gridBand (estGrid A n ω) (fun _ ↦ 1 / √(n : ℝ)) z}) atTop
      (𝓝 ((gaussianReal 0 1).real {ω | ∀ _ : Fin 2, |ω| ≤ z * √((1 : NNReal) : ℝ)})) := by
  have hse : TendstoInMeasure (gaussianReal 0 1) (fun (_ : ℕ) (_ : ℝ) (_ : Fin 2) ↦ (1 : ℝ))
      atTop (fun _ _ ↦ √((1 : NNReal) : ℝ)) := by
    rw [sqrt_one_nnreal]
    exact tendstoInMeasure_of_tendsto_ae (fun _ ↦ aestronglyMeasurable_const)
      (ae_of_all _ fun _ ↦ tendsto_const_nhds)
  exact tendsto_coverage_gridBand (v := fun _ ↦ 1) (fun _ ↦ one_ne_zero) z
    (tendstoInDistribution_estGrid A) (fun _ ↦ HasLaw.id) hse (fun _ ↦ aemeasurable_const)

/-- Pointwise versus simultaneous: the band limit is bounded by the pointwise limit, and below
by Bonferroni with `card = 2`. -/
example (z : ℝ) :
    1 - 2 * (1 - (gaussianReal 0 1).real (Set.Icc (-z) z)) ≤
      (gaussianReal 0 1).real {ω : ℝ | ∀ _ : Fin 2, |ω| ≤ z * √((1 : NNReal) : ℝ)} ∧
    (gaussianReal 0 1).real {ω : ℝ | ∀ _ : Fin 2, |ω| ≤ z * √((1 : NNReal) : ℝ)} ≤
      (gaussianReal 0 1).real (Set.Icc (-z) z) := by
  refine ⟨?_, gridBand_limit_le_pointwise (Z := fun ω (_ : Fin 2) ↦ ω) (v := fun _ ↦ 1)
    (fun _ ↦ one_ne_zero) (fun _ ↦ HasLaw.id) z 0⟩
  have h := one_sub_card_mul_le_gridBand_limit (Z := fun ω (_ : Fin 2) ↦ ω) (v := fun _ ↦ 1)
    (fun _ ↦ one_ne_zero) (fun _ ↦ HasLaw.id) z
  simpa using h

#print axioms tendsto_measureReal_preimage_of_tendstoInDistribution
#print axioms gaussianReal_real_abs_le_mul_sqrt
#print axioms tendsto_measureReal_abs_le_mul
#print axioms tendsto_coverage_waldInterval
#print axioms tendsto_logRank_rejection
#print axioms tendsto_coverage_cox_waldInterval
#print axioms tendsto_coverage_gridBand
#print axioms gridBand_limit_le_pointwise
#print axioms one_sub_card_mul_le_gridBand_limit

end MathlibExtTest.Probability.Statistics.ProcessInference
