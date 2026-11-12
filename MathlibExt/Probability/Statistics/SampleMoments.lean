/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Independence.Basic
public import MathlibExt.Probability.FiniteProbability
public import MathlibExt.Probability.Statistics.EstimationRisk

/-!
# The unbiased sample variance

For `n ≥ 2` independent, identically distributed, square-integrable real observations
`X i`, `i : Fin n`, the unbiased sample variance
`FiniteProbability.sampleVarUnbiased (fun i => X i ω) = (n - 1)⁻¹ ∑ᵢ (Xᵢ - X̄)²` is integrable
and its mean is the common variance. This finite-family statement is the primary result; the
variance of the sample mean comes from `IndepFun.variance_sum`. For an i.i.d. sequence
`X 0, X 1, …` the same holds for the first `n` observations, stated for `sampleVarUnbiased` of
their restriction to `Fin n`.

## Main results

* `integral_sampleVariance_of_iid_fin`: finite i.i.d. family indexed by `Fin n`.
* `integral_sampleVariance_of_iid`: the sequence form, a corollary.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open MathlibExt.Probability.Statistics.EstimationRisk
open scoped BigOperators ENNReal

namespace MathlibExt.Probability

/-- **The sample variance of a finite i.i.d. family is integrable and unbiased.** For
`n ≥ 2` independent, identically distributed, square-integrable real observations
`X i`, `i : Fin n`, with common law that of `X i0`, the sample variance
`s² = FiniteProbability.sampleVarUnbiased (fun i => X i ω) = (n - 1)⁻¹ ∑ᵢ (Xᵢ - X̄)²`,
`X̄ = n⁻¹ ∑ⱼ Xⱼ`, is integrable and `E s² = Var (X i0)`. -/
theorem integral_sampleVariance_of_iid_fin
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 2 ≤ n) (X : Fin n → Ω → ℝ) (i0 : Fin n)
    (hIndep : iIndepFun X μ)
    (hIdent : ∀ i, IdentDistrib (X i) (X i0) μ μ)
    (hMemLp : MemLp (X i0) 2 μ) :
    Integrable (fun ω => FiniteProbability.sampleVarUnbiased (fun i => X i ω)) μ ∧
    ∫ ω, FiniteProbability.sampleVarUnbiased (fun i => X i ω) ∂μ = variance (X i0) μ := by
  have hn0 : n ≠ 0 := by omega
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hMemLp' : ∀ i, MemLp (X i) 2 μ := fun i => (hIdent i).memLp_iff.mpr hMemLp
  have hfun : (fun ω => FiniteProbability.sampleVarUnbiased (fun i => X i ω))
      = fun ω => (∑ i, X i ω ^ 2 - n * ((∑ j, X j ω) / (n : ℝ)) ^ 2) / ((n : ℝ) - 1) := by
    funext ω
    rw [FiniteProbability.sampleVarUnbiased_eq_sum_div, FiniteProbability.sum_sq_sub_sampleMean,
      FiniteProbability.sampleMean_eq_sum_div, Fintype.card_fin]
  have hsq : ∀ i, Integrable (fun ω => X i ω ^ 2) μ := fun i => (hMemLp' i).integrable_sq
  have hSumSq : Integrable (fun ω => ∑ i, X i ω ^ 2) μ :=
    integrable_finsetSum _ (fun i _ => hsq i)
  have hMean : MemLp (fun ω => (∑ j, X j ω) / (n : ℝ)) 2 μ := by
    simp only [div_eq_inv_mul]
    exact (memLp_finsetSum _ (fun i _ => hMemLp' i)).const_mul _
  have hMeanSq : Integrable (fun ω => ((∑ j, X j ω) / (n : ℝ)) ^ 2) μ :=
    hMean.integrable_sq
  have hVarMean : variance (fun ω => (∑ j, X j ω) / (n : ℝ)) μ = variance (X i0) μ / n := by
    have hsum : variance (fun ω => ∑ j, X j ω) μ = ∑ j, variance (X j) μ := by
      have hf : (∑ j, X j) = fun ω => ∑ j, X j ω := funext fun ω => Finset.sum_apply _ _ _
      rw [← hf]
      exact IndepFun.variance_sum (fun i _ => hMemLp' i)
        (fun i _ j _ hij => hIndep.indepFun hij)
    have hshape : (fun ω => (∑ j, X j ω) / (n : ℝ)) = fun ω => (n : ℝ)⁻¹ * (∑ j, X j ω) := by
      funext ω; rw [div_eq_inv_mul]
    rw [hshape, variance_const_mul, hsum,
      Finset.sum_congr rfl (fun i _ => (hIdent i).variance_eq), Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  rw [hfun]
  refine ⟨(hSumSq.sub (hMeanSq.const_mul _)).div_const _, ?_⟩
  have hE2 : ∀ i, ∫ ω, X i ω ^ 2 ∂μ = ∫ ω, X i0 ω ^ 2 ∂μ := fun i =>
    ((hIdent i).comp (measurable_id.pow_const 2)).integral_eq
  have hSumSqInt : ∫ ω, ∑ i, X i ω ^ 2 ∂μ = n * ∫ ω, X i0 ω ^ 2 ∂μ := by
    rw [integral_finsetSum _ (fun i _ => hsq i), Finset.sum_congr rfl (fun i _ => hE2 i),
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hMeanInt : ∫ ω, (∑ j, X j ω) / (n : ℝ) ∂μ = ∫ ω, X i0 ω ∂μ := by
    rw [integral_div, integral_finsetSum _ (fun i _ => (hMemLp' i).integrable one_le_two),
      Finset.sum_congr rfl (fun i _ => (hIdent i).integral_eq), Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hMeanSqInt : ∫ ω, ((∑ j, X j ω) / (n : ℝ)) ^ 2 ∂μ
      = variance (X i0) μ / n + (∫ ω, X i0 ω ∂μ) ^ 2 := by
    have h := variance_eq_sub hMean
    simp only [Pi.pow_apply] at h
    rw [hMeanInt, hVarMean] at h
    linarith
  have hVar0 := variance_eq_sub hMemLp
  simp only [Pi.pow_apply] at hVar0
  rw [integral_div, integral_sub hSumSq (hMeanSq.const_mul _), integral_const_mul,
    hSumSqInt, hMeanSqInt, div_eq_iff hn1, hVar0]
  field_simp
  ring

/-- **Sequence form.** For an i.i.d. square-integrable sequence `X 0, X 1, …` and `n ≥ 2`, the
unbiased sample variance `FiniteProbability.sampleVarUnbiased` of the first `n` observations
(the restriction `fun i : Fin n => X i ω`) is integrable and unbiased for `Var (X 0)`.
Derived from `integral_sampleVariance_of_iid_fin` by restriction to `Fin n`. -/
theorem integral_sampleVariance_of_iid
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ)
    (hIndep : iIndepFun X μ)
    (hIdent : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hMemLp : MemLp (X 0) 2 μ)
    (n : ℕ) (hn : 2 ≤ n) :
    Integrable (fun ω => FiniteProbability.sampleVarUnbiased (fun i : Fin n => X i ω)) μ ∧
    ∫ ω, FiniteProbability.sampleVarUnbiased (fun i : Fin n => X i ω) ∂μ = variance (X 0) μ :=
  integral_sampleVariance_of_iid_fin hn (fun i : Fin n => X i) ⟨0, by omega⟩
    (hIndep.precomp Fin.val_injective) (fun i => hIdent i) hMemLp

/-- **Sample variance is unbiased for the variance family.** For an i.i.d. square-integrable
sequence and `n ≥ 2`, `s²` of the first `n` observations is unbiased for `Var (X 0)` in the
constant family over `Unit`. Proved by rewriting with `integral_sampleVariance_of_iid`. -/
theorem isUnbiased_sampleVariance_of_iid
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ)
    (hIndep : iIndepFun X μ)
    (hIdent : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hMemLp : MemLp (X 0) 2 μ)
    {n : ℕ} (hn : 2 ≤ n) :
    MathlibExt.Probability.Statistics.EstimationRisk.IsUnbiased
      (fun ω => FiniteProbability.sampleVarUnbiased (fun i : Fin n => X i ω))
      (fun _ : Unit => ⟨μ, inferInstance⟩) (fun _ => variance (X 0) μ) := by
  intro θ
  exact integral_sampleVariance_of_iid X hIndep hIdent hMemLp n hn

/-- **Family MSE of the sample variance is its variance.** At every parameter of the constant
family, via `IsUnbiased.familyMeanSquaredError_eq_variance`. -/
theorem familyMeanSquaredError_sampleVariance_of_iid
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ)
    (hIndep : iIndepFun X μ)
    (hIdent : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hMemLp : MemLp (X 0) 2 μ)
    {n : ℕ} (hn : 2 ≤ n)
    (hMem : ∀ _ : Unit, MemLp
      (fun ω => FiniteProbability.sampleVarUnbiased (fun i : Fin n => X i ω)) 2 μ)
    (h2 : ∀ _ : Unit, Integrable
      (fun x => (FiniteProbability.sampleVarUnbiased (fun i : Fin n => X i x)
        - variance (X 0) μ) ^ 2) μ) :
    MathlibExt.Probability.Statistics.EstimationRisk.familyMeanSquaredError
      (fun ω => FiniteProbability.sampleVarUnbiased (fun i : Fin n => X i ω))
      (fun _ : Unit => (⟨μ, inferInstance⟩ : ProbabilityMeasure Ω))
      (fun _ => variance (X 0) μ) h2
      = fun _ => variance
        (fun ω => FiniteProbability.sampleVarUnbiased (fun i : Fin n => X i ω)) μ := by
  funext θ
  exact IsUnbiased.familyMeanSquaredError_eq_variance
    (isUnbiased_sampleVariance_of_iid X hIndep hIdent hMemLp hn) hMem h2 θ

end MathlibExt.Probability
