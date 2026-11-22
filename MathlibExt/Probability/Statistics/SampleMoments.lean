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
import MathlibExt.Probability.MonteCarloRate

/-!
# The unbiased sample variance and the sample mean

For `n ≥ 2` pairwise independent, identically distributed, square-integrable real observations
`X i`, `i : Fin n`, the unbiased sample variance
`FiniteProbability.sampleVarUnbiased (fun i => X i ω) = (n - 1)⁻¹ ∑ᵢ (Xᵢ - X̄)²` is integrable
and its mean is the common variance. Only pairwise independence is used: the proof's
independence step is `IndepFun.variance_sum`, which needs pairwise independence only.
This finite-family statement is the primary result; the
variance of the sample mean comes from `IndepFun.variance_sum`. For an i.i.d. sequence
`X 0, X 1, …` the same holds for the first `n` observations, stated for `sampleVarUnbiased` of
their restriction to `Fin n`. The sample mean `X̄` is unbiased for the constant mean family
(`isUnbiased_sampleMean_family`, with no independence hypothesis), and under iid its family
MSE is `Var (X 0) / n` (`familyMeanSquaredError_sampleMean_of_iid`).

## Main results

* `integral_sampleVariance_of_pairwise_iid_fin`: finite pairwise-independent, identically
  distributed family indexed by `Fin n`.
* `integral_sampleVariance_of_iid_fin`: finite i.i.d. family indexed by `Fin n`, a corollary
  (mutual independence implies pairwise independence).
* `integral_sampleVariance_of_iid`: the sequence form, a corollary.
* `isUnbiased_sampleMean_of_common_mean`: the sample mean is unbiased under per-observation
  integrability and a common mean.
* `isUnbiased_sampleMean_family`: the sample mean is unbiased for the constant mean family.
* `familyMeanSquaredError_sampleMean_of_iid`: the sample-mean family MSE under iid.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open MathlibExt.Probability.Statistics.EstimationRisk
open scoped BigOperators ENNReal

namespace MathlibExt.Probability

/-- **The sample variance of a finite pairwise-independent i.i.d. family is integrable
and unbiased.** For `n ≥ 2` pairwise independent, identically distributed, square-integrable
real observations `X i`, `i : Fin n`, with common law that of `X i0`, the sample variance
`s² = FiniteProbability.sampleVarUnbiased (fun i => X i ω) = (n - 1)⁻¹ ∑ᵢ (Xᵢ - X̄)²`,
`X̄ = n⁻¹ ∑ⱼ Xⱼ`, is integrable and `E s² = Var (X i0)`. Mutual independence is not needed:
the only independence step is the variance of the sum, which uses pairwise independence. -/
theorem integral_sampleVariance_of_pairwise_iid_fin
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 2 ≤ n) (X : Fin n → Ω → ℝ) (i0 : Fin n)
    (hIndep : Pairwise fun i j => X i ⟂ᵢ[μ] X j)
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
        (fun i _ j _ hij => hIndep hij)
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

/-- **The sample variance of a finite i.i.d. family is integrable and unbiased.** For
`n ≥ 2` mutually independent, identically distributed, square-integrable real observations
`X i`, `i : Fin n`, with common law that of `X i0`, the sample variance is integrable and
`E s² = Var (X i0)`. Derived from `integral_sampleVariance_of_pairwise_iid_fin`: mutual
independence implies pairwise independence. -/
theorem integral_sampleVariance_of_iid_fin
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 2 ≤ n) (X : Fin n → Ω → ℝ) (i0 : Fin n)
    (hIndep : iIndepFun X μ)
    (hIdent : ∀ i, IdentDistrib (X i) (X i0) μ μ)
    (hMemLp : MemLp (X i0) 2 μ) :
    Integrable (fun ω => FiniteProbability.sampleVarUnbiased (fun i => X i ω)) μ ∧
    ∫ ω, FiniteProbability.sampleVarUnbiased (fun i => X i ω) ∂μ = variance (X i0) μ :=
  integral_sampleVariance_of_pairwise_iid_fin hn X i0 (fun _ _ hij => hIndep.indepFun hij)
    hIdent hMemLp

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

/-- **Sample mean family unbiasedness under common means.** For `n > 0` integrable
observations with common mean `mu`, the canonical sample mean `X̄` is unbiased for the
constant mean family over `Unit`. Uses no independence and no identical distribution
(linearity of the integral (`integral_sample_mean`) only). -/
theorem isUnbiased_sampleMean_of_common_mean
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ)
    (hInt : ∀ i, Integrable (X i) μ)
    {mu : ℝ} (hMean : ∀ i, ∫ ω, X i ω ∂μ = mu)
    (n : ℕ) (hn : 0 < n) :
    MathlibExt.Probability.Statistics.EstimationRisk.IsUnbiased
      (fun ω => FiniteProbability.sampleMean (fun i : Fin n => X i ω))
      (fun _ : Unit => (⟨μ, inferInstance⟩ : ProbabilityMeasure Ω))
      (fun _ => mu) := by
  have hSM : (fun ω => FiniteProbability.sampleMean (fun i : Fin n => X i ω))
      = (fun ω => (∑ i ∈ Finset.range n, X i ω) / (n : ℝ)) := by
    funext ω
    rw [FiniteProbability.sampleMean_eq_sum_div, Fintype.card_fin,
      Fin.sum_univ_eq_sum_range (fun i => X i ω) n]
  rw [hSM]
  have _ : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hXb : Integrable (fun ω => (∑ i ∈ Finset.range n, X i ω) / (n : ℝ)) μ :=
    (integrable_finsetSum _ (fun i _ => hInt i)).div_const _
  have hmean : ∫ ω, (∑ i ∈ Finset.range n, X i ω) / (n : ℝ) ∂μ = mu := by
    have hgen := integral_sample_mean (ι := Fin n) (X := fun i : Fin n => X i.val)
      (mu := mu) (fun i => hInt i.val) (fun i => hMean i.val)
    rw [Fintype.card_fin] at hgen
    have hfun : (fun ω => (∑ i ∈ Finset.range n, X i ω) / (n : ℝ))
        = fun ω => (∑ i : Fin n, X i.val ω) / (n : ℝ) := by
      funext ω
      congr 1
      exact (Fin.sum_univ_eq_sum_range (fun i => X i ω) n).symm
    rw [hfun]
    exact hgen
  exact fun _ => ⟨hXb, hmean⟩

/-- **Sample mean family unbiasedness.** For square-integrable identically
distributed `X i` with `n > 0`, the canonical sample mean `X̄` is unbiased for the
constant mean family over `Unit`. Derived from `isUnbiased_sampleMean_of_common_mean`;
identical distribution supplies integrability and the common mean. -/
theorem isUnbiased_sampleMean_family
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ)
    (hIdent : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hMemLp : MemLp (X 0) 2 μ)
    (n : ℕ) (hn : 0 < n) :
    MathlibExt.Probability.Statistics.EstimationRisk.IsUnbiased
      (fun ω => FiniteProbability.sampleMean (fun i : Fin n => X i ω))
      (fun _ : Unit => (⟨μ, inferInstance⟩ : ProbabilityMeasure Ω))
      (fun _ => ∫ ω, X 0 ω ∂μ) := by
  have hMem : ∀ i, MemLp (X i) 2 μ := fun i => (hIdent i).memLp_iff.mpr hMemLp
  exact isUnbiased_sampleMean_of_common_mean X
    (fun i => (hMem i).integrable one_le_two)
    (fun i => (hIdent i).integral_eq) n hn

/-- **Sample mean family MSE under iid.** For square-integrable identically distributed
`X i` with `n > 0`, the family MSE of `X̄` about the constant mean family over `Unit`
equals `Var (X 0) / n`. Adds independence for the variance calculation
(via `variance_sample_mean_of_iid`); the squared-error integrability is constructed
internally from `hMemLp`, identical distribution, and finite summation. -/
theorem familyMeanSquaredError_sampleMean_of_iid
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ)
    (hIndep : iIndepFun X μ)
    (hIdent : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hMemLp : MemLp (X 0) 2 μ)
    (n : ℕ) (hn : 0 < n) :
    ∃ h2 : (∀ _ : Unit, Integrable
      (fun x => (FiniteProbability.sampleMean (fun i : Fin n => X i x)
        - ∫ ω, X 0 ω ∂μ) ^ 2) μ),
    MathlibExt.Probability.Statistics.EstimationRisk.familyMeanSquaredError
      (fun ω => FiniteProbability.sampleMean (fun i : Fin n => X i ω))
      (fun _ : Unit => (⟨μ, inferInstance⟩ : ProbabilityMeasure Ω))
      (fun _ => ∫ ω, X 0 ω ∂μ) h2
      = fun _ => variance (X 0) μ / (n : ℝ) := by
  have hSM : (fun ω => FiniteProbability.sampleMean (fun i : Fin n => X i ω))
      = (fun ω => (∑ i ∈ Finset.range n, X i ω) / (n : ℝ)) := by
    funext ω
    rw [FiniteProbability.sampleMean_eq_sum_div, Fintype.card_fin,
      Fin.sum_univ_eq_sum_range (fun i => X i ω) n]
  have hMem : ∀ i, MemLp (X i) 2 μ := fun i => (hIdent i).memLp_iff.mpr hMemLp
  have hsum : MemLp (fun ω => ∑ i ∈ Finset.range n, X i ω) 2 μ :=
    memLp_finsetSum (Finset.range n) (fun i _ => hMem i)
  have hfunsmul : (fun ω => (∑ i ∈ Finset.range n, X i ω) / (n : ℝ))
      = (n : ℝ)⁻¹ • (fun ω => ∑ i ∈ Finset.range n, X i ω) := by
    funext ω
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [div_eq_mul_inv, mul_comm]
  have hXb : MemLp (fun ω => (∑ i ∈ Finset.range n, X i ω) / (n : ℝ)) 2 μ := by
    rw [hfunsmul]
    exact hsum.const_smul _
  have hXbsub : MemLp (fun x => (∑ i ∈ Finset.range n, X i x) / (n : ℝ)
      - ∫ ω, X 0 ω ∂μ) 2 μ :=
    hXb.sub (memLp_const (∫ ω, X 0 ω ∂μ))
  have hunb := isUnbiased_sampleMean_family X hIdent hMemLp n hn
  have hXbc := hXb
  rw [← hSM] at hXbc
  have hXbsubc : MemLp (fun x => FiniteProbability.sampleMean (fun i : Fin n => X i x)
      - ∫ ω, X 0 ω ∂μ) 2 μ :=
    hXbc.sub (memLp_const (∫ ω, X 0 ω ∂μ))
  refine ⟨fun _ => hXbsubc.integrable_sq, ?_⟩
  funext θ
  have h := IsUnbiased.familyMeanSquaredError_eq_variance
    hunb (fun _ => hXbc) (fun _ => hXbsubc.integrable_sq) θ
  rw [h, hSM]
  exact variance_sample_mean_of_iid X hIndep hIdent hMemLp n hn.ne'

end MathlibExt.Probability
