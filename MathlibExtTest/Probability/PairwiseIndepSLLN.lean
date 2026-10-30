/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.PairwiseIndepSLLN

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace MathlibExtTest.Probability.PairwiseIndepSLLN

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The constant family of whole-space events is pairwise independent:
`μ (univ ∩ univ) = 1 = μ univ * μ univ`. -/
theorem indepSet_univ_univ : Pairwise fun _ _ : ℕ => IndepSet (Set.univ : Set Ω) Set.univ μ := by
  intro _ _ _
  exact (indepSet_iff_measure_inter_eq_mul MeasurableSet.univ MeasurableSet.univ μ).mpr (by simp)

/-- The whole-space events have divergent total probability:
`∑' _n, μ univ = ∑' _n, 1 = ⊤`. -/
theorem tsum_univ_eq_top : ∑' _n : ℕ, μ (Set.univ : Set Ω) = ⊤ := by
  simp only [measure_univ]
  exact ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero

/-- The pairwise-independent strong law restates with the exact public signature. -/
example {A : ℕ → Set Ω} (hA_meas : ∀ n, MeasurableSet (A n))
    (hA_indep : Pairwise fun i j => IndepSet (A i) (A j) μ)
    (hA_sum : ∑' n, μ (A n) = ⊤) :
    ∀ᵐ ω ∂μ, Filter.Tendsto
      (fun n => (∑ i ∈ Finset.range n, (A i).indicator (1 : Ω → ℝ) ω) /
                (∑ i ∈ Finset.range n, (μ (A i)).toReal))
      Filter.atTop (nhds 1) :=
  pairwise_indep_slln hA_meas hA_indep hA_sum

/-- The strong law applied to the constant whole-space events: since `Sₙ = n`
and `E[Sₙ] = n`, the ratio `Sₙ / E[Sₙ]` tends a.s. to `1`. -/
example :
    ∀ᵐ ω ∂μ, Filter.Tendsto
      (fun n => (∑ _i ∈ Finset.range n, (Set.univ : Set Ω).indicator (1 : Ω → ℝ) ω) /
                (∑ _i ∈ Finset.range n, (μ (Set.univ : Set Ω)).toReal))
      Filter.atTop (nhds 1) :=
  pairwise_indep_slln (μ := μ) (fun _ => MeasurableSet.univ) (indepSet_univ_univ (μ := μ)) (tsum_univ_eq_top (μ := μ))

/-- For the whole-space events, the expectation of the partial sum is `n`. -/
example (n : ℕ) :
    ∫ ω, partialSumIndicators (fun _ => Set.univ : ℕ → Set Ω) n ω ∂μ = n := by
  rw [integral_partialSumIndicators _ (fun _ => MeasurableSet.univ)]
  simp

/-- For the whole-space events, the variance bound specializes to
`Var(Sₙ) ≤ n`. -/
example (n : ℕ) :
    variance (partialSumIndicators (fun _ => Set.univ : ℕ → Set Ω) n) μ ≤ n := by
  have hvar := variance_partialSumIndicators_le
    (fun _ => Set.univ : ℕ → Set Ω) (fun _ => MeasurableSet.univ) (indepSet_univ_univ (μ := μ)) n
  have hES : ∫ ω, partialSumIndicators (fun _ => Set.univ : ℕ → Set Ω) n ω ∂μ = n := by
    rw [integral_partialSumIndicators _ (fun _ => MeasurableSet.univ)]
    simp
  rwa [hES] at hvar

/-- For the whole-space events, the expectations tend to `∞`. -/
example :
    Filter.Tendsto (fun n => ∫ ω, partialSumIndicators (fun _ => Set.univ : ℕ → Set Ω) n ω ∂μ)
      Filter.atTop Filter.atTop := by
  have h := ES_tendsto_atTop (μ := μ) (fun _ => Set.univ : ℕ → Set Ω)
    (fun _ => MeasurableSet.univ) (tsum_univ_eq_top (μ := μ))
  have hES : ∀ n : ℕ,
      ∫ ω, partialSumIndicators (fun _ => Set.univ : ℕ → Set Ω) n ω ∂μ = n := by
    intro n
    rw [integral_partialSumIndicators _ (fun _ => MeasurableSet.univ)]
    simp
  simpa [hES] using h

-- `#print axioms` for the public declarations: only the standard triple.
#print axioms ProbabilityTheory.partialSumIndicators
#print axioms ProbabilityTheory.partialSumIndicators_eq
#print axioms ProbabilityTheory.comap_indicator_one_le_generateFrom
#print axioms ProbabilityTheory.indepFun_indicator_of_indepSet
#print axioms ProbabilityTheory.memLp_indicator_one
#print axioms ProbabilityTheory.indicator_one_sq
#print axioms ProbabilityTheory.variance_indicator_le
#print axioms ProbabilityTheory.integral_partialSumIndicators
#print axioms ProbabilityTheory.variance_partialSumIndicators_le
#print axioms ProbabilityTheory.ES_tendsto_atTop
#print axioms ProbabilityTheory.ES_mono
#print axioms ProbabilityTheory.ES_step_le_one
#print axioms ProbabilityTheory.sllnSubseq
#print axioms ProbabilityTheory.sllnSubseq_spec
#print axioms ProbabilityTheory.sllnSubseq_pos
#print axioms ProbabilityTheory.sllnSubseq_strictMono
#print axioms ProbabilityTheory.ES_sllnSubseq_pos
#print axioms ProbabilityTheory.memLp_partialSumIndicators
#print axioms ProbabilityTheory.ae_tendsto_of_ae_eventually_abs_sub_lt
#print axioms ProbabilityTheory.chebyshev_subseq_bound
#print axioms ProbabilityTheory.summable_chebyshev_subseq
#print axioms ProbabilityTheory.partialSumIndicators_mono
#print axioms ProbabilityTheory.partialSumIndicators_nonneg
#print axioms ProbabilityTheory.exists_bracket_of_strictMono
#print axioms ProbabilityTheory.ES_sllnSubseq_upper_bound
#print axioms ProbabilityTheory.ES_subseq_ratio_tendsto_one
#print axioms ProbabilityTheory.pairwise_indep_slln

end MathlibExtTest.Probability.PairwiseIndepSLLN
