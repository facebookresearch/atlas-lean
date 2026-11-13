/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.NonnegSLLN
public import MathlibExt.Probability.PairwiseIndepSLLN
public import MathlibExt.Probability.Distributions.PoissonKernel
public import Mathlib.Probability.Independence.InfinitePi

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace MathlibExtTest.Probability.NonnegSLLN

/-! ### Independent Poisson counts with different means -/

/-- Means alternating between `1` and `2`: the counts below are not identically distributed. -/
noncomputable def altMean (i : ℕ) : ℝ≥0 := 1 + ((i % 2 : ℕ) : ℝ≥0)

/-- The alternating means are bounded by `2`. -/
lemma altMean_le (i : ℕ) : (altMean i : ℝ) ≤ 2 := by
  have : i % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have : ((i % 2 : ℕ) : ℝ) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.1 this
  simp only [altMean, NNReal.coe_add, NNReal.coe_one, NNReal.coe_natCast]
  linarith

/-- The total alternating mean diverges (it is at least `n`). -/
lemma tendsto_sum_altMean :
    Tendsto (fun n => ∑ i ∈ Finset.range n, (altMean i : ℝ)) atTop atTop := by
  refine tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop
  calc (n : ℝ) = ∑ _i ∈ Finset.range n, (1 : ℝ) := by simp
    _ ≤ ∑ i ∈ Finset.range n, (altMean i : ℝ) := Finset.sum_le_sum fun i _ => by
        simp [altMean]

/-- The product space of independent counts `Yᵢ ∼ Po(mᵢ)` with the alternating means. -/
noncomputable abbrev altPoisson : Measure (ℕ → ℕ) :=
  Measure.infinitePi fun i : ℕ => poissonMeasure (altMean i)

/-- Each coordinate of `altPoisson` has mean `mᵢ`. -/
lemma integral_altPoisson (i : ℕ) : ∫ ω, (ω i : ℝ) ∂altPoisson = altMean i := by
  have hlaw : HasLaw (fun ω : ℕ → ℕ => ω i) (poissonMeasure (altMean i)) altPoisson :=
    ⟨(measurable_pi_apply i).aemeasurable, Measure.infinitePi_map_eval _ i⟩
  have hcast : Measurable (fun x : ℕ => (x : ℝ)) := Measurable.of_discrete
  rw [← integral_natCast_poissonMeasure]
  exact hlaw.integral_comp (f := fun n : ℕ => (n : ℝ)) hcast.aestronglyMeasurable

/-- **Strong law for independent Poisson counts with different means.** For independent
`Yᵢ ∼ Po(mᵢ)` with means alternating between `1` and `2`, `∑_{i<n} Yᵢ / ∑_{i<n} mᵢ → 1` almost
surely. The hypotheses hold with `B = 2` and `C = 1`, since `Var Yᵢ = mᵢ`. -/
theorem ae_tendsto_altPoisson :
    ∀ᵐ ω ∂altPoisson, Tendsto (fun n => (∑ i ∈ Finset.range n, (ω i : ℝ)) /
      ∑ i ∈ Finset.range n, (altMean i : ℝ)) atTop (𝓝 1) := by
  have hcast : Measurable (fun x : ℕ => (x : ℝ)) := Measurable.of_discrete
  have hlaw : ∀ i, HasLaw (fun ω : ℕ → ℕ => ω i) (poissonMeasure (altMean i)) altPoisson :=
    fun i => ⟨(measurable_pi_apply i).aemeasurable, Measure.infinitePi_map_eval _ i⟩
  have hind := iIndepFun_infinitePi (P := fun i : ℕ => poissonMeasure (altMean i))
    (X := fun _ => id) (fun _ => measurable_id)
  have hmem : ∀ r : ℝ≥0, MemLp (fun n : ℕ => (n : ℝ)) 2 (poissonMeasure r) := fun r =>
    (memLp_two_iff_integrable_sq hcast.aestronglyMeasurable).2
      (integrable_natCast_sq_poissonMeasure r)
  have hvar : ∀ i, Var[fun ω : ℕ → ℕ => (ω i : ℝ); altPoisson] = altMean i := fun i => by
    have h := variance_map (μ := altPoisson) (X := fun n : ℕ => (n : ℝ))
      (Y := fun ω : ℕ → ℕ => ω i) ((hlaw i).map_eq ▸ hcast.aemeasurable) (hlaw i).aemeasurable
    rw [(hlaw i).map_eq, variance_natCast_poissonMeasure] at h
    exact h.symm
  have h := ae_tendsto_sum_div_sum_integral (μ := altPoisson) (Y := fun i ω => (ω i : ℝ))
    (B := 2) (C := 1) (fun i => (hlaw i).memLp_comp (hmem _))
    (fun i => Eventually.of_forall fun ω => Nat.cast_nonneg _)
    (fun i j hij => (hind.indepFun hij).comp hcast hcast)
    (fun i => by rw [integral_altPoisson]; exact altMean_le i)
    (fun i => by rw [integral_altPoisson, hvar, one_mul])
    (by simpa only [integral_altPoisson] using tendsto_sum_altMean)
  simpa only [integral_altPoisson] using h

/-! ### The indicator law as the special case `B = C = 1` -/

/-- For pairwise independent events with divergent total probability, the ratio strong law with
`B = C = 1` (`Var 1_A ≤ P(A) ≤ 1`) gives the conclusion of
`ProbabilityTheory.pairwise_indep_slln`. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {A : ℕ → Set Ω} (hA : ∀ n, MeasurableSet (A n))
    (hindep : Pairwise fun i j => IndepSet (A i) (A j) μ) (hsum : ∑' n, μ (A n) = ⊤) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => (∑ i ∈ Finset.range n, (A i).indicator (1 : Ω → ℝ) ω) /
      ∑ i ∈ Finset.range n, (μ (A i)).toReal) atTop (𝓝 1) := by
  have hint : ∀ i, μ[(A i).indicator (1 : Ω → ℝ)] = (μ (A i)).toReal := fun i => by
    rw [integral_indicator_one (hA i), measureReal_def]
  have htop : Tendsto (fun n => ∑ i ∈ Finset.range n, (μ (A i)).toReal) atTop atTop := by
    simpa only [integral_partialSumIndicators A hA] using ES_tendsto_atTop A hA hsum
  have h := ae_tendsto_sum_div_sum_integral (μ := μ)
    (Y := fun i => (A i).indicator (1 : Ω → ℝ)) (B := 1) (C := 1)
    (fun i => memLp_indicator_one (hA i))
    (fun i => Eventually.of_forall fun ω => Set.indicator_nonneg (fun _ _ => zero_le_one) ω)
    (fun i j hij => indepFun_indicator_of_indepSet (hindep hij))
    (fun i => by
      rw [hint]
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one (ENNReal.ofReal_one ▸ prob_le_one))
    (fun i => by rw [hint, one_mul]; exact variance_indicator_le (hA i))
    (by simpa only [hint] using htop)
  simpa only [hint] using h

end MathlibExtTest.Probability.NonnegSLLN
