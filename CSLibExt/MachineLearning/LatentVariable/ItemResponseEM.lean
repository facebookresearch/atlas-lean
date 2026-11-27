/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.LatentVariable.BernoulliMixture
public import CSLibExt.MachineLearning.LatentVariable.ExpectationMaximization
public import MathlibExt.Probability.Statistics.Measurement.ItemResponse
public import CSLibExt.MachineLearning.Bayesian.Basic
public import MathlibExt.Probability.Statistics.Measurement.ProductMoments

import MathlibExt.Probability.FiniteProbability

/-!
# Item-response expectation maximization correspondence

The finite item law, the named expectation-maximization joint, and its
responsibilities agree: the locally independent item law read as a real
number is the product-Bernoulli mass, the joint is normalized over all
patterns and latent states, and responsibilities are the canonical
posterior singleton masses.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace Cslib.MachineLearning.LatentVariable.ItemResponseEM

open MeasureTheory ProbabilityTheory
open Cslib.MachineLearning.LatentVariable.BernoulliMixture
open MathlibExt.Probability.Statistics.Measurement

/-- Real reading of the locally independent law is the product-Bernoulli mass. -/
theorem localIndepPMF_toReal {d : ℕ} (q : Fin d → ℝ)
    (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∀ j, q j ≤ 1) (x : Fin d → Bool) :
    (localIndepPMF q hq0 hq1 x).toReal = bernPMF q x := by
  rw [localIndepPMF_toReal_apply]
  unfold bernPMF
  apply Finset.prod_congr rfl
  intro i _
  by_cases h : x i = true <;> simp [h]

/-- The EM joint normalizes over patterns and latent states. -/
theorem joint_sum_one {d K : ℕ} (θ : ValidParams d K) :
    ∑ y : Fin d → Bool, ∑ k' : Fin K, joint θ y k' = 1 := by
  have hB : ∀ k' : Fin K, ∑ y : Fin d → Bool, bernPMF (θ.1.prob k') y = 1 := by
    intro k'
    have h := MathlibExt.Probability.FiniteProbability.sum_toReal_eq_one
      (localIndepPMF (θ.1.prob k') (fun j => (θ.2.prob_pos k' j).le)
        (fun j => (θ.2.prob_lt_one k' j).le))
    simpa only [localIndepPMF_toReal] using h
  show (∑ y : Fin d → Bool, ∑ k' : Fin K, θ.1.weight k' * bernPMF (θ.1.prob k') y) = 1
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hB, mul_one]
  exact θ.2.weight_sum

private theorem localIndepPMF_ne_top {d : ℕ} (q : Fin d → ℝ)
    (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∀ j, q j ≤ 1) (x : Fin d → Bool) :
    localIndepPMF q hq0 hq1 x ≠ ⊤ := by
  rw [localIndepPMF_apply]
  have hle : (∏ i, (if x i then ENNReal.ofReal (q i) else ENNReal.ofReal (1 - q i))) ≤ 1 := by
    apply Finset.prod_le_one
    intro i _
    split
    · calc ENNReal.ofReal (q i) ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal (hq1 i)
        _ = 1 := ENNReal.ofReal_one
    · have h2 : 1 - q i ≤ 1 := by linarith [hq0 i]
      calc ENNReal.ofReal (1 - q i) ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal h2
        _ = 1 := ENNReal.ofReal_one
  exact ne_top_of_le_ne_top ENNReal.one_ne_top hle
private theorem localIndepPMF_ne_zero {d : ℕ} (q : Fin d → ℝ)
    (hq0 : ∀ j, 0 < q j) (hq1 : ∀ j, q j < 1) (x : Fin d → Bool) :
    localIndepPMF q (fun j => (hq0 j).le) (fun j => (hq1 j).le) x ≠ 0 := by
  rw [localIndepPMF_apply, Finset.prod_ne_zero_iff]
  intro i _
  split
  · exact ne_of_gt (ENNReal.ofReal_pos.mpr (hq0 i))
  · exact ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr (hq1 i)))

/-- The EM marginal evidence is positive. -/
private theorem marginal_joint_pos {d K : ℕ} [Nonempty (Fin K)] (θ : ValidParams d K)
    (x : Fin d → Bool) :
    0 < Cslib.MachineLearning.LatentVariable.ExpectationMaximization.marginal joint θ x := by
  show 0 < ∑ k', joint θ x k'
  apply Finset.sum_pos
  · intro k _
    exact joint_pos θ x k
  · exact Finset.univ_nonempty

/-- The finite item law, the named expectation-maximization joint, and the
responsibilities agree.

For valid mixture parameters `θ`, an observation pattern `x`, and a latent
state `k`, all three of the following hold.

1. The locally independent item-response mass of `x` at the `k`-th
   component probabilities, read as a real number, is the product-Bernoulli
   mass `bernPMF` at those probabilities.
2. The named joint `joint θ`, summed over all observation patterns and all
   latent states, is `1`. This is summation over the full outcome space;
   it is not a sum over a data list.
3. Let `κ` be a Markov kernel from latent states to observation patterns
   and `μ` a finite measure on latent states whose singleton masses and
   singleton likelihoods are exactly the mixture weights and the locally
   independent item law. Then the responsibility `resp θ x k` is
   the real reading of the canonical posterior mass `(κ†μ) x {k}`, the
   mass described by the copied posterior singleton formula. The evidence
   `(κ ∘ₘ μ) {x}` is positive (nonzero in `ℝ≥0∞`), since the mixture
   weights and likelihoods are all positive.

The hypotheses on `κ` and `μ` are pointwise singleton identities, stated
for the fixed observation `x` in the third part; the kernel and measure
themselves are not redefined here. -/
theorem law_objective_posterior_match {d K : ℕ}
    (θ : ValidParams d K) (x : Fin d → Bool) (k : Fin K)
    (κ : Kernel (Fin K) (Fin d → Bool)) [IsMarkovKernel κ]
    (μ : Measure (Fin K)) [IsFiniteMeasure μ]
    (hμ : ∀ k', μ {k'} = ENNReal.ofReal (θ.1.weight k'))
    (hκ : ∀ k', κ k' {x} =
      localIndepPMF (θ.1.prob k') (fun j => (θ.2.prob_pos k' j).le)
        (fun j => (θ.2.prob_lt_one k' j).le) x) :
    letI : Nonempty (Fin K) := ⟨k⟩;
    ((localIndepPMF (θ.1.prob k) (fun j => (θ.2.prob_pos k j).le)
        (fun j => (θ.2.prob_lt_one k j).le) x).toReal
      = bernPMF (θ.1.prob k) x)
    ∧ (∑ y : Fin d → Bool, ∑ k' : Fin K, joint θ y k' = 1)
    ∧ (resp θ x k = ((κ†μ) x {k}).toReal) := by
  have : Nonempty (Fin K) := ⟨k⟩
  refine ⟨?_, ?_, ?_⟩
  · exact localIndepPMF_toReal _ (fun j => (θ.2.prob_pos k j).le)
      (fun j => (θ.2.prob_lt_one k j).le) x
  · exact joint_sum_one θ
  · have hB1 : ∀ k' : Fin K, (localIndepPMF (θ.1.prob k')
          (fun j => (θ.2.prob_pos k' j).le) (fun j => (θ.2.prob_lt_one k' j).le) x).toReal
          = bernPMF (θ.1.prob k') x :=
      fun k' => localIndepPMF_toReal _ (fun j => (θ.2.prob_pos k' j).le)
        (fun j => (θ.2.prob_lt_one k' j).le) x
    have hLtop : ∀ k' : Fin K, localIndepPMF (θ.1.prob k')
          (fun j => (θ.2.prob_pos k' j).le) (fun j => (θ.2.prob_lt_one k' j).le) x ≠ ⊤ :=
      fun k' => localIndepPMF_ne_top _ (fun j => (θ.2.prob_pos k' j).le)
        (fun j => (θ.2.prob_lt_one k' j).le) x
    have hLreal : ∀ k' : Fin K, localIndepPMF (θ.1.prob k')
          (fun j => (θ.2.prob_pos k' j).le) (fun j => (θ.2.prob_lt_one k' j).le) x
          = ENNReal.ofReal (bernPMF (θ.1.prob k') x) := by
      intro k'
      have h2 := ENNReal.ofReal_toReal (hLtop k')
      rw [hB1 k'] at h2
      exact h2.symm
    have hden : (∑' k' : Fin K, ENNReal.ofReal (θ.1.weight k') * localIndepPMF (θ.1.prob k')
            (fun j => (θ.2.prob_pos k' j).le) (fun j => (θ.2.prob_lt_one k' j).le) x)
          = ENNReal.ofReal
            (Cslib.MachineLearning.LatentVariable.ExpectationMaximization.marginal joint θ x) := by
      have hsum : ∀ k' : Fin K, ENNReal.ofReal (θ.1.weight k') * localIndepPMF (θ.1.prob k')
            (fun j => (θ.2.prob_pos k' j).le) (fun j => (θ.2.prob_lt_one k' j).le) x
            = ENNReal.ofReal (joint θ x k') := by
        intro k'
        rw [hLreal k', ← ENNReal.ofReal_mul (θ.2.weight_pos k').le]
        have hj : joint θ x k' = θ.1.weight k' * bernPMF (θ.1.prob k') x := rfl
        rw [hj]
      first | rw [tsum_fintype]
      rw [Finset.sum_congr rfl (fun k' _ => hsum k'),
        ← ENNReal.ofReal_sum_of_nonneg (fun k' _ => (joint_pos θ x k').le)]
      have hmarg : (∑ k' : Fin K, joint θ x k')
            = Cslib.MachineLearning.LatentVariable.ExpectationMaximization.marginal joint θ x := rfl
      rw [hmarg]
    have hev : (κ ∘ₘ μ) {x} ≠ 0 := by
      have hev_eq := Cslib.MachineLearning.Bayesian.comp_apply_singleton_eq_tsum κ μ x
      rw [hev_eq]
      simp_rw [hμ, hκ]
      rw [hden]
      exact ne_of_gt (ENNReal.ofReal_pos.mpr (marginal_joint_pos θ x))
    have hpost : ((κ†μ) x {k})
          = μ {k} * κ k {x} / ∑' k', μ {k'} * κ k' {x} := by
      have heq := Cslib.MachineLearning.Bayesian.posterior_eq_bayesPosterior κ μ hev
      rw [heq]
      exact Cslib.MachineLearning.Bayesian.bayesPosterior_apply_singleton κ μ x k
    simp_rw [hμ, hκ] at hpost
    have hnum : ENNReal.ofReal (θ.1.weight k) * localIndepPMF (θ.1.prob k)
          (fun j => (θ.2.prob_pos k j).le) (fun j => (θ.2.prob_lt_one k j).le) x
          = ENNReal.ofReal (joint θ x k) := by
      rw [hLreal k, ← ENNReal.ofReal_mul (θ.2.weight_pos k).le]
      have hj : joint θ x k = θ.1.weight k * bernPMF (θ.1.prob k) x := rfl
      rw [hj]
    have hjpos := joint_pos θ x k
    have hjnn := hjpos.le
    have hmpos : 0 < Cslib.MachineLearning.LatentVariable.ExpectationMaximization.marginal
        joint θ x :=
      marginal_joint_pos θ x
    have hmnn := hmpos.le
    rw [hpost, hnum, hden, ENNReal.toReal_div, ENNReal.toReal_ofReal hjnn,
      ENNReal.toReal_ofReal hmnn]
    have hr : resp θ x k = joint θ x k
        / Cslib.MachineLearning.LatentVariable.ExpectationMaximization.marginal joint θ x := rfl
    rw [hr]

end Cslib.MachineLearning.LatentVariable.ItemResponseEM
