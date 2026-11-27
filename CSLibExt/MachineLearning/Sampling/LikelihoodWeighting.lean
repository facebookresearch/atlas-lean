/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.CausalAdjustment
public import CSLibExt.MachineLearning.Sampling.MonteCarlo

/-!
# Likelihood weighting as importance sampling for Bayesian networks

Likelihood weighting estimates a posterior `P(· | X_E = e)` of a finite Bayesian network
`b : BayesNet α n` by forward sampling with the evidence nodes clamped and weighting each sample
by the likelihood of the evidence. The clamped network is `b.mutilateSet E e` (every evidence
node `k ∈ E` gets the point mass at `e k` and no parents); the weight of an assignment `x` is
`lwWeight b E x = ∏_{k ∈ E} p_k (x_k | x_{pa k})`. Likelihood weighting is importance sampling
with this proposal and this weight, applied through `Sampling.isEstimate`.

## Main definitions

* `BayesNet.lwWeight b E x`: the likelihood weight `∏_{k ∈ E} p_k (x_k | x_{pa k})`.
* `BayesNet.evidenceProb b E e`: `P(X_E = e) = ∑_{x, x_E = e} P(x)`.
* `BayesNet.posteriorMean b E e f`: `E[f | X_E = e] = (∑_{x_E = e} P(x) f(x)) / P(X_E = e)`.
* `BayesNet.jointMeasure b`: the joint as a finite measure, `∑_x P(x) δ_x`, the law of a forward
  sample.
* `BayesNet.lwEstimate b E f X m`: the likelihood-weighting average of `w f` over the first `m`
  samples, as `Sampling.isEstimate`; `BayesNet.lwSelfNormalized b E f X m`: the ratio of the
  estimates for `f` and for `1`.

## Main results

* `BayesNet.proposal_mul_lwWeight`: pointwise, proposal times weight is the joint restricted to
  the evidence, `q(x) w(x) = P(x) 1[x_E = e]`.
* `BayesNet.proposal_ne_zero_of_joint_ne_zero`: the proposal and the weight are nonzero at every
  positive-probability assignment that agrees with the evidence (support coverage).
* `BayesNet.sum_proposal_mul_lwWeight`: `E_q[w] = P(X_E = e)`;
  `BayesNet.sum_proposal_mul_lwWeight_mul`: `E_q[w f] = ∑_{x_E = e} P(x) f(x)`.
* `BayesNet.lwWeight_empty`, `BayesNet.joint_mutilateSet_empty`: without evidence the weight is
  `1` and the proposal is the joint.
* `BayesNet.integral_lwEstimate` (**unbiased numerator**): for samples with the proposal law, the
  unnormalized estimate from `m > 0` samples has expectation `∑_{x_E = e} P(x) f(x)`; for `f = 1`
  it is `P(X_E = e)`.
* `BayesNet.tendsto_lwEstimate` and `BayesNet.tendsto_lwSelfNormalized` (**consistency**): for
  pairwise independent samples, the unnormalized estimate converges almost surely, and when
  `P(X_E = e) ≠ 0` the self-normalized estimate converges almost surely to `E[f | X_E = e]`.
* `BayesNet.integral_lwSelfNormalized_one`: the self-normalized estimate from one sample has
  expectation `∑_x q(x) 1[w(x) ≠ 0] f(x)`, the proposal mean of `f` on positive weights, which is
  in general not the posterior mean: the finite-sample self-normalized estimator is not claimed
  to be unbiased.

## References

* R. Fung and K.-C. Chang, *Weighing and integrating evidence for stochastic simulation in
  Bayesian networks*, UAI 1989.
* R. D. Shachter and M. A. Peot, *Simulation approaches to general probabilistic inference on
  belief networks*, UAI 1989.
* S. Russell and P. Norvig, *Artificial Intelligence: A Modern Approach*, 4th ed., §13.4.2.
* D. Koller and N. Friedman, *Probabilistic Graphical Models*, MIT Press, 2009, §12.2.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.GraphicalModels

open Finset MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

variable {α : Type*}

namespace BayesNet

variable {n : ℕ} [Nonempty α] (b : BayesNet α n)

/-! ### Weights and the evidence-clamped proposal -/

/-- The **likelihood weight** of an assignment `x` for evidence nodes `E`: the product of the
tables of the evidence nodes at `x`, `∏_{k ∈ E} p_k (x_k | x_{pa k})`. On assignments that agree
with the evidence this is the likelihood of the evidence given the sampled non-evidence values. -/
noncomputable def lwWeight (E : Finset (Fin n)) (x : Fin n → α) : ℝ :=
  ∏ k ∈ E, (b.cpt k (b.paVal k x)).weights (x k)

omit [Nonempty α] in
theorem lwWeight_nonneg (E : Finset (Fin n)) (x : Fin n → α) : 0 ≤ b.lwWeight E x :=
  prod_nonneg fun k _ => (b.cpt k _).nonneg _

omit [Nonempty α] in
/-- Without evidence every weight is `1`. -/
@[simp]
theorem lwWeight_empty (x : Fin n → α) : b.lwWeight ∅ x = 1 :=
  prod_empty

/-- The probability of the evidence `X_E = e`. -/
noncomputable def evidenceProb [Fintype α] [DecidableEq α] (E : Finset (Fin n))
    (e : Fin n → α) : ℝ :=
  ∑ x with ∀ k ∈ E, x k = e k, b.joint x

/-- The posterior mean `E[f | X_E = e]` (with Lean's `x / 0 = 0` when `P(X_E = e) = 0`). -/
noncomputable def posteriorMean [Fintype α] [DecidableEq α] (E : Finset (Fin n))
    (e : Fin n → α) (f : (Fin n → α) → ℝ) : ℝ :=
  (∑ x with ∀ k ∈ E, x k = e k, b.joint x * f x) / b.evidenceProb E e

/-- **Proposal times weight is the joint restricted to the evidence**: for the evidence-clamped
network `b.mutilateSet E e`, `q(x) w(x) = P(x)` if `x` agrees with `e` on `E`, and `0` otherwise. -/
theorem proposal_mul_lwWeight [DecidableEq α] (E : Finset (Fin n)) (e x : Fin n → α) :
    (b.mutilateSet E e).joint x * b.lwWeight E x =
      if ∀ k ∈ E, x k = e k then b.joint x else 0 := by
  have hW : b.lwWeight E x =
      ∏ j, if j ∈ E then (b.cpt j (b.paVal j x)).weights (x j) else 1 := by
    rw [lwWeight, prod_ite_mem, univ_inter]
  rw [joint_mutilateSet, hW, ← prod_mul_distrib]
  split_ifs with hx
  · rw [joint_eq_prod]
    refine prod_congr rfl fun j _ => ?_
    by_cases hj : j ∈ E
    · simp only [hj, ↓reduceIte, hx j hj, one_mul]
      rfl
    · simp only [hj, ↓reduceIte, mul_one]
      rfl
  · obtain ⟨k, hk, hne⟩ : ∃ k ∈ E, x k ≠ e k := by simpa using hx
    exact prod_eq_zero (mem_univ k) (by simp [hk, hne])

/-- **The proposal covers the target**: an assignment that agrees with the evidence and has
positive probability has nonzero proposal probability and nonzero weight, so likelihood weighting
never meets the zero-proposal-support failure of importance sampling. -/
theorem proposal_ne_zero_of_joint_ne_zero {E : Finset (Fin n)}
    {e x : Fin n → α} (hx : ∀ k ∈ E, x k = e k) (hP : b.joint x ≠ 0) :
    (b.mutilateSet E e).joint x ≠ 0 ∧ b.lwWeight E x ≠ 0 := by
  classical
  have h := b.proposal_mul_lwWeight E e x
  rw [ite_eq_left hx] at h
  exact mul_ne_zero_iff.1 (h ▸ hP)

/-- **The weighted proposal sum is the evidence-restricted sum**:
`E_q[w f] = ∑_{x_E = e} P(x) f(x)`, the unnormalized numerator of the posterior mean. -/
theorem sum_proposal_mul_lwWeight_mul [Fintype α] [DecidableEq α] (E : Finset (Fin n))
    (e : Fin n → α) (f : (Fin n → α) → ℝ) :
    ∑ x, (b.mutilateSet E e).joint x * b.lwWeight E x * f x =
      ∑ x with ∀ k ∈ E, x k = e k, b.joint x * f x := by
  rw [sum_filter]
  refine sum_congr rfl fun x _ => ?_
  rw [proposal_mul_lwWeight]
  split_ifs <;> simp

/-- **The expected likelihood weight is the probability of the evidence**: `E_q[w] = P(X_E = e)`. -/
theorem sum_proposal_mul_lwWeight [Fintype α] [DecidableEq α] (E : Finset (Fin n))
    (e : Fin n → α) :
    ∑ x, (b.mutilateSet E e).joint x * b.lwWeight E x = b.evidenceProb E e := by
  simpa [evidenceProb] using b.sum_proposal_mul_lwWeight_mul E e fun _ => 1

/-- The ratio of the weighted proposal sums is the posterior mean. -/
theorem sum_proposal_lwWeight_div [Fintype α] [DecidableEq α] (E : Finset (Fin n))
    (e : Fin n → α) (f : (Fin n → α) → ℝ) :
    (∑ x, (b.mutilateSet E e).joint x * b.lwWeight E x * f x) /
        ∑ x, (b.mutilateSet E e).joint x * b.lwWeight E x = b.posteriorMean E e f := by
  rw [sum_proposal_mul_lwWeight_mul, sum_proposal_mul_lwWeight, posteriorMean]

theorem joint_nonneg (x : Fin n → α) : 0 ≤ b.joint x :=
  b.toChain.joint_nonneg n x

/-- Without evidence the evidence has probability `1`. -/
theorem evidenceProb_empty [Fintype α] [DecidableEq α] (e : Fin n → α) :
    b.evidenceProb ∅ e = 1 := by
  simp [evidenceProb, b.sum_joint]

/-! ### The sampling estimators -/

variable [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

/-- The joint of the network as a finite measure on assignments, `∑_x P(x) δ_x`: the law of one
forward sample. -/
noncomputable def jointMeasure : Measure (Fin n → α) :=
  ∑ x, ENNReal.ofReal (b.joint x) • Measure.dirac x

instance : IsProbabilityMeasure b.jointMeasure := by
  refine ⟨?_⟩
  rw [jointMeasure, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, Measure.dirac_apply, Set.indicator_of_mem, Set.mem_univ,
    smul_eq_mul, Pi.one_apply, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => b.joint_nonneg x), b.sum_joint,
    ENNReal.ofReal_one]

theorem integrable_jointMeasure (g : (Fin n → α) → ℝ) : Integrable g b.jointMeasure :=
  integrable_finsetSum_measure.2 fun _ _ =>
    Integrable.of_finite.smul_measure ENNReal.ofReal_ne_top

/-- Integrals against the joint measure are finite sums. -/
theorem integral_jointMeasure (g : (Fin n → α) → ℝ) :
    ∫ x, g x ∂b.jointMeasure = ∑ x, b.joint x * g x := by
  rw [jointMeasure, integral_finsetSum_measure fun _ _ =>
    Integrable.of_finite.smul_measure ENNReal.ofReal_ne_top]
  refine sum_congr rfl fun x _ => ?_
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (b.joint_nonneg x),
    smul_eq_mul]

/-- The expected weighted integrand under the evidence-clamped proposal. -/
theorem integral_proposal_lwWeight_mul [DecidableEq α] (E : Finset (Fin n)) (e : Fin n → α)
    (f : (Fin n → α) → ℝ) :
    ∫ x, b.lwWeight E x * f x ∂(b.mutilateSet E e).jointMeasure =
      ∑ x with ∀ k ∈ E, x k = e k, b.joint x * f x := by
  rw [integral_jointMeasure, ← b.sum_proposal_mul_lwWeight_mul E e f]
  simp only [mul_assoc]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The **likelihood-weighting estimate** from the first `m` samples `X 0, …, X (m - 1)`: the
importance-sampling average of `w(X i) f(X i)` with the likelihood weight `w`. -/
noncomputable def lwEstimate (E : Finset (Fin n)) (f : (Fin n → α) → ℝ)
    (X : ℕ → Ω → Fin n → α) (m : ℕ) (ω : Ω) : ℝ :=
  Sampling.isEstimate (fun x => ENNReal.ofReal (b.lwWeight E x)) f X m ω

/-- The **self-normalized likelihood-weighting estimate**: the ratio of the estimates for `f` and
for the constant `1`, `∑ w(X i) f(X i) / ∑ w(X i)`. -/
noncomputable def lwSelfNormalized (E : Finset (Fin n)) (f : (Fin n → α) → ℝ)
    (X : ℕ → Ω → Fin n → α) (m : ℕ) (ω : Ω) : ℝ :=
  b.lwEstimate E f X m ω / b.lwEstimate E (fun _ => 1) X m ω

omit [Nonempty α] [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [MeasurableSpace Ω] in
theorem lwEstimate_eq_mcEstimate (E : Finset (Fin n)) (f : (Fin n → α) → ℝ)
    (X : ℕ → Ω → Fin n → α) (m : ℕ) (ω : Ω) :
    b.lwEstimate E f X m ω = Sampling.mcEstimate (fun x => b.lwWeight E x * f x) X m ω := by
  simp only [lwEstimate, Sampling.isEstimate, Sampling.mcEstimate]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  rw [ENNReal.toReal_ofReal (b.lwWeight_nonneg E _)]

/-- **The likelihood-weighting numerator is unbiased**: for samples whose law is the
evidence-clamped proposal, the estimate from `m > 0` samples has expectation
`∑_{x_E = e} P(x) f(x)`. -/
theorem integral_lwEstimate [DecidableEq α] (E : Finset (Fin n)) (e : Fin n → α)
    (f : (Fin n → α) → ℝ) {X : ℕ → Ω → Fin n → α} (hX : ∀ i, Measurable (X i))
    (hlaw : ∀ i, μ.map (X i) = (b.mutilateSet E e).jointMeasure) {m : ℕ} (hm : m ≠ 0) :
    ∫ ω, b.lwEstimate E f X m ω ∂μ = ∑ x with ∀ k ∈ E, x k = e k, b.joint x * f x := by
  simp only [lwEstimate_eq_mcEstimate]
  rw [Sampling.integral_mcEstimate (measurable_of_finite _) (integrable_jointMeasure _ _) hX hlaw
    hm, integral_proposal_lwWeight_mul]

/-- **The expected likelihood-weighting estimate of `1` is the probability of the evidence**. -/
theorem integral_lwEstimate_one [DecidableEq α] (E : Finset (Fin n)) (e : Fin n → α)
    {X : ℕ → Ω → Fin n → α} (hX : ∀ i, Measurable (X i))
    (hlaw : ∀ i, μ.map (X i) = (b.mutilateSet E e).jointMeasure) {m : ℕ} (hm : m ≠ 0) :
    ∫ ω, b.lwEstimate E (fun _ => 1) X m ω ∂μ = b.evidenceProb E e := by
  rw [b.integral_lwEstimate E e _ hX hlaw hm]
  simp [evidenceProb]

/-- **The likelihood-weighting numerator is consistent**: for pairwise independent samples with
the proposal law, the estimate converges almost surely to `∑_{x_E = e} P(x) f(x)`. -/
theorem tendsto_lwEstimate [DecidableEq α] (E : Finset (Fin n)) (e : Fin n → α)
    (f : (Fin n → α) → ℝ) {X : ℕ → Ω → Fin n → α} (hX : ∀ i, Measurable (X i))
    (hlaw : ∀ i, μ.map (X i) = (b.mutilateSet E e).jointMeasure)
    (hindep : Pairwise fun i j ↦ IndepFun (X i) (X j) μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun m ↦ b.lwEstimate E f X m ω) atTop
      (𝓝 (∑ x with ∀ k ∈ E, x k = e k, b.joint x * f x)) := by
  filter_upwards [Sampling.tendsto_mcEstimate (measurable_of_finite _)
    ((b.mutilateSet E e).integrable_jointMeasure (fun x => b.lwWeight E x * f x)) hX hlaw
    hindep] with ω hω
  rw [← b.integral_proposal_lwWeight_mul E e f]
  simpa only [lwEstimate_eq_mcEstimate] using hω

/-- **Self-normalized likelihood weighting is consistent**: for pairwise independent samples with
the proposal law and evidence of positive probability, the self-normalized estimate converges
almost surely to the posterior mean `E[f | X_E = e]`. -/
theorem tendsto_lwSelfNormalized [DecidableEq α] (E : Finset (Fin n)) (e : Fin n → α)
    (f : (Fin n → α) → ℝ) {X : ℕ → Ω → Fin n → α} (hX : ∀ i, Measurable (X i))
    (hlaw : ∀ i, μ.map (X i) = (b.mutilateSet E e).jointMeasure)
    (hindep : Pairwise fun i j ↦ IndepFun (X i) (X j) μ) (he : b.evidenceProb E e ≠ 0) :
    ∀ᵐ ω ∂μ, Tendsto (fun m ↦ b.lwSelfNormalized E f X m ω) atTop
      (𝓝 (b.posteriorMean E e f)) := by
  filter_upwards [b.tendsto_lwEstimate E e f hX hlaw hindep,
    b.tendsto_lwEstimate E e (fun _ => 1) hX hlaw hindep] with ω h1 h2
  simp only [mul_one] at h2
  exact h1.div h2 he

/-- **One-sample self-normalized likelihood weighting**: its expectation is the proposal mean of
`f` over assignments of positive weight, `∑_x q(x) 1[w(x) ≠ 0] f(x)`. This is in general not the
posterior mean (see the tests), so the finite-sample self-normalized estimator is biased. -/
theorem integral_lwSelfNormalized_one (E : Finset (Fin n)) (e : Fin n → α)
    (f : (Fin n → α) → ℝ) {X : ℕ → Ω → Fin n → α} (hX : ∀ i, Measurable (X i))
    (hlaw : ∀ i, μ.map (X i) = (b.mutilateSet E e).jointMeasure) :
    ∫ ω, b.lwSelfNormalized E f X 1 ω ∂μ =
      ∑ x, (b.mutilateSet E e).joint x * (if b.lwWeight E x = 0 then 0 else f x) := by
  have hpt : ∀ ω, b.lwSelfNormalized E f X 1 ω =
      (fun x => if b.lwWeight E x = 0 then 0 else f x) (X 0 ω) := by
    intro ω
    simp only [lwSelfNormalized, lwEstimate_eq_mcEstimate, Sampling.mcEstimate, range_one,
      sum_singleton, Nat.cast_one, inv_one, one_mul, mul_one]
    split_ifs with h
    · simp [h]
    · exact mul_div_cancel_left₀ _ h
  calc ∫ ω, b.lwSelfNormalized E f X 1 ω ∂μ
      = ∫ ω, (fun x => if b.lwWeight E x = 0 then 0 else f x) (X 0 ω) ∂μ :=
        integral_congr_ae (ae_of_all _ hpt)
    _ = ∫ x, (fun x => if b.lwWeight E x = 0 then 0 else f x) x ∂(μ.map (X 0)) :=
        (integral_map (f := fun x => if b.lwWeight E x = 0 then 0 else f x) (hX 0).aemeasurable
          (measurable_of_finite _).aestronglyMeasurable).symm
    _ = _ := by rw [hlaw 0, integral_jointMeasure]

end BayesNet

end Cslib.MachineLearning.GraphicalModels
