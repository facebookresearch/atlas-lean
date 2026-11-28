/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.MachineLearning.Bandit.CanonicalModel

/-!
# The regret decomposition for stochastic bandits

For a stochastic `k`-armed bandit `ν` with `k ≥ 1` arms and finite means, every policy `π` and
every horizon `n`, the regret is the sum over the arms of the suboptimality gap
`Δ_i = μ* - μ_i` times the expected pull count `𝔼[T_i(n)]` under the canonical bandit model:
`R_n = ∑_i Δ_i 𝔼[T_i(n)]` (`regret_eq_sum_sub_mul_integral_pullCount`).

## Main statements

* `sum_comp_fst_eq_sum_pullCount_mul`: in every history, the sum over the rounds of a quantity
  `f A_t` of the chosen arm is `∑_i T_i(n) f i`.
* `regret_eq_sum_sub_mul_integral_pullCount`: the regret decomposition.

## Proof outline

By `integral_reward`, the expected reward of round `t` is the expected mean `𝔼[μ_{A_t}]` of the
arm chosen in it, so `R_n = n μ* - 𝔼[∑_t μ_{A_t}]`. Grouping the rounds by the arm chosen gives
`∑_t μ_{A_t} = ∑_i μ_i T_i(n)` pathwise, and the pull counts sum to `n` (`sum_pullCount`), so
`n μ* = ∑_i μ* 𝔼[T_i(n)]`. Subtracting gives the decomposition.

## References

* T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Lemma 4.5.
-/

public section

open MeasureTheory Finset

namespace Cslib.MachineLearning.Bandit

variable {k : ℕ}

/- Grouping the rounds of a history by the arm chosen in them: the sum over the rounds of a
quantity `f A_t` of the chosen arm is the sum over the arms of `T_i(n) f i`. -/
theorem sum_comp_fst_eq_sum_pullCount_mul {n : ℕ} (f : Fin k → ℝ) (h : History k n) :
    ∑ t, f (h t).1 = ∑ i, (pullCount i h : ℝ) * f i := by
  rw [← sum_fiberwise univ (fun t ↦ (h t).1) (fun t ↦ f (h t).1)]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [sum_congr rfl fun t ht ↦ by rw [(mem_filter.1 ht).2], sum_const, nsmul_eq_mul, pullCount]

/- Under any finite measure on histories, the pull count of an arm is integrable: it is
measurable and bounded by the number of rounds. -/
private theorem integrable_pullCount {n : ℕ} (μ : Measure (History k n)) [IsFiniteMeasure μ]
    (i : Fin k) : Integrable (fun h ↦ (pullCount i h : ℝ)) μ :=
  (integrable_const (n : ℝ)).mono'
    ((measurable_of_countable Nat.cast).comp (measurable_pullCount i)).aestronglyMeasurable
    (ae_of_all _ fun h ↦ by simpa using pullCount_le i h)

variable (ν : StochasticBandit k) (π : Policy k)

/-- **Regret decomposition** (Lattimore and Szepesvári, Lemma 4.5). Let `ν = (P_1, …, P_k)` be
a stochastic bandit with `k ≥ 1` arms and finite means `μ_1, …, μ_k`, let `μ* = max_i μ_i` and
let `Δ_i = μ* - μ_i` be the suboptimality gap of arm `i`. For every policy `π` and every horizon
`n`, the regret is `R_n = ∑_i Δ_i 𝔼[T_i(n)]`, where `T_i(n)` is the number of rounds among the
first `n` in which arm `i` is chosen and the expectation is taken under the canonical bandit
model `ℙ_{ν,π}`. In Lean, the arm `i` is stored as `i - 1`. -/
theorem regret_eq_sum_sub_mul_integral_pullCount [NeZero k] (hν : ν.HasFiniteMeans) (n : ℕ) :
    regret ν π n =
      ∑ i, (ν.maxMean - ν.mean i) * ∫ h, (pullCount i h : ℝ) ∂canonicalLaw ν π n := by
  set P := canonicalLaw ν π n
  have hT : ∑ i, ∫ h, (pullCount i h : ℝ) ∂P = n := by
    rw [← integral_finsetSum _ fun i _ ↦ integrable_pullCount P i]
    simp_rw [← Nat.cast_sum, sum_pullCount]
    simp
  have hmeans : ∑ t, ∫ h, ν.mean (h t).1 ∂P = ∑ i, ν.mean i * ∫ h, (pullCount i h : ℝ) ∂P := by
    rw [← integral_finsetSum _ fun t _ ↦ integrable_mean_action ν P t]
    simp_rw [sum_comp_fst_eq_sum_pullCount_mul]
    rw [integral_finsetSum _ fun i _ ↦ (integrable_pullCount P i).mul_const _]
    simp_rw [integral_mul_const, mul_comm]
  rw [regret, integral_finsetSum _ fun t _ ↦ integrable_reward ν π hν t,
    sum_congr rfl fun t _ ↦ integral_reward ν π hν t, hmeans, ← hT, sum_mul, ← sum_sub_distrib]
  simp_rw [sub_mul, mul_comm]

end Cslib.MachineLearning.Bandit
