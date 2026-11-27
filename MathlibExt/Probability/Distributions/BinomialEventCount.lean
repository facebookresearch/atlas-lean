/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Set.Card
public import Mathlib.Probability.Independence.Basic

import Mathlib.Probability.Distributions.Bernoulli
import MathlibExt.Probability.BernoulliSumPmf
import MathlibExt.Probability.Distributions.PoissonBinomial

/-!
# The number of independent events of equal probability that occur

If `E 0, …, E (n - 1)` are mutually independent events, each of probability `p`, then the number
`#{i | ω ∈ E i}` of events that occur has the binomial law with parameters `n` and `p`: it equals
`k` with probability `C(n, k) p ^ k (1 - p) ^ (n - k)`, and it is at least `k` with probability
`∑_{k ≤ j ≤ n} C(n, j) p ^ j (1 - p) ^ (n - j)`. This is the event form of the binomial law of a
sum of independent Bernoulli variables (`ProbabilityTheory.bernoulli_sum_pmf_iid`,
`ProbabilityTheory.measure_le_sum_eq_poissonBinomialTail`), applied to the indicators of the
events.

## Main results

* `ProbabilityTheory.iIndepSet.measureReal_ncard_eq`: the probability that exactly `k` of the
  events occur.
* `ProbabilityTheory.iIndepSet.measureReal_le_ncard`: the probability that at least `k` of the
  events occur.
-/

@[expose] public section

open MeasureTheory Finset

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n : ℕ} {E : Fin n → Set Ω}
  {p : ℝ}

/-- The number of events that occur at `ω` is the sum of their indicators at `ω`. -/
private lemma ncard_eq_sum_indicator (ω : Ω) :
    {i | ω ∈ E i}.ncard = ∑ i, (E i).indicator (1 : Ω → ℕ) ω := by
  classical
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred, card_filter]
  simp [Set.indicator_apply]

/-- The indicators of independent events of probability `p` are independent Bernoulli variables
with parameter `p`. -/
private lemma isBernoulliRV_indicator (hE : ∀ i, MeasurableSet (E i)) (h : iIndepSet E μ)
    (hp : ∀ i, μ.real (E i) = p) (i : Fin n) :
    IsBernoulliRV ((E i).indicator (1 : Ω → ℕ)) μ p := by
  have := h.isProbabilityMeasure
  rw [← hp i]
  exact ⟨by simp, hasLaw_indicator_one_bernoulliMeasure (hE i).nullMeasurableSet⟩

/-- **The number of independent events that occur is binomial.** Let $\mu$ be a probability
measure and let $E_0, \dots, E_{n-1}$ be mutually independent measurable events, each of
probability $p$. Then for every $k \in \mathbb{N}$ the probability that exactly $k$ of them occur
is

$$\mu\{\omega : \#\{i : \omega \in E_i\} = k\} = \binom{n}{k} p^k (1 - p)^{n - k},$$

where $\binom{n}{k} = 0$ for $k > n$ (and the exponent $n - k$ is truncated at $0$). -/
theorem iIndepSet.measureReal_ncard_eq (hE : ∀ i, MeasurableSet (E i)) (h : iIndepSet E μ)
    (hp : ∀ i, μ.real (E i) = p) (k : ℕ) :
    μ.real {ω | {i | ω ∈ E i}.ncard = k} = n.choose k * p ^ k * (1 - p) ^ (n - k) := by
  have := h.isProbabilityMeasure
  have hpmf := bernoulli_sum_pmf_iid (isBernoulliRV_indicator hE h hp) h.iIndepFun_indicator
    (fun i => measurable_const.indicator (hE i)) k
  rw [measureReal_def, ← hpmf]
  congr 2
  ext ω
  simp [ncard_eq_sum_indicator]

/-- **Upper tail of the number of independent events that occur.** Let $\mu$ be a probability
measure and let $E_0, \dots, E_{n-1}$ be mutually independent measurable events, each of
probability $p$. Then for every $k \in \mathbb{N}$ the probability that at least $k$ of them occur
is the binomial upper tail

$$\mu\{\omega : \#\{i : \omega \in E_i\} \ge k\} =
  \sum_{j = k}^{n} \binom{n}{j} p^j (1 - p)^{n - j},$$

an empty sum, equal to $0$, when $k > n$. -/
theorem iIndepSet.measureReal_le_ncard (hE : ∀ i, MeasurableSet (E i)) (h : iIndepSet E μ)
    (hp : ∀ i, μ.real (E i) = p) (k : ℕ) :
    μ.real {ω | k ≤ {i | ω ∈ E i}.ncard} =
      ∑ j ∈ Icc k n, (n.choose j : ℝ) * p ^ j * (1 - p) ^ (n - j) := by
  have := h.isProbabilityMeasure
  have htail := measure_le_sum_eq_poissonBinomialTail (isBernoulliRV_indicator hE h hp)
    h.iIndepFun_indicator (fun i => measurable_const.indicator (hE i)) k
  simp only [poissonBinomialTail, poissonBinomialPMF_const] at htail
  rw [measureReal_def, ← htail]
  simp [ncard_eq_sum_indicator]

end ProbabilityTheory
