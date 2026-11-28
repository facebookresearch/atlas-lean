/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Set.Card
public import Mathlib.Probability.Distributions.Binomial
public import Mathlib.Probability.Independence.Basic
public import MathlibExt.Probability.Distributions.BinomialTail

import Mathlib.Probability.Distributions.Bernoulli
import MathlibExt.Probability.BernoulliSumPmf
import MathlibExt.Probability.Distributions.PoissonBinomial

/-!
# The number of independent events of equal probability that occur

If `E 0, …, E (n - 1)` are mutually independent events, each of probability `p`, then the number
`#{i | ω ∈ E i}` of events that occur has the binomial law `binomial n p` with parameters `n` and
`p`: it equals `k` with probability `C(n, k) p ^ k (1 - p) ^ (n - k)`, and it is at least `k` with
probability `binomTail n k p = ∑_{k ≤ j ≤ n} C(n, j) p ^ j (1 - p) ^ (n - j)`. The mass function
and the tail are the event form of the binomial law of a sum of independent Bernoulli variables
(`ProbabilityTheory.bernoulli_sum_pmf_iid`,
`ProbabilityTheory.measure_le_sum_eq_poissonBinomialTail`), applied to the indicators of the
events; they hold for every real `p` (which is in `[0, 1]` as soon as `n > 0`). The law follows
from the mass function, for `p` in the unit interval.

## Main results

* `ProbabilityTheory.iIndepSet.measureReal_ncard_eq`: the probability that exactly `k` of the
  events occur.
* `ProbabilityTheory.iIndepSet.hasLaw_ncard_binomial`: the number of events that occur has the
  law `binomial n p`, so Mathlib's binomial API applies to it.
* `ProbabilityTheory.iIndepSet.measureReal_le_ncard`: the probability that at least `k` of the
  events occur, the binomial upper tail `ProbabilityTheory.binomTail`.
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

/-- **Mass function of the number of independent events that occur.** Let $\mu$ be a probability
measure and let $E_0, \dots, E_{n-1}$ be mutually independent measurable events, each of
probability $p$. Then for every $k \in \mathbb{N}$ the probability that exactly $k$ of them occur
is the binomial mass

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

/-- **The number of independent events that occur has the binomial law.** Let $\mu$ be a
probability measure, let $p \in [0, 1]$, and let $E_0, \dots, E_{n-1}$ be mutually independent
measurable events, each of probability $p$. Then the number
$\omega \mapsto \#\{i : \omega \in E_i\}$ of events that occur has the binomial law
$\operatorname{Bin}(n, p)$ (`ProbabilityTheory.binomial n p`). -/
theorem iIndepSet.hasLaw_ncard_binomial {q : unitInterval} (hE : ∀ i, MeasurableSet (E i))
    (h : iIndepSet E μ) (hq : ∀ i, μ.real (E i) = q) :
    HasLaw (fun ω => {i | ω ∈ E i}.ncard) (binomial n q) μ := by
  have := h.isProbabilityMeasure
  have hmeas : Measurable fun ω => {i | ω ∈ E i}.ncard := by
    rw [funext ncard_eq_sum_indicator]
    exact Finset.measurable_sum _ fun i _ => measurable_const.indicator (hE i)
  refine ⟨hmeas.aemeasurable, Measure.ext_of_singleton fun k => ?_⟩
  rw [Measure.map_apply hmeas (measurableSet_singleton k), binomial_singleton,
    ← h.measureReal_ncard_eq hE hq k, ofReal_measureReal]
  rfl

/-- **Upper tail of the number of independent events that occur.** Let $\mu$ be a probability
measure and let $E_0, \dots, E_{n-1}$ be mutually independent measurable events, each of
probability $p$. Then for every $k \in \mathbb{N}$ the probability that at least $k$ of them occur
is the binomial upper tail `binomTail n k p`,

$$\mu\{\omega : \#\{i : \omega \in E_i\} \ge k\} =
  \sum_{j = k}^{n} \binom{n}{j} p^j (1 - p)^{n - j},$$

an empty sum, equal to $0$, when $k > n$. -/
theorem iIndepSet.measureReal_le_ncard (hE : ∀ i, MeasurableSet (E i)) (h : iIndepSet E μ)
    (hp : ∀ i, μ.real (E i) = p) (k : ℕ) :
    μ.real {ω | k ≤ {i | ω ∈ E i}.ncard} = binomTail n k p := by
  have := h.isProbabilityMeasure
  have htail := measure_le_sum_eq_poissonBinomialTail (isBernoulliRV_indicator hE h hp)
    h.iIndepFun_indicator (fun i => measurable_const.indicator (hE i)) k
  simp only [poissonBinomialTail, poissonBinomialPMF_const] at htail
  rw [binomTail, measureReal_def, ← htail]
  simp [ncard_eq_sum_indicator]

end ProbabilityTheory
