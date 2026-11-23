/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

namespace MathlibExt.Probability.ScottishBook17Wanted

/--
**Converse of Poisson's theorem for urns.** Let $(\Omega, \mu)$ be a probability space, let
$(p_n)_{n \ge 0}$ be real numbers in $[0, 1]$, and let $(X_n)_{n \ge 0}$ be pairwise independent
measurable real random variables on $\Omega$ such that each $X_n$ almost surely takes only the
values $0$ and $1$, and $\mu(X_n = 1) = p_n$. Then for every real number $L$ and almost every
$\omega \in \Omega$: if $\frac{1}{n} \sum_{i=0}^{n-1} X_i(\omega) \to L$ as $n \to \infty$, then
$\frac{1}{n} \sum_{i=0}^{n-1} p_i \to L$ as $n \to \infty$.

Here $X_n$ records one draw from the $n$-th of a sequence of urns of unknown composition, a white
ball as $1$ and a black ball as $0$, and $p_n$ is the probability of drawing a white ball from the
$n$-th urn. Only pairwise independence is assumed: for uncorrelated variables with uniformly
bounded variances the strong law of large numbers still holds.

Source:
S. Ulam, Problem 17 of the Scottish Book. The proof is Kolmogorov's strong
law of large numbers for independent bounded variables (1933).
-/
theorem_wanted urnConversePoisson :
    ∀ (Ω : Type) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
      [MeasureTheory.IsProbabilityMeasure μ] (prob : ℕ → ℝ) (X : ℕ → Ω → ℝ) (L : ℝ),
      (∀ n, 0 ≤ prob n ∧ prob n ≤ 1) →
      (∀ n, Measurable (X n)) →
      (∀ n, ∀ᵐ ω ∂μ, X n ω = 0 ∨ X n ω = 1) →
      (∀ n, μ {ω | X n ω = 1} = ENNReal.ofReal (prob n)) →
      (∀ i j, i ≠ j → ProbabilityTheory.IndepFun (X i) (X j) μ) →
      ∀ᵐ ω ∂μ, Filter.Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, X i ω) / (n : ℝ))
          Filter.atTop (nhds L) →
        Filter.Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, prob i) / (n : ℝ))
          Filter.atTop (nhds L)

end MathlibExt.Probability.ScottishBook17Wanted
