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
Converse of Poisson's theorem for urns. Consider a sequence of urns, each
containing white balls (recorded as `1`) and black balls (recorded as `0`),
whose compositions are unknown and are described by probabilities `prob n`.
For each urn in turn, draw one ball and record the outcome `X n`. Then,
with probability `1`, if the average of the outcomes `(1 / n) ∑ i < n, X i`
converges to a number `L`, then the average of the unknown probabilities
`(1 / n) ∑ i < n, prob i` also converges to `L`. The draws are pairwise
independent `{0, 1}`-valued variables with `μ {X n = 1} = prob n`; for
uniformly bounded variables pairwise independence suffices for the strong
law used here, via the variance bound `∑ Var / n ^ 2 < ∞`. Source:
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
