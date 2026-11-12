/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.ExactTests.BinomialTest

@[expose] public section

open MeasureTheory ProbabilityTheory MathlibExt.Probability.Statistics.MultipleTesting
open MathlibExt.Probability.Statistics.ExactTests

namespace MathlibExtTest.Probability.Statistics.ExactTests.BinomialTest

/-- `p = p₀` recovers the point-null theorem. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n : ℕ} {p : unitInterval}
    {X : Ω → ℕ} (hX : HasLaw X (binomial n p) μ) :
    IsValidPValue μ (upperTailPValue (binomial n p) X) :=
  isValidPValue_upperTailPValue_binomial_of_le le_rfl hX

/-- Tied/zero observation: the p-value of `X = 0` is `1` under every boundary null. -/
example (n : ℕ) (p₀ : unitInterval) : upperTail (binomial n p₀) 0 = 1 := by
  rw [upperTail_binomial, binomTail_zero]

/-- `n = 0`: the only possible count is `0`, whose p-value is `1`; the test never rejects at a
level `s < 1`. -/
example (p₀ : unitInterval) : upperTail (binomial 0 p₀) 0 = 1 ∧
    ∀ k, 1 ≤ k → upperTail (binomial 0 p₀) k = 0 := by
  refine ⟨by rw [upperTail_binomial, binomTail_zero], fun k hk => ?_⟩
  rw [upperTail_binomial, binomTail, Finset.Icc_eq_empty_of_lt (by omega), Finset.sum_empty]

/-- All-successes endpoint: at the boundary `p₀ = 1` the count `n` is an atom of mass `1`, so its
p-value is `1`. -/
example (n : ℕ) : upperTail (binomial n 1) n = 1 := by
  rw [upperTail_binomial, binomTail]
  simp

/-- Negative check: the hypothesis `p ≤ p₀` cannot be dropped. With `n = 1`, true `p = 1` and
boundary `p₀ = 0`, the observation `X = 1` has p-value `0` almost surely, so the test rejects
with probability `1 > 0` at level `s = 0`. -/
example : ¬ IsValidPValue (binomial 1 1) (upperTailPValue (binomial 1 0) id) := by
  intro h
  have hset : ({1} : Set ℕ) ⊆ {ω | upperTailPValue (binomial 1 0) id ω ≤ 0} := by
    rintro _ rfl
    show upperTail (binomial 1 0) 1 ≤ 0
    rw [upperTail_binomial, binomTail]
    simp
  have h1 := (measure_mono hset).trans (h 0 ⟨le_rfl, zero_le_one⟩)
  rw [binomial_singleton] at h1
  simp at h1

end MathlibExtTest.Probability.Statistics.ExactTests.BinomialTest
