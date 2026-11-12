/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.BinomialTail
public import MathlibExt.Probability.Statistics.MultipleTesting.Basic
public import MathlibExt.Probability.Statistics.ExactTests.TailPValue
public import Mathlib.Probability.Distributions.Binomial

/-!
# The exact binomial test of a composite one-sided null

For `X ~ Bin(n, p)` and the one-sided null `p ≤ p₀`, the exact upper-tail p-value computed
under the boundary null `Bin(n, p₀)` is valid at every `p` in the null. The point-null case
`p = p₀` is `isValidPValue_upperTailPValue`; the composite case follows because the binomial
upper tail is nondecreasing in `p` (`monotoneOn_binomTail`).

The formal proof uses exactly two ingredients: the p-value is computed at the boundary `p₀`, and
the binomial upper tail is nondecreasing in the success probability. For a level `s`, the
rejection event `{π(X) ≤ s}` is `{X ≥ k₀}` for the least cutoff `k₀` whose tail under
`Bin(n, p₀)` is at most `s`, and for `p ≤ p₀`, `P_p(X ≥ k₀) ≤ P_{p₀}(X ≥ k₀) ≤ s`. The
monotonicity ingredient is `monotoneOn_binomTail`.

## Main results

* `upperTail_binomial`: the upper tail of Mathlib's `binomial` measure is `binomTail`.
* `isValidPValue_upperTailPValue_binomial_of_le`

## References

* E. L. Lehmann and J. P. Romano, *Testing Statistical Hypotheses*, 3rd ed., Springer (2005),
  Lemma 3.3.1.
* W. Feller, *An Introduction to Probability Theory and Its Applications*, vol. I, 3rd ed.,
  Wiley, 1968 (binomial tails).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory MathlibExt.Probability.Statistics.MultipleTesting

namespace MathlibExt.Probability.Statistics.ExactTests

/-- The upper tail `P(X ≥ x)` of Mathlib's `Bin(n, p)` is `binomTail n x p`. -/
theorem upperTail_binomial (n x : ℕ) (p : unitInterval) :
    upperTail (binomial n p) x = binomTail n x p := by
  have hae : ∀ᵐ j ∂(binomial n p), j ≤ n := ae_le_of_hasLaw_binomial HasLaw.id
  have hset : {j : ℕ | x ≤ j} =ᵐ[binomial n p] (↑(Finset.Icc x n) : Set ℕ) := by
    filter_upwards [hae] with j hj
    simp [hj]
  rw [upperTail, measureReal_congr hset, ← sum_measureReal_singleton]
  exact Finset.sum_congr rfl fun j _ => binomial_real_singleton n j p

/-- **Exact binomial test of the composite one-sided null `p ≤ p₀`.** If `X ~ Bin(n, p)` with
`p ≤ p₀`, the exact upper-tail p-value computed under the boundary null `Bin(n, p₀)` is valid:
`μ {upperTail Bin(n, p₀) X ≤ s} ≤ s` for every `s ∈ [0, 1]`.

The proof combines the boundary p-value with `monotoneOn_binomTail`, the monotonicity of the
binomial upper tail in the success probability.

Source: Lehmann–Romano (2005), Lemma 3.3.1; Feller (1968) (binomial tails). -/
theorem isValidPValue_upperTailPValue_binomial_of_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {n : ℕ} {p p₀ : unitInterval} (hp : (p : ℝ) ≤ p₀) {X : Ω → ℕ}
    (hX : HasLaw X (binomial n p) μ) :
    IsValidPValue μ (upperTailPValue (binomial n p₀) X) := by
  intro s _
  by_cases hS : ∃ k, upperTail (binomial n p₀) k ≤ s
  · classical
    have hset : {ω | upperTailPValue (binomial n p₀) X ω ≤ s} = {ω | Nat.find hS ≤ X ω} := by
      ext ω
      simp only [upperTailPValue, Set.mem_ofPred_eq]
      exact ⟨fun h => Nat.find_min' hS h,
        fun h => (upperTail_antitone _ h).trans (Nat.find_spec hS)⟩
    rw [hset, hX.measure_eq (p := (Nat.find hS ≤ ·)) (measurableSet_Ici (a := Nat.find hS)),
      ← ofReal_measureReal]
    have hmono : upperTail (binomial n p) (Nat.find hS) ≤
        upperTail (binomial n p₀) (Nat.find hS) := by
      rw [upperTail_binomial, upperTail_binomial]
      exact monotoneOn_binomTail n _ p.2 p₀.2 hp
    exact ENNReal.ofReal_le_ofReal (hmono.trans (Nat.find_spec hS))
  · have hset : {ω | upperTailPValue (binomial n p₀) X ω ≤ s} = ∅ :=
      Set.eq_empty_of_forall_notMem fun ω h => hS ⟨X ω, h⟩
    simp [hset]

end MathlibExt.Probability.Statistics.ExactTests
