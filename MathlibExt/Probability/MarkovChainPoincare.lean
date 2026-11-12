/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.FiniteProbability

import Mathlib.Tactic.Ring

@[expose] public section

/-! # Iterating a variance contraction

A nonnegative one-step bound on finite-probability variance iterates
geometrically. For a Markov kernel use `Matrix.mulVec K` as the
transformation and `(1 - gap)^2` as the factor. Stochasticity,
stationarity, and a spectral gap are inputs to proving that one-step
bound, not additional hypotheses of the iteration lemma.

The theorem uses `FiniteProbability.variance` and `Function.iterate`
directly, without introducing alternative names for these operations.

Source: David A. Levin, Yuval Peres, and Elizabeth L. Wilmer,
Markov Chains and Mixing Times, second edition (2017), Chapter 12.
-/

namespace MathlibExt.Probability.MarkovChainPoincare

/-- A nonnegative one-step variance bound iterates geometrically.
No stochasticity, stationarity, or gap assumptions are needed for this
algebraic implication; they belong in proofs of the one-step bound. -/
theorem variance_iterate_le {α : Type*} [Fintype α] {π : α → ℝ}
    {T : (α → ℝ) → α → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hcontract : ∀ f : α → ℝ,
      FiniteProbability.variance π (T f) ≤ c * FiniteProbability.variance π f)
    (f : α → ℝ) (t : ℕ) :
    FiniteProbability.variance π (T^[t] f) ≤
      c ^ t * FiniteProbability.variance π f := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    calc FiniteProbability.variance π (T (T^[t] f))
        ≤ c * FiniteProbability.variance π (T^[t] f) := hcontract _
      _ ≤ c * (c ^ t * FiniteProbability.variance π f) :=
        mul_le_mul_of_nonneg_left ih hc
      _ = c ^ (t + 1) * FiniteProbability.variance π f := by
        rw [pow_succ]
        ring

end MathlibExt.Probability.MarkovChainPoincare
