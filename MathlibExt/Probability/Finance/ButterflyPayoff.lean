/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Butterfly payoff and its price

A long butterfly payoff (long one call at `K1`, short two at `K2`, long one
at `K3`, with `K2` the midpoint of `K1` and `K3`) is nonnegative, hence has
nonnegative price under positive state pricing.

## Main results

* `butterflyPayoff_nonneg`: payoff nonnegativity under the midpoint
  hypothesis.
* `butterflyPrice_nonneg`: price nonnegativity under positive state prices.
* `butterflyPayoff_example`: a concrete instance.
-/

@[expose] public section

namespace MathlibExt.Probability.Finance.ButterflyPayoff

/-- Long butterfly payoff at expiry with strikes `K1 < K2 < K3`: long one call
at `K1`, short two calls at `K2`, long one call at `K3`. -/
noncomputable def butterflyPayoff (S K1 K2 K3 : ℝ) : ℝ :=
  max (S - K1) 0 - 2 * max (S - K2) 0 + max (S - K3) 0

/-- A butterfly payoff is nonnegative when the middle strike is the midpoint of
the outer strikes (`K1 + K3 = 2 * K2`) and `K1 ≤ K2 ≤ K3`. The midpoint
hypothesis is sharp: with `K1 = 0, K2 = 1, K3 = 100` the payoff at `S = 100`
is `-98`. -/
theorem butterflyPayoff_nonneg {K1 K2 K3 S : ℝ} (h12 : K1 ≤ K2) (h23 : K2 ≤ K3)
    (hmid : K1 + K3 = 2 * K2) : 0 ≤ butterflyPayoff S K1 K2 K3 := by
  unfold butterflyPayoff
  by_cases h2 : S ≤ K2
  · by_cases h1 : S ≤ K1
    · have e1 : max (S - K1) 0 = 0 := max_eq_right (by linarith)
      have e2 : max (S - K2) 0 = 0 := max_eq_right (by linarith)
      have e3 : max (S - K3) 0 = 0 := max_eq_right (by linarith)
      rw [e1, e2, e3]
      linarith
    · have e1 : max (S - K1) 0 = S - K1 := max_eq_left (by linarith)
      have e2 : max (S - K2) 0 = 0 := max_eq_right (by linarith)
      have e3 : max (S - K3) 0 = 0 := max_eq_right (by linarith)
      rw [e1, e2, e3]
      linarith
  · by_cases h3 : S ≤ K3
    · have e1 : max (S - K1) 0 = S - K1 := max_eq_left (by linarith)
      have e2 : max (S - K2) 0 = S - K2 := max_eq_left (by linarith)
      have e3 : max (S - K3) 0 = 0 := max_eq_right (by linarith)
      rw [e1, e2, e3]
      linarith
    · have e1 : max (S - K1) 0 = S - K1 := max_eq_left (by linarith)
      have e2 : max (S - K2) 0 = S - K2 := max_eq_left (by linarith)
      have e3 : max (S - K3) 0 = S - K3 := max_eq_left (by linarith)
      rw [e1, e2, e3]
      linarith

/-- A nonnegative butterfly payoff has nonnegative price under positive state
pricing: with strictly positive state prices `psi`, the state-price-weighted
sum of butterfly payoffs is nonnegative. This is `Finset.sum_nonneg` plus
`mul_nonneg` applied to `butterflyPayoff_nonneg`; do not reprove either. -/
theorem butterflyPrice_nonneg {Ω : Type*} [Fintype Ω] {psi : Ω → ℝ} {S : Ω → ℝ}
    {K1 K2 K3 : ℝ} (hpsi : ∀ ω, 0 < psi ω) (h12 : K1 ≤ K2) (h23 : K2 ≤ K3)
    (hmid : K1 + K3 = 2 * K2) :
    0 ≤ ∑ ω, psi ω * butterflyPayoff (S ω) K1 K2 K3 := by
  apply Finset.sum_nonneg
  intro ω _
  exact mul_nonneg (hpsi ω).le (butterflyPayoff_nonneg h12 h23 hmid)

/-- Concrete instance: strikes `90, 100, 110`, terminal price `105`:
payoff `15 - 2 * 5 + 0 = 5 ≥ 0`. -/
theorem butterflyPayoff_example : 0 ≤ butterflyPayoff 105 90 100 110 := by
  exact butterflyPayoff_nonneg (by norm_num) (by norm_num) (by norm_num)


end MathlibExt.Probability.Finance.ButterflyPayoff
