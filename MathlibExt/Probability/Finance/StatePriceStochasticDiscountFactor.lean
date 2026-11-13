/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import MathlibExt.Probability.FiniteProbability
import Mathlib.Tactic.Ring

/-!
# State prices and the stochastic discount factor

On a finite state space, a positive state-price vector `ψ` and positive physical weights `P`
induce the stochastic discount factor `m ω = ψ ω / P ω`, and the state-price value of a payoff
equals its `P`-weighted expectation under `m`:
`∑ ω, ψ ω * X ω = ∑ ω, P ω * (m ω * X ω)`. Both sides are
`MathlibExt.Probability.FiniteProbability.expectation`, with the state prices `ψ` and the physical
weights `P` as the respective weights. The identity does not need `∑ ω, P ω = 1`; when `P` is
normalized, the right-hand side is the physical expectation `E_P[m * X]`.

This is the state-price-to-SDF direction. It is distinct from the marginal-utility SDF
pricing equation in `MathlibExt.Probability.Finance.ConsumptionSDF`, which derives an SDF
from an investor's first-order condition; here the state prices are taken as given.

## Main results

* `stochasticDiscountFactor_pos`: the induced SDF is positive.
* `price_eq_expectation_stochasticDiscountFactor`: the state-price value `expectation ψ X`
  equals the `P`-weighted expectation `expectation P (m * X)`.

## References

* J. H. Cochrane, *Asset Pricing*, revised edition, Princeton University Press (2005),
  Section 1.2.
-/

@[expose] public section

namespace MathlibExt.Probability.Finance.StatePriceStochasticDiscountFactor

open MathlibExt.Probability.FiniteProbability

/-- The stochastic discount factor induced by the state-price vector `ψ` and the physical
weights `P`: `m ω = ψ ω / P ω`. Requires `P ω ≠ 0` to be meaningful; the theorems below
assume `0 < P ω`. -/
noncomputable def stochasticDiscountFactor {Ω : Type*} (ψ P : Ω → ℝ) (ω : Ω) : ℝ :=
  ψ ω / P ω

/-- A positive state-price vector and positive physical weights induce a positive stochastic
discount factor. -/
theorem stochasticDiscountFactor_pos {Ω : Type*} {ψ P : Ω → ℝ}
    (hψ : ∀ ω, 0 < ψ ω) (hP : ∀ ω, 0 < P ω) (ω : Ω) :
    0 < stochasticDiscountFactor ψ P ω := by
  unfold stochasticDiscountFactor
  exact div_pos (hψ ω) (hP ω)

/-- **State-price value equals SDF pricing.** With positive physical weights `P`, the
state-price value `expectation ψ X = ∑ ω, ψ ω * X ω` of a payoff `X` equals its `P`-weighted
expectation under the induced stochastic discount factor, `∑ ω, P ω * (m ω * X ω)`. When
`∑ ω, P ω = 1` the right-hand side is the physical expectation `E_P[m * X]`; the identity does
not use the normalization. -/
theorem price_eq_expectation_stochasticDiscountFactor {Ω : Type*} [Fintype Ω]
    {ψ P X : Ω → ℝ} (hP : ∀ ω, 0 < P ω) :
    expectation ψ X = expectation P (fun ω => stochasticDiscountFactor ψ P ω * X ω) := by
  unfold expectation stochasticDiscountFactor
  apply Finset.sum_congr rfl
  intro ω _
  have hPω : P ω ≠ 0 := ne_of_gt (hP ω)
  calc ψ ω * X ω
      = P ω * (ψ ω / P ω) * X ω := by rw [mul_div_cancel₀ _ hPω]
    _ = P ω * (ψ ω / P ω * X ω) := by ring

end MathlibExt.Probability.Finance.StatePriceStochasticDiscountFactor
